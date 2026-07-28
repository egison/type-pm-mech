import TypePM.Exec

/-!
# 実行可能意味論の適切性 (Exec → 関係的意味論) — 証明済み

`Examples.lean` の機械検証(`rfl`)の結果を関係的意味論の導出に持ち上げる
健全性定理群。fuel に関する相互構造帰納で証明する
(論文 Thm 5.6 の「結合導出木の高さに関する帰納法」の実行器版)。

これにより Examples の 4 実行例は、関係的意味論 `Eval` の導出の存在まで
機械的に保証される(`Examples.lean` 末尾の系を参照)。
-/

namespace TypePM

/-! ## Option の分解補題 -/

theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β}
    (h : x >>= f = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => exact nomatch h
  | some a => exact ⟨a, rfl, h⟩

theorem pure_eq_some {α} {a b : α} (h : (pure a : Option α) = some b) : a = b :=
  Option.some.inj h

/-- find? が返す対のキーは探したキーに一致する -/
theorem find?_fst {α} {l : List (String × α)} {k : String} {pr : String × α}
    (h : List.find? (fun q => q.1 == k) l = some pr) : pr.1 = k := by
  have := List.find?_some h
  simpa [beq_iff_eq] using this

/-! ## ppShapeOKList の長さ補題 -/

theorem ppShapeOKList_length : ∀ {pps : List PPat} {ps : List Pattern},
    ppShapeOKList pps ps = true → pps.length = ps.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: pps, _ :: ps, h => by
      simp only [ppShapeOKList, Bool.and_eq_true] at h
      simp [ppShapeOKList_length (pps := pps) (ps := ps) h.2]

theorem ppShapeOKList_false_of_length_ne {pps : List PPat} {ps : List Pattern}
    (h : pps.length ≠ ps.length) : ppShapeOKList pps ps = false := by
  cases hOK : ppShapeOKList pps ps
  · rfl
  · exact absurd (ppShapeOKList_length hOK) h

/-! ## piHit の反転補題 -/

theorem piHit_some {piE : PiEnv} {t : Tree} {y : String} {q : Pattern} {m v : Value}
    (h : piHit piE t = some (y, q, m, v)) :
    t = .atom ⟨.embed y, m, v⟩ ∧
    List.find? (fun pr => pr.1 == y) piE = some (y, q) := by
  cases t with
  | atom a =>
      obtain ⟨p, m', v'⟩ := a
      simp only [piHit] at h
      split at h
      · next y' =>
        split at h
        · next fst q' hf =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ :
              y' = y ∧ q' = q ∧ m' = m ∧ v' = v := by
            have := Option.some.inj h
            simp_all
          have hk := find?_fst hf
          subst hk
          exact ⟨rfl, hf⟩
        · exact nomatch h
      · exact nomatch h
  | mnode S ρf θf piE' => simp [piHit] at h

theorem piHit_none {piE : PiEnv} {t : Tree}
    (h : piHit piE t = none) :
    ∀ y m v, t = .atom ⟨.embed y, m, v⟩ →
      List.find? (fun pr => pr.1 == y) piE = none := by
  intro y m v ht
  subst ht
  simp only [piHit] at h
  split at h
  · exact nomatch h
  · next hf => exact hf

/-- pappHit の反転:ヒットすれば p はパターン関数適用で、Σ_F 検索とアリティが立つ -/
theorem pappHit_some {SF : SigF} {p : Pattern} {f : String} {qs : List Pattern}
    {sig : PatFunSig} (h : pappHit SF p = some (f, qs, sig)) :
    p = .papp f qs ∧
    List.find? (fun pr => pr.1 == f) SF = some (f, sig) ∧
    sig.params.length = qs.length := by
  cases p <;> simp only [pappHit] at h <;> try cases h
  next f' qs' =>
    split at h
    · next fst sig' hf =>
      split at h
      · next hlen =>
        obtain ⟨rfl, rfl, rfl⟩ : f' = f ∧ qs' = qs ∧ sig' = sig := by
          have := Option.some.inj h
          simp_all
        have hk := find?_fst hf
        subst hk
        exact ⟨rfl, hf, by simpa [beq_iff_eq] using hlen⟩
      · exact nomatch h
    · exact nomatch h

/-! ## 適切性(健全性)本体 -/

mutual

theorem evalF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {e : Expr} {v : Value},
    evalF SF n ρ e = some v → Eval SF ρ e v
  | n+1, SF, ρ, e, v, h => by
    unfold evalF at h
    split at h
    -- var
    · exact Eval.var h
    -- lam
    · exact (Option.some.inj h) ▸ Eval.lam
    -- fix
    · exact (Option.some.inj h) ▸ Eval.fix
    -- app
    · obtain ⟨v₁, h₁, h⟩ := bind_eq_some h
      obtain ⟨v₂, h₂, h⟩ := bind_eq_some h
      cases v₁
      case closure self ρ' x eb =>
        exact Eval.app (evalF_sound' n h₁) (evalF_sound' n h₂) (evalF_sound' n h)
      all_goals exact nomatch h
    -- lit
    · exact (Option.some.inj h) ▸ Eval.lit
    -- tuple
    · obtain ⟨vs, h₁, h⟩ := bind_eq_some h
      obtain ⟨hlen, hall⟩ := evalListF_sound' n h₁
      exact (pure_eq_some h) ▸ Eval.tuple hlen hall
    -- ctor
    · obtain ⟨vs, h₁, h⟩ := bind_eq_some h
      obtain ⟨hlen, hall⟩ := evalListF_sound' n h₁
      exact (pure_eq_some h) ▸ Eval.ctor hlen hall
    -- prim
    · obtain ⟨vs, h₁, h⟩ := bind_eq_some h
      obtain ⟨hlen, hall⟩ := evalListF_sound' n h₁
      exact Eval.prim hlen hall h
    -- letE
    · obtain ⟨v₁, h₁, h⟩ := bind_eq_some h
      exact Eval.letE (evalF_sound' n h₁) (evalF_sound' n h)
    -- something
    · exact (Option.some.inj h) ▸ Eval.something
    -- matcher
    · exact (Option.some.inj h) ▸ Eval.matcher
    -- matchAll
    · obtain ⟨v_t, h₁, h⟩ := bind_eq_some h
      obtain ⟨v_m, h₂, h⟩ := bind_eq_some h
      obtain ⟨θs, h₃, h⟩ := bind_eq_some h
      obtain ⟨vs, h₄, h⟩ := bind_eq_some h
      obtain ⟨hlen, hall⟩ := evalBodiesF_sound' n h₄
      exact (pure_eq_some h) ▸
        Eval.matchAll (evalF_sound' n h₁) (evalF_sound' n h₂)
          (searchF_sound' n h₃) hlen hall

theorem evalListF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {es : List Expr}
    {vs : List Value},
    evalListF SF n ρ es = some vs →
    es.length = vs.length ∧ ∀ pr ∈ es.zip vs, Eval SF ρ pr.1 pr.2
  | n+1, SF, ρ, es, vs, h => by
    unfold evalListF at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, by intro pr hpr; cases hpr⟩
    · next e es' =>
      obtain ⟨v, h₁, h⟩ := bind_eq_some h
      obtain ⟨vs', h₂, h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      obtain ⟨hlen, hall⟩ := evalListF_sound' n h₂
      refine ⟨by simp [hlen], ?_⟩
      intro pr hpr
      simp only [List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact evalF_sound' n h₁
      · exact hall pr hpr

theorem evalBodiesF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {body : Expr}
    {θs : List Subst} {vs : List Value},
    evalBodiesF SF n ρ body θs = some vs →
    θs.length = vs.length ∧ ∀ pr ∈ θs.zip vs, Eval SF (pr.1 ++ ρ) body pr.2
  | n+1, SF, ρ, body, θs, vs, h => by
    unfold evalBodiesF at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, by intro pr hpr; cases hpr⟩
    · next θ θs' =>
      obtain ⟨v, h₁, h⟩ := bind_eq_some h
      obtain ⟨vs', h₂, h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      obtain ⟨hlen, hall⟩ := evalBodiesF_sound' n h₂
      refine ⟨by simp [hlen], ?_⟩
      intro pr hpr
      simp only [List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact evalF_sound' n h₁
      · exact hall pr hpr

theorem ppmF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {pp : PPat} {p : Pattern}
    {res : Option (List Pattern × Env)},
    ppmF SF n ρ pp p = some res → PPM SF ρ pp p res
  | n+1, SF, ρ, pp, p, res, h => by
    unfold ppmF at h
    split at h
    -- hole
    · exact (Option.some.inj h) ▸ PPM.hole
    -- wild-wild
    · exact (Option.some.inj h) ▸ PPM.wild
    -- pval-pval
    · obtain ⟨v, h₁, h⟩ := bind_eq_some h
      exact (pure_eq_some h) ▸ PPM.pval (evalF_sound' n h₁)
    -- ctor-pctor
    · next c pps c' ps =>
      split at h
      · next hguard =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hguard
        obtain ⟨rfl, hlen⟩ := hguard
        rcases ppmListF_sound' n h with ⟨rs, rfl, hrslen, hall⟩ | ⟨rfl, hfalse⟩
        · exact PPM.ctor hlen hrslen hall
        · exact PPM.fail (by simp [ppShapeOK, hfalse])
      · next hguard =>
        obtain rfl := Option.some.inj h
        cases hc : c == c' with
        | false => exact PPM.fail (by simp [ppShapeOK, hc])
        | true =>
          cases hl : pps.length == ps.length with
          | false =>
            refine PPM.fail ?_
            have hne : pps.length ≠ ps.length := by
              intro he; rw [he] at hl; simp at hl
            simp [ppShapeOK, ppShapeOKList_false_of_length_ne hne]
          | true => exact absurd (by simp [hc, hl]) hguard
    -- tuple-ptuple
    · next pps ps =>
      split at h
      · next hlen =>
        simp only [beq_iff_eq] at hlen
        rcases ppmListF_sound' n h with ⟨rs, rfl, hrslen, hall⟩ | ⟨rfl, hfalse⟩
        · exact PPM.tuple hlen hrslen hall
        · exact PPM.fail (by simp [ppShapeOK, hfalse])
      · next hlen =>
        obtain rfl := Option.some.inj h
        refine PPM.fail ?_
        have : pps.length ≠ ps.length := by
          intro he; rw [he] at hlen; simp at hlen
        simp [ppShapeOK, ppShapeOKList_false_of_length_ne this]
    -- fail (catch-all:形状ガード付き)
    · split at h
      · exact nomatch h
      · next hOK =>
        obtain rfl := Option.some.inj h
        cases hOK' : ppShapeOK pp p with
        | false => exact PPM.fail hOK'
        | true => exact absurd hOK' hOK

theorem ppmListF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {pps : List PPat}
    {ps : List Pattern} {res : Option (List Pattern × Env)},
    ppmListF SF n ρ pps ps = some res →
    (∃ rs : List (List Pattern × Env),
       res = some ((rs.map (·.1)).flatten, (rs.map (·.2)).flatten) ∧
       (pps.zip ps).length = rs.length ∧
       (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)))
    ∨ (res = none ∧ ppShapeOKList pps ps = false)
  | n+1, SF, ρ, pps, ps, res, h => by
    unfold ppmListF at h
    split at h
    -- nil-nil
    · obtain rfl := Option.some.inj h
      exact .inl ⟨[], rfl, rfl, by intro tr htr; cases htr⟩
    -- cons-cons
    · next pp pps' p ps' =>
      obtain ⟨r, h₁, h⟩ := bind_eq_some h
      have hchild := ppmF_sound' n h₁
      cases r with
      | none =>
        obtain rfl := pure_eq_some h
        cases hchild with
        | fail hsh => exact .inr ⟨rfl, by simp [ppShapeOKList, hsh]⟩
      | some pr =>
        obtain ⟨nexts, ρp⟩ := pr
        obtain ⟨r', h₂, h⟩ := bind_eq_some h
        rcases ppmListF_sound' n h₂ with ⟨rs', hr', hrslen, hall⟩ | ⟨hr', hfalse⟩
        · subst hr'
          obtain rfl := pure_eq_some h
          refine .inl ⟨(nexts, ρp) :: rs', ?_, ?_, ?_⟩
          · simp
          · simp [List.zip_cons_cons, hrslen]
          · intro tr htr
            simp only [List.zip_cons_cons, List.mem_cons] at htr
            rcases htr with rfl | htr
            · exact hchild
            · exact hall tr htr
        · subst hr'
          obtain rfl := pure_eq_some h
          exact .inr ⟨rfl, by simp [ppShapeOKList, hfalse]⟩
    -- mismatch
    · next hne =>
      obtain rfl := Option.some.inj h
      refine .inr ⟨rfl, ?_⟩
      cases pps <;> cases ps <;> simp_all [ppShapeOKList]

theorem matomF_sound' : ∀ (n : Nat) {SF : SigF} {ρ : Env} {p : Pattern} {m v : Value}
    {res : List (List Atom) × Subst},
    matomF SF n ρ p m v = some res → MAtom SF ρ p m v res.1 res.2
  | n+1, SF, ρ, p, m, v, res, h => by
    unfold matomF at h
    split at h
    -- pand
    · obtain rfl := Option.some.inj h; exact MAtom.and
    -- por
    · obtain rfl := Option.some.inj h; exact MAtom.or
    -- wild-something
    · obtain rfl := Option.some.inj h; exact MAtom.someWC
    -- pvar-something
    · obtain rfl := Option.some.inj h; exact MAtom.someVar
    -- pval-something
    · obtain ⟨ve, h₁, h⟩ := bind_eq_some h
      split at h
      · next heq =>
        obtain rfl := pure_eq_some h
        exact MAtom.someValEq (evalF_sound' n h₁) heq
      · next heq =>
        obtain rfl := pure_eq_some h
        exact MAtom.someValNeq (evalF_sound' n h₁) (by simpa using heq)
    -- ptuple-tuple
    · next ps ms =>
      split at h
      · next vs =>
        split at h
        · next hlen =>
          obtain rfl := Option.some.inj h
          simp only [Bool.and_eq_true, beq_iff_eq] at hlen
          exact MAtom.tuple hlen.1 hlen.2
        · exact nomatch h
      · exact nomatch h
    -- primForm-tuple
    · split at h
      · next hprim =>
        obtain rfl := Option.some.inj h
        exact MAtom.prodSome hprim
      · exact nomatch h
    -- matcherV
    · exact clausesF_sound' n h
    -- default
    · exact nomatch h

theorem clausesF_sound' : ∀ (n : Nat) {SF : SigF} {ρ ρm : Env} {cls : List Clause}
    {p : Pattern} {v : Value} {res : List (List Atom) × Subst},
    clausesF SF n ρ ρm cls p v = some res →
    MAtom SF ρ p (.matcherV ρm cls) v res.1 res.2
  | n+1, SF, ρ, ρm, cls, p, v, res, h => by
    unfold clausesF at h
    split at h
    · exact nomatch h
    · next pp M arms cls' =>
      obtain ⟨r, h₁, h⟩ := bind_eq_some h
      have hppm := ppmF_sound' n h₁
      cases r with
      | none => exact MAtom.matcherPPFail hppm (clausesF_sound' n h)
      | some pr =>
        obtain ⟨ps', ρp⟩ := pr
        exact armsF_sound' n h hppm

theorem armsF_sound' : ∀ (n : Nat) {SF : SigF} {ρ ρm ρp : Env}
    {arms : List (DPat × Expr)} {ps' : List Pattern} {M : Expr} {v : Value}
    {res : List (List Atom) × Subst} {pp : PPat} {p : Pattern} {cls : List Clause},
    armsF SF n ρm ρp arms ps' M v = some res →
    PPM SF ρ pp p (some (ps', ρp)) →
    MAtom SF ρ p (.matcherV ρm ((pp, M, arms) :: cls)) v res.1 res.2
  | n+1, SF, ρ, ρm, ρp, arms, ps', M, v, res, pp, p, cls, h, hppm => by
    unfold armsF at h
    split at h
    · exact nomatch h
    · next dp N arms' =>
      split at h
      · next hpd =>
        exact MAtom.matcherDPFail hppm hpd (armsF_sound' n h hppm)
      · next ρd hpd =>
        obtain ⟨vN, h₁, h⟩ := bind_eq_some h
        obtain ⟨tuples, h₂, h⟩ := bind_eq_some h
        obtain ⟨vss, h₃, h⟩ := bind_eq_some h
        obtain ⟨vM, h₄, h⟩ := bind_eq_some h
        obtain ⟨ms, h₅, h⟩ := bind_eq_some h
        obtain rfl := pure_eq_some h
        exact MAtom.matcher hppm hpd (evalF_sound' n h₁) h₂ h₃
          (evalF_sound' n h₄) h₅

theorem stepF_sound' : ∀ (n : Nat) {SF : SigF} {s : MState} {ss : List MState},
    stepF SF n s = some ss → Step SF s ss
  | n+1, SF, ⟨[], ρ, θ⟩, ss, h => nomatch h
  | n+1, SF, ⟨.atom ⟨p, m, v⟩ :: S, ρ, θ⟩, ss, h => by
    simp only [stepF] at h
    split at h
    -- MS-PATFUN-ENTER(pappHit ヒット)
    · obtain rfl := Option.some.inj h
      obtain ⟨rfl, hf, hlen⟩ := pappHit_some (by assumption)
      exact Step.patfunEnter hf hlen
    -- MS-REDUCE(一般の原子)
    · obtain ⟨r, h₁, h⟩ := bind_eq_some h
      obtain ⟨conts, θ'⟩ := r
      obtain rfl := pure_eq_some h
      exact Step.reduce (matomF_sound' n h₁)
  | n+1, SF, ⟨.mnode [] ρf θf piE :: S, ρ, θ⟩, ss, h => by
    simp only [stepF] at h
    obtain rfl := Option.some.inj h
    exact Step.mnodeDone
  | n+1, SF, ⟨.mnode (t :: Srest) ρf θf piE :: S, ρ, θ⟩, ss, h => by
    simp only [stepF] at h
    split at h
    · obtain rfl := Option.some.inj h
      obtain ⟨rfl, hf⟩ := piHit_some (by assumption)
      exact Step.mnodeVarpat hf
    · next hmiss =>
      obtain ⟨ss', h₁, h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      exact Step.mnodeStep (piHit_none hmiss) (stepF_sound' n h₁)

theorem searchF_sound' : ∀ (n : Nat) {SF : SigF} {s : MState} {θs : List Subst},
    searchF SF n s = some θs → Search SF s θs
  | n+1, SF, s, θs, h => by
    unfold searchF at h
    split at h
    · obtain rfl := Option.some.inj h
      exact Search.done
    · obtain ⟨ss, h₁, h⟩ := bind_eq_some h
      obtain ⟨θss, h₂, h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      obtain ⟨hlen, hall⟩ := searchListF_sound' n h₂
      exact Search.step (stepF_sound' n h₁) hlen hall

theorem searchListF_sound' : ∀ (n : Nat) {SF : SigF} {ss : List MState}
    {θss : List (List Subst)},
    searchListF SF n ss = some θss →
    ss.length = θss.length ∧ ∀ pr ∈ ss.zip θss, Search SF pr.1 pr.2
  | n+1, SF, ss, θss, h => by
    unfold searchListF at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, by intro pr hpr; cases hpr⟩
    · next s ss' =>
      obtain ⟨θs, h₁, h⟩ := bind_eq_some h
      obtain ⟨θss', h₂, h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      obtain ⟨hlen, hall⟩ := searchListF_sound' n h₂
      refine ⟨by simp [hlen], ?_⟩
      intro pr hpr
      simp only [List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact searchF_sound' n h₁
      · exact hall pr hpr

end

/-! ## 公開ステートメント(旧 sorry の置き換え) -/

/-- `evalF` の健全性:値を返せば ⇓ の導出が存在する。(**証明済み**) -/
theorem evalF_sound {SF : SigF} {n : Nat} {ρ : Env} {e : Expr} {v : Value}
    (h : evalF SF n ρ e = some v) :
    Eval SF ρ e v := evalF_sound' n h

/-- `stepF` の健全性(**証明済み**) -/
theorem stepF_sound {SF : SigF} {n : Nat} {s : MState} {ss : List MState}
    (h : stepF SF n s = some ss) :
    Step SF s ss := stepF_sound' n h

/-- `searchF` の健全性(**証明済み**) -/
theorem searchF_sound {SF : SigF} {n : Nat} {s : MState} {θs : List Subst}
    (h : searchF SF n s = some θs) :
    Search SF s θs := searchF_sound' n h

end TypePM
