import TypePM.Metatheory.Preservation
import TypePM.Metatheory.Canonical
import TypePM.Metatheory.Adequacy

/-!
# Lemma 5.5:マッチング状態の進行 (Matching State Progress) と前提補題群

整型な非終端状態は必ず簡約できる(l = 0 は正当なマッチ失敗であり、行き詰まりではない)。

本ファイルには Progress の組み立てに要る前提補題を置き、証明する:
* `ListSigOK`・`canonical_list` — リスト型の値は `listOfV` で分解できる
  (分解関数の返り値 [(τ⃗)] を MS-MATCHER の継続に直すために使う)
* `clausesTy_mem`・`armsTy_mem` — T-MATCHER の節/アーム型付けの member 取り出し
* `mapM_eq_some` — 要素ごとの成功から `mapM` の成功へ
* `decomposeME_tuple` — 次マッチャー式のタプル分解の反転
* `pdMatch_typed` — dp 束縛の型付け(Lem 5.4 の dp 版;(b) でも使う)

機械化上の注意(README 設計判断):
MS-MATCHER の premise は分解関数 N・次マッチャー式 M の評価 ⇓ を含むため、
「簡約列 s → [sᵢ] が導出可能」という主張は埋め込まれた式評価の**停止**を要する。
論文は「分解関数は停止すると仮定する」(§5)と明言しており、
ここではそれを大域的停止仮定 `htotal` として渡す。さらに分解結果の**形**
(リストである・k 組である)は型に依存するため、Thm 5.6(a) を oracle 仮定に取る
(Thm 5.7・Lem 5.4/C.2 と同じ流儀;論文も結合帰納法でこれらを同時に示す)。
-/

namespace TypePM

/-! ## リストシグネチャの整形性と正準形 -/

/-- `data [a] := [] | (::) a [a]` が Σ_D に標準形で入っており、
    List 型構成子を狙う構成子は nil/cons のみ(§2.2 の宣言の暗黙条件)。 -/
def ListSigOK (SD : SigD) : Prop :=
  List.find? (fun pr => pr.1 == "nil") SD =
    some ("nil", ⟨1, [], Ty.listT (.var 0)⟩) ∧
  List.find? (fun pr => pr.1 == "cons") SD =
    some ("cons", ⟨1, [.var 0, Ty.listT (.var 0)], Ty.listT (.var 0)⟩) ∧
  ∀ pr ∈ SD, ∀ args, pr.2.res = Ty.data "List" args →
    pr.1 = "nil" ∨ pr.1 = "cons"

/-- リスト型の値は `listOfV` で分解でき、要素は要素型で型付く(**証明済み**)。 -/
theorem canonical_list {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hL : ListSigOK SD) :
    ∀ {v : Value} {τx : Ty}, ValueTy SD SP SF v τx →
    ∀ (τ : Ty), τx = Ty.listT τ →
    ∃ l, listOfV v = some l ∧ ∀ x ∈ l, ValueTy SD SP SF x τ := by
  intro v τx hv
  induction hv with
  | lit => intro τ heq; simp [Ty.listT] at heq
  | ctor hfind hlen hall ih =>
      intro τ heq
      rename_i C sig ts vs
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at heq
      simp only [Ty.instSig, Ty.applyTS, Ty.listT] at heq
      injection heq with hn hargs
      subst hn
      -- パラメタ数は 1
      have hnp : sig.nparams = 1 := by
        have := congrArg List.length hargs
        simpa [applyTSList_length] using this
      -- inst ts (var 0) = τ
      have h0 : TySubst.appVar ((List.range ts.length).zip ts) 0 = τ := by
        rw [hnp] at hargs
        simpa [List.range_one, applyTSList, Ty.applyTS] using hargs
      -- C は nil か cons
      have hCmem := List.mem_of_find?_eq_some hfind
      have hres' : sig.res = Ty.data "List" ((List.range sig.nparams).map .var) :=
        hres
      rcases hL.2.2 _ hCmem _ hres' with hC | hC
      · -- nil
        subst hC
        have hsig : sig = ⟨1, [], Ty.listT (.var 0)⟩ :=
          congrArg (·.2) (Option.some.inj (hfind.symm.trans hL.1))
        rw [hsig] at hlen
        simp only [List.length_nil] at hlen
        cases vs with
        | cons h vs' => simp at hlen
        | nil =>
          exact ⟨[], rfl, by intro x hx; cases hx⟩
      · -- cons
        subst hC
        have hsig : sig = ⟨1, [.var 0, Ty.listT (.var 0)], Ty.listT (.var 0)⟩ :=
          congrArg (·.2) (Option.some.inj (hfind.symm.trans hL.2.1))
        have hargsmap : sig.args.map (Ty.instSig ts) = [τ, Ty.listT τ] := by
          rw [hsig]
          simp only [List.map_cons, List.map_nil, Ty.instSig, Ty.applyTS,
            applyTSList, Ty.listT, h0]
        rw [hsig] at hlen
        simp only [List.length_cons, List.length_nil] at hlen
        cases vs with
        | nil => simp at hlen
        | cons h vs' =>
          cases vs' with
          | nil => simp at hlen
          | cons t vs'' =>
            cases vs'' with
            | cons _ _ => simp at hlen
            | nil =>
              rw [hargsmap] at hall ih
              have hh : ValueTy SD SP SF h τ :=
                hall (h, τ) (by simp [List.zip_cons_cons])
              obtain ⟨l', hl', htl⟩ :=
                ih (t, Ty.listT τ) (by simp [List.zip_cons_cons]) τ rfl
              refine ⟨h :: l', by simp [listOfV, hl'], ?_⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hh
              · exact htl x hx
  | tuple _ _ _ => intro τ heq; simp [Ty.listT] at heq
  | closure Γ' _ _ _ _ => intro τ heq; simp [Ty.listT] at heq
  | matcherV _ _ _ _ => intro τ heq; simp [Ty.listT] at heq
  | something => intro τ heq; simp [Ty.listT] at heq
  | prodMatcher _ _ _ => intro τ heq; simp [Ty.listT] at heq
  | slotV _ _ _ _ _ => intro τ heq; simp [Ty.listT] at heq
  | prodSlot _ _ _ => intro τ heq; simp [Ty.listT] at heq

/-! ## 節・アーム型付けの member 取り出し -/

theorem clausesTy_mem {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {τ : Ty} :
    ∀ {cls : List Clause}, ClausesTy SD SP SF Γ τ cls →
    ∀ {cl}, cl ∈ cls → ClauseTy SD SP SF Γ τ cl
  | [], _, _, hmem => nomatch hmem
  | _ :: cls, h, cl, hmem => by
      cases h with
      | cons hh ht =>
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hh
        · exact clausesTy_mem ht hmem

theorem armsTy_mem {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {τ : Ty}
    {Δi : BindCtx} {τres : Ty} :
    ∀ {arms : List (DPat × Expr)}, ArmsTy SD SP SF Γ τ Δi τres arms →
    ∀ {arm}, arm ∈ arms →
    ∃ Γij, PDTy SD arm.1 τ Γij ∧
      HasTy SD SP SF (BindCtx.toCtx Γij ++ BindCtx.toCtx Δi ++ Γ) arm.2 τres
  | [], _, _, hmem => nomatch hmem
  | _ :: arms, h, arm, hmem => by
      cases h with
      | cons hpd hty ht =>
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨_, hpd, hty⟩
        · exact armsTy_mem ht hmem

/-! ## mapM・decomposeME の補助 -/

theorem mapM_eq_some {α β} {f : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = some b) →
    ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨l', hl'⟩ :=
        mapM_eq_some l fun x hx => h x (List.mem_cons_of_mem _ hx)
      exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-- k ≠ 1 のとき decomposeME はタプル式の分解(反転) -/
theorem decomposeME_tuple {M : Expr} {k : Nat} {Ms : List Expr}
    (hk : k ≠ 1) (h : decomposeME M k = some Ms) :
    M = .tuple Ms ∧ Ms.length = k := by
  unfold decomposeME at h
  rw [if_neg (by simpa using hk)] at h
  split at h
  · next es =>
    split at h
    · next hlen =>
      obtain rfl := Option.some.inj h
      exact ⟨rfl, by simpa using hlen⟩
    · exact nomatch h
  · exact nomatch h

/-! ## dp 束縛の型付け (Lem 5.4 の dp 版;(b) でも使用) -/

mutual

theorem pdMatch_typed {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) :
    ∀ (dp : DPat) {v : Value} {τ : Ty} {Γd : List (String × Ty)} {ρd : Env},
    PDTy SD dp τ Γd →
    ValueTy SD SP SF v τ →
    pdMatch dp v = some ρd →
    (∀ pr ∈ ρd, pr.1 ∈ Γd.map (·.1)) ∧
    ((Γd.map (·.1)).Nodup →
      ∀ pr ∈ Γd, ∃ v', Env.find? ρd pr.1 = some v' ∧ ValueTy SD SP SF v' pr.2)
  | .var z, v, τ, Γd, ρd, hpd, hv, hm => by
      cases hpd
      simp only [pdMatch] at hm
      obtain rfl := Option.some.inj hm
      refine ⟨?_, ?_⟩
      · intro pr hpr
        simp only [List.mem_singleton] at hpr
        subst hpr
        simp
      · intro _ pr hpr
        simp only [List.mem_singleton] at hpr
        subst hpr
        exact ⟨v, by simp [Env.find?, List.find?], hv⟩
  | .wild, v, τ, Γd, ρd, hpd, hv, hm => by
      cases hpd
      simp only [pdMatch] at hm
      obtain rfl := Option.some.inj hm
      refine ⟨?_, ?_⟩
      · intro pr hpr
        exact nomatch hpr
      · intro _ pr hpr
        exact nomatch hpr
  | .ctor C dps, v, τ, Γd, ρd, hpd, hv, hm => by
      cases hpd with
      | ctor hfindP hdps =>
        rename_i sig ts
        -- pdMatch の反転:v = ctor C' vs かつ C = C'
        simp only [pdMatch] at hm
        split at hm
        · next C' vs =>
          split at hm
          · next hC =>
            simp only [beq_iff_eq] at hC
            subst hC
            -- ValueTy の反転(index を一般化してから)
            generalize hτ : Ty.instSig ts sig.res = τx at hv
            cases hv with
            | ctor hfindV hlenV hallV =>
              rename_i sigV tsV
              have hsig : sig = sigV :=
                congrArg (·.2) (Option.some.inj (hfindP.symm.trans hfindV))
              subst hsig
              have hwf := hwfD _ (List.mem_of_find?_eq_some hfindP)
              have hagree := instSig_args_agree hwf hτ
              have hall' : ∀ pr ∈ vs.zip (sig.args.map (Ty.instSig ts)),
                  ValueTy SD SP SF pr.1 pr.2 := by
                intro pr hpr
                have hmapeq : sig.args.map (Ty.instSig ts) =
                    sig.args.map (Ty.instSig tsV) :=
                  List.map_congr_left fun τa hτa => hagree τa hτa
                exact hallV pr (hmapeq ▸ hpr)
              exact pdMatchList_typed hwfD dps hdps
                (by simpa using hlenV) hall' hm
            | slotV hm' hren how huni =>
              exfalso
              obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfindP)
              rw [hres] at hτ
              simp [Ty.instSig, Ty.applyTS] at hτ
          · exact nomatch hm
        · exact nomatch hm
  | .tuple dps, v, τ, Γd, ρd, hpd, hv, hm => by
      cases hpd with
      | tuple hdps =>
        obtain ⟨vs', rfl, hlen, hall⟩ := canonical_prod hwfD hv
        simp only [pdMatch] at hm
        exact pdMatchList_typed hwfD dps hdps hlen hall hm

theorem pdMatchList_typed {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) :
    ∀ (dps : List DPat) {vs : List Value} {τs : List Ty}
      {Γs : List (String × Ty)} {ρd : Env},
    PDTys SD dps τs Γs →
    vs.length = τs.length →
    (∀ pr ∈ vs.zip τs, ValueTy SD SP SF pr.1 pr.2) →
    pdMatchList dps vs = some ρd →
    (∀ pr ∈ ρd, pr.1 ∈ Γs.map (·.1)) ∧
    ((Γs.map (·.1)).Nodup →
      ∀ pr ∈ Γs, ∃ v', Env.find? ρd pr.1 = some v' ∧ ValueTy SD SP SF v' pr.2)
  | [], vs, τs, Γs, ρd, hpds, hlen, hall, hm => by
      cases hpds
      cases vs with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [pdMatchList] at hm
        obtain rfl := Option.some.inj hm
        refine ⟨?_, ?_⟩
        · intro pr hpr
          exact nomatch hpr
        · intro _ pr hpr
          exact nomatch hpr
  | dp :: dps, vs, τs, Γs, ρd, hpds, hlen, hall, hm => by
      cases hpds with
      | cons hpd hpds' =>
        rename_i τh Γh τt Γt
        cases vs with
        | nil => simp at hlen
        | cons v vs' =>
          simp only [pdMatchList] at hm
          obtain ⟨ρ₁, h₁, hm⟩ := bind_eq_some hm
          obtain ⟨ρ₂, h₂, hm⟩ := bind_eq_some hm
          obtain rfl := pure_eq_some hm
          have hvh : ValueTy SD SP SF v τh :=
            hall (v, τh) (by simp [List.zip_cons_cons])
          obtain ⟨hdom₁, hbind₁⟩ := pdMatch_typed hwfD dp hpd hvh h₁
          obtain ⟨hdom₂, hbind₂⟩ := pdMatchList_typed hwfD dps hpds'
            (by simpa using hlen)
            (fun pr hpr => hall pr (by simp [List.zip_cons_cons]; exact .inr hpr))
            h₂
          refine ⟨?_, ?_⟩
          · intro pr hpr
            simp only [List.map_append, List.mem_append]
            rcases List.mem_append.mp hpr with hpr | hpr
            · exact .inl (hdom₁ pr hpr)
            · exact .inr (hdom₂ pr hpr)
          · intro hnd pr hpr
            rw [List.map_append] at hnd
            obtain ⟨ndh, ndt, hdisj⟩ := nodup_append_split hnd
            rcases List.mem_append.mp hpr with hpr | hpr
            · obtain ⟨v', hfind, hty⟩ := hbind₁ ndh pr hpr
              exact ⟨v', Env.find?_append_left hfind, hty⟩
            · have hnot : ∀ q ∈ ρ₁, q.1 ≠ pr.1 := by
                intro q hq heq
                exact hdisj q.1 (hdom₁ q hq) (heq ▸ List.mem_map_of_mem hpr)
              obtain ⟨v', hfind, hty⟩ := hbind₂ ndt pr hpr
              exact ⟨v', (Env.find?_append_right hnot).trans hfind, hty⟩

end

/-! ## 環境型付けの合成グルー(MS-MATCHER の分解関数評価環境の型付け) -/

theorem applyTS_nil : ∀ (τ : Ty), τ.applyTS [] = τ := by
  intro τ
  exact applyTS_congr_nil τ
where
  applyTS_congr_nil : ∀ (τ : Ty), τ.applyTS [] = τ := fun τ => by
    induction τ using Ty.rec (motive_2 := fun ts => applyTSList [] ts = ts) with
    | var a => rfl
    | int => rfl
    | bool => rfl
    | data n ts ih => simp [Ty.applyTS, ih]
    | prod ts ih => simp [Ty.applyTS, ih]
    | fn t₁ t₂ ih₁ ih₂ => simp [Ty.applyTS, ih₁, ih₂]
    | matcher t ih => simp [Ty.applyTS, ih]
    | slot t₁ t₂ ih₁ ih₂ => simp [Ty.applyTS, ih₁, ih₂]
    | nil => rfl
    | cons t ts ih ihs => simp [applyTSList, ih, ihs]

/-- 単相スキームのインスタンスは本体そのもの -/
theorem inst_mono {τ τ' : Ty} (h : (Scheme.mono τ).Inst τ') : τ' = τ := by
  obtain ⟨θ, hdom, happ⟩ := h
  have hθ : θ = [] := by
    cases θ with
    | nil => rfl
    | cons pr θ' => exact absurd (hdom pr.1 (by simp [TySubst.dom])) nofun
  rw [hθ, applyTS_nil] at happ
  exact happ.symm

/-- toCtx 上の検索は元の束縛列の検索の mono 化 -/
theorem tyCtxFind_toCtx : ∀ (Δ : BindCtx) (y : String),
    TyCtx.find? (BindCtx.toCtx Δ) y =
      (List.find? (fun pr => pr.1 == y) Δ).map (fun pr => Scheme.mono pr.2)
  | [], _ => rfl
  | pr :: Δ, y => by
      simp only [BindCtx.toCtx, List.map_cons, TyCtx.find?, List.find?]
      cases hy : (pr.1 == y)
      · exact tyCtxFind_toCtx Δ y
      · rfl

/-- 束縛列の型付け(Lem 5.4/pdMatch_typed の出力形)から EnvTyped へ -/
theorem envTyped_of_bindings {SD : SigD} {SP : SigP} {SF : SigF}
    {Δd : BindCtx} {ρd : Env}
    (hdom : ∀ pr ∈ ρd, pr.1 ∈ Δd.map (·.1))
    (hbind : ∀ pr ∈ Δd, ∃ v, Env.find? ρd pr.1 = some v ∧
      ValueTy SD SP SF v pr.2) :
    EnvTyped SD SP SF (BindCtx.toCtx Δd) ρd := by
  intro y v hfind
  -- y は Δd のドメインにある
  have hy : y ∈ Δd.map (·.1) := by
    have : ∃ pr, List.find? (fun pr => pr.1 == y) ρd = some pr := by
      simp only [Env.find?] at hfind
      cases hf : List.find? (fun pr => pr.1 == y) ρd with
      | none => rw [hf] at hfind; exact nomatch hfind
      | some pr => exact ⟨pr, rfl⟩
    obtain ⟨pr, hpr⟩ := this
    have hmem := List.mem_of_find?_eq_some hpr
    have := List.find?_some hpr
    simp only [beq_iff_eq] at this
    exact this ▸ hdom pr hmem
  -- Δd の最初の y-エントリを取る
  obtain ⟨prd, hprd⟩ : ∃ prd,
      List.find? (fun pr => pr.1 == y) Δd = some prd := by
    cases hf : List.find? (fun pr => pr.1 == y) Δd with
    | some prd => exact ⟨prd, rfl⟩
    | none =>
      exfalso
      simp only [List.mem_map] at hy
      obtain ⟨pr, hpr, hfst⟩ := hy
      have := List.find?_eq_none.mp hf pr hpr
      simp [hfst] at this
  have hkey := find?_fst hprd
  refine ⟨Scheme.mono prd.2, ?_, ?_⟩
  · rw [tyCtxFind_toCtx, hprd]
    rfl
  · intro τ' hinst
    rw [inst_mono hinst]
    obtain ⟨v', hfind', hty'⟩ :=
      hbind prd (List.mem_of_find?_eq_some hprd)
    rw [hkey] at hfind'
    rw [hfind] at hfind'
    exact (Option.some.inj hfind') ▸ hty'

/-- 束縛列の型付けはドメイン被覆も与える(EnvTyped 連結の側条件) -/
theorem bindings_cover {SD : SigD} {SP : SigP} {SF : SigF}
    {Δd : BindCtx} {ρd : Env}
    (hbind : ∀ pr ∈ Δd, ∃ v, Env.find? ρd pr.1 = some v ∧
      ValueTy SD SP SF v pr.2) :
    ∀ y, TyCtx.find? (BindCtx.toCtx Δd) y ≠ none → Env.find? ρd y ≠ none := by
  intro y hΓ
  rw [tyCtxFind_toCtx] at hΓ
  cases hf : List.find? (fun pr => pr.1 == y) Δd with
  | none => rw [hf] at hΓ; simp at hΓ
  | some prd =>
    have hkey := find?_fst hf
    obtain ⟨v', hfind', -⟩ := hbind prd (List.mem_of_find?_eq_some hf)
    rw [hkey] at hfind'
    simp [hfind']

/-- EnvTyped の連結(左の文脈ドメインが左の環境で被覆されているとき) -/
theorem envTyped_append {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ₁ Γ₂ : TyCtx} {ρ₁ ρ₂ : Env}
    (h₁ : EnvTyped SD SP SF Γ₁ ρ₁)
    (hcover : ∀ y, TyCtx.find? Γ₁ y ≠ none → Env.find? ρ₁ y ≠ none)
    (h₂ : EnvTyped SD SP SF Γ₂ ρ₂) :
    EnvTyped SD SP SF (Γ₁ ++ Γ₂) (ρ₁ ++ ρ₂) := by
  intro y v hfind
  cases hρ₁ : Env.find? ρ₁ y with
  | some v₁ =>
    have : Env.find? (ρ₁ ++ ρ₂) y = some v₁ := Env.find?_append_left hρ₁
    rw [hfind] at this
    obtain rfl := Option.some.inj this
    obtain ⟨σ, hΓ, hty⟩ := h₁ y v hρ₁
    refine ⟨σ, ?_, hty⟩
    simp only [TyCtx.find?] at hΓ ⊢
    cases hf : List.find? (fun pr => pr.1 == y) Γ₁ with
    | none => rw [hf] at hΓ; exact nomatch hΓ
    | some pr =>
      rw [list_find?_append_some hf]
      rw [hf] at hΓ
      exact hΓ
  | none =>
    have hΓ₁ : TyCtx.find? Γ₁ y = none := by
      cases hΓf : TyCtx.find? Γ₁ y with
      | none => rfl
      | some σ =>
        exfalso
        exact (hcover y (by simp [hΓf])) hρ₁
    have hstep : Env.find? (ρ₁ ++ ρ₂) y = Env.find? ρ₂ y := by
      apply Env.find?_append_right
      intro pr hpr heq
      have : Env.find? ρ₁ pr.1 ≠ none := by
        simp only [Env.find?]
        cases hf : List.find? (fun q => q.1 == pr.1) ρ₁ with
        | none =>
          have := List.find?_eq_none.mp hf pr hpr
          simp at this
        | some _ => simp
      rw [heq] at this
      exact this hρ₁
    rw [hstep] at hfind
    obtain ⟨σ, hΓ, hty⟩ := h₂ y v hfind
    refine ⟨σ, ?_, hty⟩
    simp only [TyCtx.find?] at hΓ₁ hΓ ⊢
    cases hf : List.find? (fun pr => pr.1 == y) Γ₁ with
    | some pr => rw [hf] at hΓ₁; exact nomatch hΓ₁
    | none =>
      rw [list_find?_append_none hf]
      exact hΓ

/-- matcher 値の反転:捕獲環境の型付けと T-MATCHER 型付けを取り出す -/
theorem envTyped_of_matcherV {SD : SigD} {SP : SigP} {SF : SigF}
    {ρm : Env} {cls : List Clause} {τ : Ty}
    (h : ValueTy SD SP SF (.matcherV ρm cls) (.matcher τ)) :
    ∃ Γm, EnvTyped SD SP SF Γm ρm ∧
      HasTy SD SP SF Γm (.matcher cls) (.matcher τ) := by
  cases h with
  | matcherV Γm hdom hty hmty =>
    refine ⟨Γm, ?_, hmty⟩
    intro y v hfind
    obtain ⟨σ, hσ⟩ := hdom y v hfind
    exact ⟨σ, hσ, fun τ' hinst => hty y v σ τ' hfind hσ hinst⟩

/-! ## Lemma 5.5 本体(組み立ては未機械化) -/

/-- **Lemma 5.5 (Matching State Progress)**。
    証明は先頭マッチング木の場合分け(論文付録 C.2 の全ケース):
    変数/ワイルドカード/値パターンは MS-SOME-* / MS-PROD-SOME / catch-all、
    構成子パターンは構造前提が裸変数マッチャーを排除し
    (`something_rejected_at_data`・`prod_rejected_at_data`、Canonical.lean)
    Coverage (Def 4.2(3)) と arm exhaustiveness (1c) で MS-MATCHER が発火、
    タプルは MS-TUPLE または積型 Coverage、
    and/or/パターン関数/MNode は構文主導。
    前提補題(本ファイル上部+Canonical.lean)は証明済み;
    残る組み立ては README ロードマップ参照。 -/
theorem ms_progress
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {Δgoal : BindCtx}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)     -- 分解関数の停止仮定(§5)
    (hSigF : SigFWF SD SP SF Γ)
    (hwt : WTState SD SP SF Γ s Δgoal)
    (hne : s.S ≠ []) :
    ∃ ss, Step SF s ss := by
  sorry

end TypePM
