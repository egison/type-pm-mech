import TypePM.Metatheory.Preservation
import TypePM.Metatheory.Canonical
import TypePM.Metatheory.Adequacy

/-!
# Lemma 5.5:マッチング状態の進行 (Matching State Progress) — **証明済み**

整型な非終端状態は必ず簡約できる(l = 0 は正当なマッチ失敗であり、行き詰まりではない)。
本体 `ms_progress` は `WTTree.rec` の結合再帰子(木 motive+スタック motive)による。
成立には ValueTy.something の裸変数固定(README 設計判断 16)と
armExh のインスタンス閉包(同 17)が必要だった。

前提補題(本ファイルで証明):
* `ListSigOK`・`canonical_list` — リスト型の値は `listOfV` で分解できる
  (分解関数の返り値 [(τ⃗)] を MS-MATCHER の継続に直すために使う)
* `clausesTy_mem`・`armsTy_mem` — T-MATCHER の節/アーム型付けの member 取り出し
* `mapM_eq_some` — 要素ごとの成功から `mapM` の成功へ
* `decomposeME_tuple` — 次マッチャー式のタプル分解の反転
* `pdMatch_typed` — dp 束縛の型付け(Lem 5.4 の dp 版;(b) でも使う)
* `vshape_applyTS`・`armExh_instance` — VShape の代入安定性と Def 4.2(1c) の発火
* `ppm_total`・`ppm_length` — 形状一致なら PPM は成功し、抽出数=穴対数
* `clause_walk`・`arms_walk` — 節・アームを先頭から歩く MS-MATCHER 系導出の構成

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

/-! ## 代入の合成と VShape の代入安定性(armExh のインスタンス発火に使用) -/

theorem applyTSList_eq_map (θ : TySubst) : ∀ (l : List Ty),
    applyTSList θ l = l.map (Ty.applyTS θ)
  | [] => rfl
  | t :: l => by simp [applyTSList, applyTSList_eq_map θ l]

mutual
/-- 各自由変数上で「θ' = U ∘ θ」ならば適用結果も合成に一致する -/
theorem applyTS_comp_pointwise : ∀ (τ : Ty) {θ θ' U : TySubst},
    (∀ a ∈ τ.ftv, TySubst.appVar θ' a = (TySubst.appVar θ a).applyTS U) →
    τ.applyTS θ' = (τ.applyTS θ).applyTS U
  | .var a, θ, θ', U, h => by
      simpa [Ty.applyTS] using h a (by simp [Ty.ftv])
  | .int, _, _, _, _ => rfl
  | .bool, _, _, _, _ => rfl
  | .data n ts, θ, θ', U, h => by
      simp only [Ty.applyTS]
      rw [applyTSList_comp_pointwise ts fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .prod ts, θ, θ', U, h => by
      simp only [Ty.applyTS]
      rw [applyTSList_comp_pointwise ts fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .fn t₁ t₂, θ, θ', U, h => by
      simp only [Ty.applyTS]
      rw [applyTS_comp_pointwise t₁ fun a ha =>
            h a (by simp only [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_comp_pointwise t₂ fun a ha =>
            h a (by simp only [Ty.ftv, List.mem_append]; exact .inr ha)]
  | .matcher t, θ, θ', U, h => by
      simp only [Ty.applyTS]
      rw [applyTS_comp_pointwise t fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .slot t₁ t₂, θ, θ', U, h => by
      simp only [Ty.applyTS]
      rw [applyTS_comp_pointwise t₁ fun a ha =>
            h a (by simp only [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_comp_pointwise t₂ fun a ha =>
            h a (by simp only [Ty.ftv, List.mem_append]; exact .inr ha)]

theorem applyTSList_comp_pointwise : ∀ (ts : List Ty) {θ θ' U : TySubst},
    (∀ a ∈ ftvList ts, TySubst.appVar θ' a = (TySubst.appVar θ a).applyTS U) →
    applyTSList θ' ts = applyTSList U (applyTSList θ ts)
  | [], _, _, _, _ => rfl
  | t :: ts, θ, θ', U, h => by
      simp only [applyTSList]
      rw [applyTS_comp_pointwise t fun a ha =>
            h a (by simp only [ftvList, List.mem_append]; exact .inl ha),
          applyTSList_comp_pointwise ts fun a ha =>
            h a (by simp only [ftvList, List.mem_append]; exact .inr ha)]
end

theorem zip_map_self {α β} (f : α → β) : ∀ (l : List α),
    l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [List.zip_cons_cons, zip_map_self f l]

theorem find?_pair_map (f : Nat → Ty) (a : Nat) : ∀ (l : List Nat), a ∈ l →
    List.find? (fun pr => pr.1 == a) (l.map fun i => (i, f i)) = some (a, f a)
  | [], h => nomatch h
  | b :: l, h => by
      simp only [List.map_cons, List.find?]
      cases hba : (b == a) with
      | true =>
          have hb : b = a := by simpa using hba
          subst hb
          rfl
      | false =>
          have : a ∈ l := by
            rcases List.mem_cons.mp h with rfl | hl
            · simp at hba
            · exact hl
          exact find?_pair_map f a l this

theorem appVar_zip_range_map (f : Nat → Ty) {n a : Nat} (h : a < n) :
    TySubst.appVar ((List.range n).zip ((List.range n).map f)) a = f a := by
  unfold TySubst.appVar
  rw [zip_map_self, find?_pair_map f a _ (List.mem_range.mpr h)]

/-- 有界変数の型では「インスタンス化してから U」は「U を通した列でのインスタンス化」 -/
theorem instSig_applyTS {ts : List Ty} {U : TySubst} {np : Nat} (τa : Ty)
    (hb : ∀ a ∈ τa.ftv, a < np) :
    (Ty.instSig ts τa).applyTS U =
    Ty.instSig ((List.range np).map fun i => (Ty.instSig ts (.var i)).applyTS U) τa := by
  generalize hts' : ((List.range np).map fun i => (Ty.instSig ts (.var i)).applyTS U) = ts'
  have hlen : ts'.length = np := by rw [← hts']; simp
  symm
  unfold Ty.instSig
  rw [hlen]
  refine applyTS_comp_pointwise τa fun a ha => ?_
  rw [← hts', appVar_zip_range_map _ (hb a ha)]
  rfl

theorem ftvList_map_var : ∀ (l : List Nat), ftvList (l.map .var) = l
  | [] => rfl
  | a :: l => by simp [ftvList, Ty.ftv, ftvList_map_var l]

theorem ftv_res_lt {sig : CtorSig} (hwf : CtorSigWF sig) :
    ∀ a ∈ sig.res.ftv, a < sig.nparams := by
  obtain ⟨⟨n, hres⟩, -⟩ := hwf
  rw [hres]
  intro a ha
  simp only [Ty.ftv] at ha
  rw [ftvList_map_var] at ha
  exact List.mem_range.mp ha

theorem zip_map_right' {α β γ} (f : β → γ) : ∀ (l₁ : List α) (l₂ : List β),
    l₁.zip (l₂.map f) = (l₁.zip l₂).map fun pr => (pr.1, f pr.2)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
      simp [List.zip_cons_cons, zip_map_right' f l₁ l₂]

/-- **VShape の代入安定性**:形状型付けは任意の型代入で保たれる。
    Def 4.2(1c) をマッチャー型のインスタンス(使用 site の値型)で発火させる鍵。 -/
theorem vshape_applyTS {SD : SigD} (hwfD : SigDWF SD) (U : TySubst) :
    ∀ {v : Value} {τ : Ty}, VShape SD v τ → VShape SD v (τ.applyTS U) := by
  intro v τ h
  induction h with
  | @ctor C sig ts vs hfind hlen hall ih =>
      have hwf := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [instSig_applyTS sig.res (ftv_res_lt hwf)]
      refine VShape.ctor hfind hlen ?_
      intro pr hpr
      have hargsmap :
          sig.args.map (Ty.instSig
            ((List.range sig.nparams).map fun i => (Ty.instSig ts (.var i)).applyTS U)) =
          (sig.args.map (Ty.instSig ts)).map (Ty.applyTS U) := by
        rw [List.map_map]
        exact List.map_congr_left fun τa hτa =>
          (instSig_applyTS τa fun a ha => hwf.2 a (mem_ftvList_of_mem hτa ha)).symm
      rw [hargsmap, zip_map_right'] at hpr
      obtain ⟨pr', hpr', rfl⟩ := List.mem_map.mp hpr
      exact ih pr' hpr'
  | tuple hlen hall ih =>
      simp only [Ty.applyTS]
      rw [applyTSList_eq_map]
      refine VShape.tuple (by simpa using hlen) ?_
      intro pr hpr
      rw [zip_map_right'] at hpr
      obtain ⟨pr', hpr', rfl⟩ := List.mem_map.mp hpr
      exact ih pr' hpr'
  | lit => exact VShape.lit
  | closure => simp only [Ty.applyTS]; exact VShape.closure
  | matcherV => simp only [Ty.applyTS]; exact VShape.matcherV
  | something => simp only [Ty.applyTS]; exact VShape.something
  | matcherTuple => simp only [Ty.applyTS]; exact VShape.matcherTuple
  | slotAny => simp only [Ty.applyTS]; exact VShape.slotAny

/-- Unifiable τm τ と v : τ から、armExh の量化域 VShape v (τm.applyTS U) を作る -/
theorem armExh_instance {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) {cls : List Clause} {τm τ : Ty} {v : Value}
    (hcons : ConsistentClauses SD SP cls τm)
    (huni : Unifiable τm τ) (hv : ValueTy SD SP SF v τ) :
    ∀ cl ∈ cls, ∃ arm ∈ cl.2.2, (pdMatch arm.1 v).isSome := by
  obtain ⟨U, hU⟩ := huni
  intro cl hcl
  exact hcons.armExh cl hcl U v (by
    rw [hU]
    exact vshape_applyTS hwfD U (vshape_of_valueTy hv))

/-! ## 改名・値型付けの反転(構造前提による却下と MS-TUPLE の形) -/

theorem applyRenList_length (r : TyVar → TyVar) : ∀ (l : List Ty),
    (applyRenList r l).length = l.length
  | [] => rfl
  | t :: l => by simp [applyRenList, applyRenList_length r l]

/-- 改名先がデータ頭なら元もデータ頭(同名・同アリティ) -/
theorem renamesTo_data_inv {τm τm' : Ty} {n : String} {l' : List Ty}
    (h : RenamesTo τm τm') (he : τm' = .data n l') :
    ∃ l, τm = .data n l ∧ l.length = l'.length := by
  obtain ⟨r, -, hr⟩ := h
  rw [← hr] at he
  cases τm with
  | var a => simp [Ty.applyRen] at he
  | int => simp [Ty.applyRen] at he
  | bool => simp [Ty.applyRen] at he
  | data n₂ l₂ =>
      simp only [Ty.applyRen, Ty.data.injEq] at he
      exact ⟨l₂, by rw [he.1], by rw [← he.2, applyRenList_length]⟩
  | prod ts => simp [Ty.applyRen] at he
  | fn t₁ t₂ => simp [Ty.applyRen] at he
  | matcher t => simp [Ty.applyRen] at he
  | slot t₁ t₂ => simp [Ty.applyRen] at he

/-- 改名先が積頭なら元も積頭(同アリティ) -/
theorem renamesTo_prod_inv {τm τm' : Ty} {l' : List Ty}
    (h : RenamesTo τm τm') (he : τm' = .prod l') :
    ∃ l, τm = .prod l ∧ l.length = l'.length := by
  obtain ⟨r, -, hr⟩ := h
  rw [← hr] at he
  cases τm with
  | var a => simp [Ty.applyRen] at he
  | int => simp [Ty.applyRen] at he
  | bool => simp [Ty.applyRen] at he
  | data n₂ l₂ => simp [Ty.applyRen] at he
  | prod ts =>
      simp only [Ty.applyRen, Ty.prod.injEq] at he
      exact ⟨ts, rfl, by rw [← he, applyRenList_length]⟩
  | fn t₁ t₂ => simp [Ty.applyRen] at he
  | matcher t => simp [Ty.applyRen] at he
  | slot t₁ t₂ => simp [Ty.applyRen] at he

/-- something の内在マッチャー型は裸変数(T-SOME の評価像;ValueTy 改定後の反転) -/
theorem valueTy_something_var {SD : SigD} {SP : SigP} {SF : SigF} {τm : Ty}
    (h : ValueTy SD SP SF .something (.matcher τm)) : ∃ a, τm = .var a := by
  cases h with
  | something => exact ⟨_, rfl⟩

/-- タプル値のマッチャー型は積マッチャー(prodMatcher の反転) -/
theorem valueTy_tuple_matcher_inv {SD : SigD} {SP : SigP} {SF : SigF}
    {ms : List Value} {τm : Ty}
    (h : ValueTy SD SP SF (.tuple ms) (.matcher τm)) :
    ∃ τs, τm = .prod τs ∧ ms.length = τs.length ∧
      ∀ pr ∈ ms.zip τs, ValueTy SD SP SF pr.1 (.matcher pr.2) := by
  cases h with
  | prodMatcher hlen hall => exact ⟨_, rfl, hlen, hall⟩

/-- matcherV 値の整合性(T-MATCHER premise の取り出し) -/
theorem valueTy_matcherV_consistent {SD : SigD} {SP : SigP} {SF : SigF}
    {ρm : Env} {cls : List Clause} {τm : Ty}
    (h : ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm)) :
    ConsistentClauses SD SP cls τm := by
  obtain ⟨Γm, -, hty⟩ := envTyped_of_matcherV h
  cases hty with
  | matcherE hclsty hcons => exact hcons
  | coerceTupleMatcher hpre => cases hpre

/-- matcherV 値の節型付け(T-MATCHER premise の取り出し、Γm ごと) -/
theorem valueTy_matcherV_clausesTy {SD : SigD} {SP : SigP} {SF : SigF}
    {ρm : Env} {cls : List Clause} {τm : Ty}
    (h : ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm)) :
    ∃ Γm, ClausesTy SD SP SF Γm τm cls := by
  obtain ⟨Γm, -, hty⟩ := envTyped_of_matcherV h
  cases hty with
  | matcherE hclsty hcons => exact ⟨Γm, hclsty⟩
  | coerceTupleMatcher hpre => cases hpre

/-- タプル式の評価はタプル値(反転) -/
theorem eval_tuple_inv {SF : SigF} {ρ : Env} {es : List Expr} {v : Value}
    (h : Eval SF ρ (.tuple es) v) :
    ∃ vs, v = .tuple vs ∧ es.length = vs.length := by
  cases h with
  | tuple hlen hall => exact ⟨_, rfl, hlen⟩

theorem prodK_of_len_ne_one {l : List Ty} (h : l.length ≠ 1) : prodK l = .prod l := by
  cases l with
  | nil => rfl
  | cons τ l' =>
      cases l' with
      | nil => simp at h
      | cons τ₂ l'' => rfl

/-! ## PPM の全域性(形状一致なら成功;停止仮定つき)と抽出長 -/

mutual
theorem ppm_total {SF : SigF} (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v) :
    ∀ (pp : PPat) (p : Pattern) (ρ : Env), ppShapeOK pp p = true →
    ∃ ps' ρp, PPM SF ρ pp p (some (ps', ρp))
  | .hole, p, _, _ => ⟨[p], [], PPM.hole⟩
  | .wild, p, ρ, h => by
      cases p
      case wild => exact ⟨[], [], PPM.wild⟩
      all_goals simp [ppShapeOK] at h
  | .pval y, p, ρ, h => by
      cases p
      case pval M =>
        obtain ⟨v, hv⟩ := htotal ρ M
        exact ⟨[], [(y, v)], PPM.pval hv⟩
      all_goals simp [ppShapeOK] at h
  | .ctor c pps, p, ρ, h => by
      cases p
      case pctor c' ps =>
        simp only [ppShapeOK, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hlist⟩ := h
        obtain ⟨rs, hl1, hl2, hall⟩ := ppm_total_list htotal pps ps ρ hlist
        exact ⟨_, _, PPM.ctor hl1 hl2 hall⟩
      all_goals simp [ppShapeOK] at h
  | .tuple pps, p, ρ, h => by
      cases p
      case ptuple ps =>
        simp only [ppShapeOK] at h
        obtain ⟨rs, hl1, hl2, hall⟩ := ppm_total_list htotal pps ps ρ h
        exact ⟨_, _, PPM.tuple hl1 hl2 hall⟩
      all_goals simp [ppShapeOK] at h

theorem ppm_total_list {SF : SigF} (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v) :
    ∀ (pps : List PPat) (ps : List Pattern) (ρ : Env), ppShapeOKList pps ps = true →
    ∃ rs, pps.length = ps.length ∧ (pps.zip ps).length = rs.length ∧
      ∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)
  | [], [], _, _ => ⟨[], rfl, rfl, by intro tr htr; cases htr⟩
  | [], _ :: _, _, h => by simp [ppShapeOKList] at h
  | _ :: _, [], _, h => by simp [ppShapeOKList] at h
  | pp :: pps, p :: ps, ρ, h => by
      simp only [ppShapeOKList, Bool.and_eq_true] at h
      obtain ⟨hh, ht⟩ := h
      obtain ⟨ps', ρp, hm⟩ := ppm_total htotal pp p ρ hh
      obtain ⟨rs, hl1, hl2, hall⟩ := ppm_total_list htotal pps ps ρ ht
      refine ⟨(ps', ρp) :: rs, by simp [hl1], by simp [List.zip_cons_cons, hl2], ?_⟩
      intro tr htr
      simp only [List.zip_cons_cons, List.mem_cons] at htr
      rcases htr with rfl | htr
      · exact hm
      · exact hall tr htr
end

mutual
/-- PPM の抽出パターン数 = PPTy の穴対数(型付け非依存の長さ対応) -/
theorem ppm_length {SF : SigF} {SP : SigP} :
    ∀ (pp : PPat) {ρ : Env} {p : Pattern} {ps' : List Pattern} {ρp : Env}
      {τ : Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx},
    PPM SF ρ pp p (some (ps', ρp)) → PPTy SP pp τ pairs Δpp →
    ps'.length = pairs.length
  | .hole, _, _, _, _, _, _, _, hm, hpp => by
      cases hm; cases hpp; rfl
  | .wild, _, _, _, _, _, _, _, hm, hpp => by
      cases hm; cases hpp; rfl
  | .pval y, _, _, _, _, _, _, _, hm, hpp => by
      cases hm; cases hpp; rfl
  | .ctor c pps, _, _, _, _, _, _, _, hm, hpp => by
      cases hm with
      | ctor hl1 hl2 hall =>
        cases hpp with
        | ctor hfind hpps hlenp hrefresh =>
          rw [← hlenp]
          exact ppm_length_list pps hl1 hl2 hall hpps
  | .tuple pps, _, _, _, _, _, _, _, hm, hpp => by
      cases hm with
      | tuple hl1 hl2 hall =>
        cases hpp with
        | tuple hpps hlenp hrefresh =>
          rw [← hlenp]
          exact ppm_length_list pps hl1 hl2 hall hpps

theorem ppm_length_list {SF : SigF} {SP : SigP} :
    ∀ (pps : List PPat) {ρ : Env} {ps : List Pattern}
      {rs : List (List Pattern × Env)} {τs : List Ty}
      {pairss : List (Ty × Ty)} {Δs : BindCtx},
    pps.length = ps.length → (pps.zip ps).length = rs.length →
    (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
    PPTys SP pps τs pairss Δs →
    ((rs.map (·.1)).flatten).length = pairss.length
  | [], _, ps, rs, _, _, _, hl1, hl2, _, hpps => by
      cases hpps
      cases ps with
      | cons _ _ => simp at hl1
      | nil =>
        cases rs with
        | cons _ _ => simp at hl2
        | nil => rfl
  | pp :: pps, _, ps, rs, _, _, _, hl1, hl2, hall, hpps => by
      cases hpps with
      | cons hpph hppt =>
        cases ps with
        | nil => simp at hl1
        | cons p ps' =>
          cases rs with
          | nil => simp [List.zip_cons_cons] at hl2
          | cons r rs' =>
            obtain ⟨nexts, ρpc⟩ := r
            have hh : PPM SF _ pp p (some (nexts, ρpc)) :=
              hall ((pp, p), (nexts, ρpc)) (by simp [List.zip_cons_cons])
            simp only [List.map_cons, List.flatten_cons, List.length_append]
            rw [ppm_length pp hh hpph,
                ppm_length_list pps (by simpa using hl1)
                  (by simpa [List.zip_cons_cons] using hl2)
                  (fun tr htr => hall tr
                    (by simp [List.zip_cons_cons]; exact .inr htr)) hppt]
end

/-! ## 一般形節の形状一致と catch-all witness -/

theorem ppShapeOK_hole (p : Pattern) : ppShapeOK .hole p = true := rfl

theorem ppShapeOKList_replicate_hole : ∀ (ps : List Pattern) {k : Nat},
    ps.length = k → ppShapeOKList (List.replicate k .hole) ps = true
  | [], _, h => by subst h; rfl
  | p :: ps, _, h => by
      subst h
      simp only [List.length_cons, List.replicate_succ, ppShapeOKList,
        Bool.and_eq_true]
      exact ⟨ppShapeOK_hole p, ppShapeOKList_replicate_hole ps rfl⟩

theorem generalPP_shape {c : String} {ps : List Pattern} {k : Nat}
    (h : ps.length = k) :
    ppShapeOK (generalPP c k) (.pctor c ps) = true := by
  simp only [generalPP, ppShapeOK, Bool.and_eq_true]
  exact ⟨by simp, ppShapeOKList_replicate_hole ps h⟩

theorem tupleGeneral_shape {ps : List Pattern} {k : Nat}
    (h : ps.length = k) :
    ppShapeOK (.tuple (List.replicate k .hole)) (.ptuple ps) = true := by
  simp only [ppShapeOK]
  exact ppShapeOKList_replicate_hole ps h

/-- catch-all 節は任意のパターンに形状一致する(Def 4.2(2)) -/
theorem catchall_witness {SD : SigD} {SP : SigP} {cls : List Clause}
    {τm : Ty} (p : Pattern)
    (hcons : ConsistentClauses SD SP cls τm) :
    ∃ cl ∈ cls, ppShapeOK cl.1 p = true := by
  obtain ⟨M, x, N, hmem⟩ := hcons.catchall
  exact ⟨(.hole, M, [(.var x, N)]), hmem, ppShapeOK_hole p⟩

/-- 鍵つき検索の存在(y がドメインにあれば find? が成功する) -/
theorem find?_key_of_mem {α} {l : List (String × α)} {y : String}
    (h : ∃ pr ∈ l, pr.1 = y) :
    ∃ q, List.find? (fun pr => pr.1 == y) l = some q ∧ q.1 = y := by
  obtain ⟨pr, hmem, hy⟩ := h
  cases hf : List.find? (fun pr => pr.1 == y) l with
  | none =>
      exfalso
      have := List.find?_eq_none.mp hf pr hmem
      simp [hy] at this
  | some q =>
      have := List.find?_some hf
      simp only [beq_iff_eq] at this
      exact ⟨q, rfl, this⟩

/-! ## 節・アーム歩き(MS-MATCHER 系規則の導出構成)

MAtom の節規則は先頭節を剥がして再帰するので、
「形状一致する節が(接尾辞に)ある」ことを不変量にリストを歩く。
評価の形(リストである・k 組である)には (a)-oracle `heval` を使う
(ppp_core と同じ流儀;結合帰納法での供給は README ロードマップ)。 -/

theorem arms_walk {SD : SigD} {SP : SigP} {SF : SigF} {Γm : TyCtx} {τm : Ty}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty} {ρ' : Env},
       Eval SF ρ' e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    {ρθ ρm ρp : Env} {p : Pattern} {v : Value} {pp : PPat} {M : Expr}
    {ps' : List Pattern} {pairs : List (Ty × Ty)} {Δi : BindCtx} {Ms : List Expr}
    (hpc : p.isClauseForm = true)
    (hppm : PPM SF ρθ pp p (some (ps', ρp)))
    (hppty : PPTy SP pp τm pairs Δi)
    (hMs : decomposeME M pairs.length = some Ms) :
    ∀ (arms : List (DPat × Expr)) (cls' : List Clause),
    ArmsTy SD SP SF Γm τm Δi (Ty.listT (prodK (pairs.map (·.2)))) arms →
    (∃ arm ∈ arms, (pdMatch arm.1 v).isSome) →
    ∃ conts θ', MAtom SF ρθ p (.matcherV ρm ((pp, M, arms) :: cls')) v conts θ'
  | [], _, _, hex => by
      obtain ⟨arm, hmem, _⟩ := hex
      cases hmem
  | (dp, N) :: arms', cls', harms, hex => by
      cases harms with
      | cons hpd hNty harmsT =>
        cases hpdm : pdMatch dp v with
        | none =>
            have hex' : ∃ arm ∈ arms', (pdMatch arm.1 v).isSome := by
              obtain ⟨arm, hmem, hsome⟩ := hex
              rcases List.mem_cons.mp hmem with rfl | hmem
              · rw [hpdm] at hsome; simp at hsome
              · exact ⟨arm, hmem, hsome⟩
            obtain ⟨conts, θ', hMA⟩ :=
              arms_walk htotal heval hwfD hL hpc hppm hppty hMs arms' cls' harmsT hex'
            exact ⟨conts, θ', MAtom.matcherDPFail hpc hppm hpdm hMA⟩
        | some ρd =>
            have hk : ps'.length = pairs.length := ppm_length pp hppm hppty
            -- 分解関数の評価と像の形
            obtain ⟨vN, hevN⟩ := htotal (ρd ++ ρp ++ ρm) N
            have hvN := heval hevN hNty
            obtain ⟨tuples, hlist, helem⟩ :=
              canonical_list hwfD hL hvN (prodK (pairs.map (·.2))) rfl
            have hdec : ∀ t ∈ tuples, ∃ vs, decodeTuple ps'.length t = some vs := by
              intro t ht
              cases h1 : (ps'.length == 1) with
              | true => exact ⟨[t], by simp [decodeTuple, h1]⟩
              | false =>
                  have hne1 : (pairs.map (·.2)).length ≠ 1 := by
                    simp only [List.length_map, ← hk]
                    simpa using h1
                  have hty := helem t ht
                  rw [prodK_of_len_ne_one hne1] at hty
                  obtain ⟨vs, rfl, hlenvs, -⟩ := canonical_prod hwfD hty
                  have hveq : vs.length = ps'.length := by
                    rw [hlenvs]; simp [← hk]
                  exact ⟨vs, by simp [decodeTuple, h1, hveq]⟩
            obtain ⟨vss, hvss⟩ := mapM_eq_some tuples hdec
            -- 次マッチャー式の評価と分解
            obtain ⟨vM, hevM⟩ := htotal ρm M
            have hdecM : ∃ ms, decodeTuple ps'.length vM = some ms := by
              cases h1 : (ps'.length == 1) with
              | true => exact ⟨[vM], by simp [decodeTuple, h1]⟩
              | false =>
                  have hk1 : pairs.length ≠ 1 := by
                    rw [← hk]; simpa using h1
                  obtain ⟨hMt, hMslen⟩ := decomposeME_tuple hk1 hMs
                  subst hMt
                  obtain ⟨vms, rfl, hlenv⟩ := eval_tuple_inv hevM
                  have hveq : vms.length = ps'.length := by
                    rw [← hlenv, hMslen, hk]
                  exact ⟨vms, by simp [decodeTuple, h1, hveq]⟩
            obtain ⟨ms, hms⟩ := hdecM
            exact ⟨_, _, MAtom.matcher hpc hppm hpdm hevN hlist hvss hevM hms⟩

theorem clause_walk {SD : SigD} {SP : SigP} {SF : SigF} {Γm : TyCtx} {τm : Ty}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty} {ρ' : Env},
       Eval SF ρ' e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    {ρθ ρm : Env} {p : Pattern} {v : Value} (hpc : p.isClauseForm = true) :
    ∀ (cls' : List Clause),
    ClausesTy SD SP SF Γm τm cls' →
    (∀ cl ∈ cls', ∃ arm ∈ cl.2.2, (pdMatch arm.1 v).isSome) →
    (∃ cl ∈ cls', ppShapeOK cl.1 p = true) →
    ∃ conts θ', MAtom SF ρθ p (.matcherV ρm cls') v conts θ'
  | [], _, _, hex => by
      obtain ⟨cl, hmem, _⟩ := hex
      cases hmem
  | (pp, M, arms) :: cls', hclsty, hArm, hex => by
      cases hclsty with
      | cons hclty hclstyT =>
        cases hshape : ppShapeOK pp p with
        | false =>
            have hex' : ∃ cl ∈ cls', ppShapeOK cl.1 p = true := by
              obtain ⟨cl, hmem, htrue⟩ := hex
              rcases List.mem_cons.mp hmem with rfl | hmem
              · rw [hshape] at htrue; simp at htrue
              · exact ⟨cl, hmem, htrue⟩
            obtain ⟨conts, θ', hMA⟩ :=
              clause_walk htotal heval hwfD hL hpc cls' hclstyT
                (fun cl h => hArm cl (List.mem_cons_of_mem _ h)) hex'
            exact ⟨conts, θ', MAtom.matcherPPFail hpc (PPM.fail hshape) hMA⟩
        | true =>
            obtain ⟨ps', ρp, hppm⟩ := ppm_total htotal pp p ρθ hshape
            cases hclty with
            | mk hppty hdecM hslots harms =>
              exact arms_walk htotal heval hwfD hL hpc hppm hppty hdecM arms cls' harms
                (hArm (pp, M, arms) (by simp))

/-- matcherV に対する原子は必ず簡約できる(形状一致節の存在を仮定に取る核補題) -/
theorem matcherV_progress {SD : SigD} {SP : SigP} {SF : SigF}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty} {ρ' : Env},
       Eval SF ρ' e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    {ρθ ρm : Env} {cls : List Clause} {p : Pattern} {v : Value} {τm τ : Ty}
    (hpc : p.isClauseForm = true)
    (hm : ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm))
    (huni : Unifiable τm τ) (hv : ValueTy SD SP SF v τ)
    (hwit : ∃ cl ∈ cls, ppShapeOK cl.1 p = true) :
    ∃ conts θ', MAtom SF ρθ p (.matcherV ρm cls) v conts θ' := by
  obtain ⟨Γm, hclsty⟩ := valueTy_matcherV_clausesTy hm
  exact clause_walk htotal heval hwfD hL hpc cls hclsty
    (armExh_instance hwfD (valueTy_matcherV_consistent hm) huni hv) hwit

/-! ## Lemma 5.5 本体 -/

/-- 整型マッチング木の先頭は必ず簡約できる(WTTree/WTStack の結合再帰子による;
    embed 原子は呼び出し側(mnode の varpat / トップの Φ=[])で除外する)。 -/
theorem wtTree_progress {SD : SigD} {SP : SigP} {SF : SigF} {Γ₀ : TyCtx}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty} {ρ' : Env},
       Eval SF ρ' e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hSigF : SigFWF SD SP SF Γ₀)
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    {Γ : TyCtx} {Φ : PatParamCtx} {Δ Δ' : BindCtx} {t : Tree}
    (hwt : WTTree SD SP SF Γ Φ Δ t Δ') :
    ∀ (S : List Tree) (ρ : Env) (θ : Subst),
    (∀ y m v, t ≠ .atom ⟨.embed y, m, v⟩) →
    ∃ ss, Step SF ⟨t :: S, ρ, θ⟩ ss := by
  refine WTTree.rec (SD := SD) (SP := SP) (SF := SF)
    (motive_1 := fun _Γ _Φ _Δ t _Δ' _ =>
      ∀ (S : List Tree) (ρ : Env) (θ : Subst),
      (∀ y m v, t ≠ .atom ⟨.embed y, m, v⟩) →
      ∃ ss, Step SF ⟨t :: S, ρ, θ⟩ ss)
    (motive_2 := fun _Γ _Φ _Δ St _Δ' _ =>
      ∀ (t₀ : Tree) (rest : List Tree), St = t₀ :: rest →
      ∀ (ρ : Env) (θ : Subst),
      (∀ y m v, t₀ ≠ .atom ⟨.embed y, m, v⟩) →
      ∃ ss, Step SF ⟨t₀ :: rest, ρ, θ⟩ ss)
    ?_ ?_ ?_ ?_ ?_ hwt
  -- WT-ATOM:原子の場合分け(論文付録 C.2 の全ケース)
  case _ =>
    intro Γ Φ Δ Δ' p m v τ τp τt τm τm' hp hm hren how htt htm hok hv _hvps
    intro S ρ θ hne
    cases p with
    | embed y => exact absurd rfl (hne y m v)
    | pand p₁ p₂ => exact ⟨_, Step.reduce MAtom.and⟩
    | por p₁ p₂ => exact ⟨_, Step.reduce MAtom.or⟩
    | papp f qs =>
        cases hp with
        | papp hfind hqs hd1 hd2 =>
          rename_i sig ss ts duals
          refine ⟨_, Step.patfunEnter hfind ?_⟩
          have h1 : qs.length = duals.length := patTys_length hqs
          have h2 := congrArg List.length hd1
          have h3 : sig.params.length = sig.argDuals.length :=
            (hSigF _ (List.mem_of_find?_eq_some hfind)).arity
          simp only [List.length_map] at h2
          omega
    | pvar x =>
        cases hok with
        | something => exact ⟨_, Step.reduce MAtom.someVar⟩
        | prod hall => exact ⟨_, Step.reduce (MAtom.prodSome rfl)⟩
        | consistent _ =>
            obtain ⟨conts, θ', hMA⟩ :=
              matcherV_progress (p := .pvar x) htotal heval hwfD hL rfl hm htm hv
                (catchall_witness _ (valueTy_matcherV_consistent hm))
            exact ⟨_, Step.reduce hMA⟩
    | wild =>
        cases hok with
        | something => exact ⟨_, Step.reduce MAtom.someWC⟩
        | prod hall => exact ⟨_, Step.reduce (MAtom.prodSome rfl)⟩
        | consistent _ =>
            obtain ⟨conts, θ', hMA⟩ :=
              matcherV_progress (p := .wild) htotal heval hwfD hL rfl hm htm hv
                (catchall_witness _ (valueTy_matcherV_consistent hm))
            exact ⟨_, Step.reduce hMA⟩
    | pval e =>
        cases hok with
        | something =>
            obtain ⟨ve, hev⟩ := htotal (θ ++ ρ) e
            cases hsE : ve.structEq v with
            | true => exact ⟨_, Step.reduce (MAtom.someValEq hev hsE)⟩
            | false => exact ⟨_, Step.reduce (MAtom.someValNeq hev hsE)⟩
        | prod hall => exact ⟨_, Step.reduce (MAtom.prodSome rfl)⟩
        | consistent _ =>
            obtain ⟨conts, θ', hMA⟩ :=
              matcherV_progress (p := .pval e) htotal heval hwfD hL rfl hm htm hv
                (catchall_witness _ (valueTy_matcherV_consistent hm))
            exact ⟨_, Step.reduce hMA⟩
    | pctor c ps =>
        cases hp with
        | pctor hfindSP hps hd1 hd2 =>
          rename_i sig ss ts duals
          obtain ⟨⟨n, hres⟩, -⟩ := hwfP _ (List.mem_of_find?_eq_some hfindSP)
          rw [hres] at how
          simp only [Ty.instSig, Ty.applyTS] at how
          cases hok with
          | something =>
              exfalso
              obtain ⟨a, rfl⟩ := valueTy_something_var hm
              exact something_rejected_at_data hren how
          | prod hall =>
              exfalso
              obtain ⟨τs, rfl, -, -⟩ := valueTy_tuple_matcher_inv hm
              exact prod_rejected_at_data hren how
          | consistent _ =>
              -- Coverage で一般形節が witness
              obtain ⟨lm', hm', -⟩ := oneWay_data how
              obtain ⟨lm, hlm, -⟩ := renamesTo_data_inv hren hm'
              have hcons := valueTy_matcherV_consistent hm
              have hhm : Ty.headMatches sig.res τm = true := by
                rw [hres, hlm]; simp [Ty.headMatches]
              obtain ⟨M₀, arms₀, hmem⟩ :=
                hcons.coverage _ (List.mem_of_find?_eq_some hfindSP) hhm
              have hlen : ps.length = sig.args.length := by
                have h1 := patTys_length hps
                have h2 := congrArg List.length hd1
                simp only [List.length_map] at h2
                omega
              obtain ⟨conts, θ', hMA⟩ :=
                matcherV_progress (p := .pctor c ps) htotal heval hwfD hL rfl hm htm hv
                  ⟨(generalPP c sig.args.length, M₀, arms₀), hmem,
                    generalPP_shape hlen⟩
              exact ⟨_, Step.reduce hMA⟩
    | ptuple ps =>
        cases hp with
        | ptuple hps =>
          rename_i duals
          cases hok with
          | something =>
              exfalso
              obtain ⟨a, rfl⟩ := valueTy_something_var hm
              exact something_rejected_at_prod hren how
          | prod hall =>
              -- MS-TUPLE
              obtain ⟨τs, hτm, hlenms, hcomp⟩ := valueTy_tuple_matcher_inv hm
              obtain ⟨l', hl', hlen'⟩ := oneWay_prod how
              obtain ⟨l'', hl'', hlen''⟩ := renamesTo_prod (hτm ▸ hren)
              have hleql : l'.length = l''.length := by
                have h := hl'.symm.trans hl''
                injection h with h
                rw [h]
              rw [hτm] at htm
              obtain ⟨τs₂, rfl, hlen₂⟩ := valueTy_unifiable_prod hwfD hv htm
              obtain ⟨vs, rfl, hlenvs, -⟩ := canonical_prod hwfD hv
              have hlps := patTys_length hps
              have hlenmap : l'.length = duals.length := by simpa using hlen'
              refine ⟨_, Step.reduce (MAtom.tuple ?_ ?_)⟩
              · omega
              · omega
          | consistent _ =>
              -- 積型 Coverage で一般タプル節が witness
              obtain ⟨l', hl', hlen'⟩ := oneWay_prod how
              obtain ⟨τs, hτs, hlenτs⟩ := renamesTo_prod_inv hren hl'
              have hcons := valueTy_matcherV_consistent hm
              obtain ⟨M₀, arms₀, hmem⟩ := hcons.coverageProd τs hτs
              have hlen : ps.length = τs.length := by
                have h1 := patTys_length hps
                simp only [List.length_map] at hlen'
                omega
              obtain ⟨conts, θ', hMA⟩ :=
                matcherV_progress (p := .ptuple ps) htotal heval hwfD hL rfl hm htm hv
                  ⟨(.tuple (List.replicate τs.length .hole), M₀, arms₀), hmem,
                    tupleGeneral_shape hlen⟩
              exact ⟨_, Step.reduce hMA⟩
  -- WT-ATOM-TUPLE:成分分解形はそのまま MS-TUPLE で簡約できる
  case _ =>
    intro Γ Φ Δ Δ' ps ms vs hlen1 hlen2 _hstack _ih_stack
    intro S ρ θ _hne
    exact ⟨_, Step.reduce (MAtom.tuple hlen1 hlen2)⟩
  -- WT-MNODE:内側スタックの場合分け(varpat / done / 内側ステップ)
  case _ =>
    intro Γ Φ Δ Δ' S' ρf θf piE rem duals Γf Δθf Δfin
      h_j h_occ _h_q _h_d1 _h_d2 _h_θ _h_stack ih_stack
    intro S ρ θ _hne
    cases S' with
    | nil => exact ⟨_, Step.mnodeDone⟩
    | cons t' rest =>
        rcases Classical.em (∃ y m v, t' = .atom ⟨.embed y, m, v⟩) with
          ⟨y, m, v, rfl⟩ | hnotem
        · -- MS-MNODE-VARPAT:先頭 embed は接尾辞前提により Π にいる
          have hy : y ∈ rem.map (·.1) := by
            rw [← h_occ]
            simp [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars]
          obtain ⟨j, hj⟩ := h_j
          have hy' : ∃ pr ∈ piE, pr.1 = y := by
            rw [hj] at hy
            simp only [List.mem_map] at hy
            obtain ⟨pr, hpr, hfst⟩ := hy
            exact ⟨pr, List.mem_of_mem_drop hpr, hfst⟩
          obtain ⟨q, hfind, hqy⟩ := find?_key_of_mem hy'
          have hfind' : List.find? (fun pr => pr.1 == y) piE = some (y, q.2) := by
            rw [hfind]
            cases q
            cases hqy
            rfl
          exact ⟨_, Step.mnodeVarpat hfind'⟩
        · -- MS-MNODE-STEP:内側の先頭に再帰
          have hne' : ∀ y m v, t' ≠ .atom ⟨.embed y, m, v⟩ := by
            intro y m v heq
            exact hnotem ⟨y, m, v, heq⟩
          obtain ⟨ss', hss'⟩ := ih_stack t' rest rfl ρf θf hne'
          refine ⟨_, Step.mnodeStep ?_ hss'⟩
          intro y m v heq
          exact absurd heq (hne' y m v)
  -- WT-STACK-NIL
  case _ =>
    intro Γ Φ Δ t₀ rest heq
    exact nomatch heq
  -- WT-STACK-CONS
  case _ =>
    intro Γ Φ Δ₀ Δ₁ Δ' t St _htree _hstack ih_tree _ih_stack
    intro t₀ rest heq ρ θ hne
    cases heq
    exact ih_tree St ρ θ hne

/-- **Lemma 5.5 (Matching State Progress)**(**証明済み**)。
    整型な非終端状態は必ず簡約できる(l = 0 は正当な失敗であり行き詰まりではない)。
    場合分けは論文付録 C.2 のとおり:
    変数/ワイルドカード/値パターンは MS-SOME-* / MS-PROD-SOME / catch-all 節、
    構成子・タプルパターンでは構造前提が裸変数マッチャー・積マッチャーを却下し
    (`something_rejected_at_*`・`prod_rejected_at_data`;ValueTy.something の
    添字を T-SOME の字面どおり裸変数に固定したことが効く)、
    Coverage (Def 4.2(3)) の一般形節と arm exhaustiveness (1c) の
    インスタンス発火(`armExh_instance`)で MS-MATCHER が構成される。
    and/or/パターン関数は構文主導、MNode は varpat/done/内側ステップ。

    仮定:`htotal` = 式評価の停止(論文 §5 の分解関数停止仮定の大域形)、
    `heval` = (a)-oracle(`ppp_core` と同じ ∀Γ' 形;分解関数の像がリスト・
    k 組であることに使う。結合帰納法での供給は README ロードマップ参照)。 -/
theorem ms_progress
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {Δgoal : BindCtx}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)     -- 分解関数の停止仮定(§5)
    (heval : ∀ {Γ' : TyCtx} {e : Expr} {v : Value} {τ' : Ty} {ρ' : Env},
       Eval SF ρ' e v → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF v τ')
    (hSigF : SigFWF SD SP SF Γ)
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hwt : WTState SD SP SF Γ s Δgoal)
    (hne : s.S ≠ []) :
    ∃ ss, Step SF s ss := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  obtain ⟨S, ρ, θ⟩ := s
  cases hstack with
  | nil => exact absurd rfl hne
  | cons htree hstackT =>
      rename_i t St
      rcases Classical.em (∃ y m v, t = .atom ⟨.embed y, m, v⟩) with
        ⟨y, m, v, rfl⟩ | hnotem
      · -- トップレベルは Φ = [] なので embed 原子は整型でない
        exfalso
        cases htree with
        | atom hp _ _ _ _ _ _ _ =>
          cases hp with
          | embed hfind => exact nomatch hfind
      · exact wtTree_progress htotal heval hSigF hwfD hwfP hL htree St ρ θ
          (fun y m v heq => hnotem ⟨y, m, v, heq⟩)

end TypePM
