import TypePM.Metatheory.Progress
import TypePM.Metatheory.Safety

/-!
# Theorem 5.6 (Type Safety) — (a) 式評価の型付け・(b) マッチング状態保存

(a) `type_safety_a` は **oracle 分解で証明済み**:論文 §5.4 の結合帰納法のうち
Eval 側の帰納を `Eval.rec`(5 motive、他 4 判断は自明 motive)で機械化し、
他判断・他補題への依存を oracle 仮定に取る(Thm 5.7・Lem 5.4/5.5 と同じ流儀):

* `hb` = Theorem 5.6(b)(Step の状態保存)。EV-MATCHALL の探索を
  `search_mem_reaches` + `reaches_preservation` で反復するのに使う。
* `hgen` = HM 一般化補題(let 束縛値はスキームの全インスタンスで型付く)。
  宣言的な自由インスタンス化は matcher 添字の rigidity(§4.6)を失うため
  (bare-hole のみのマッチャー値を具体型へインスタンス化する導出が宣言的には
  書けてしまう)、rigidity を尊重する導出への制限つきで Stage 2 で放電する。
* `hinit` = matchAll site の初期マッチング状態の整型(WT-ATOM/WT-ATOM-TUPLE の
  組み立て)。vp-scoped premise(細部その 3;静的検査が既知形状 site で放電)と
  スロット witness の合成(成分改名の変数分離 = HasTy の改名補題)を含む。

型付けの強制(3 コアーション)は任意の式に適用できるが、強制の結論型は
matcher/slot に限られ premise は prod/matcher なので、強制の入れ子は
高々 2 段(coe2 → coe1)で必ず構文主導規則に到達する。各 Eval ケースは
`cases hty` をその深さだけ入れ子にし、強制層は値レベル対応物
(`slotV`/`prodMatcher`/`prodSlot`;README 設計判断 11)で追随する。

(b) `type_safety_b` は未機械化(sorry;README ロードマップ [b-3]〜[b-5])。
-/

namespace TypePM

/-! ## 環境型付けの拡張・分解 -/

/-- 閉包/マッチャー値に格納された 2 前提形から EnvTyped へ -/
theorem envTyped_of_parts {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {ρ : Env}
    (hdom : ∀ y v, Env.find? ρ y = some v → ∃ σ, TyCtx.find? Γ y = some σ)
    (hinst : ∀ y v σ τ', Env.find? ρ y = some v → TyCtx.find? Γ y = some σ →
       σ.Inst τ' → ValueTy SD SP SF v τ') :
    EnvTyped SD SP SF Γ ρ := fun y v hf =>
  ⟨(hdom y v hf).choose, (hdom y v hf).choose_spec,
    fun τ' hi => hinst y v _ τ' hf (hdom y v hf).choose_spec hi⟩

theorem envTyped_dom {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {ρ : Env} (hρ : EnvTyped SD SP SF Γ ρ) :
    ∀ y v, Env.find? ρ y = some v → ∃ σ, TyCtx.find? Γ y = some σ :=
  fun y v h => ⟨(hρ y v h).choose, (hρ y v h).choose_spec.1⟩

theorem envTyped_inst {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {ρ : Env} (hρ : EnvTyped SD SP SF Γ ρ) :
    ∀ y v σ τ', Env.find? ρ y = some v → TyCtx.find? Γ y = some σ →
       σ.Inst τ' → ValueTy SD SP SF v τ' := by
  intro y v σ τ' hf hσ hi
  obtain ⟨σ', hσ', hty⟩ := hρ y v hf
  have := hσ.symm.trans hσ'
  obtain rfl := Option.some.inj this
  exact hty τ' hi

/-- スキームつき環境拡張(let 束縛) -/
theorem envTyped_cons_scheme {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {ρ : Env} {x : String} {v : Value} {σ : Scheme}
    (hv : ∀ τ', σ.Inst τ' → ValueTy SD SP SF v τ')
    (hρ : EnvTyped SD SP SF Γ ρ) :
    EnvTyped SD SP SF ((x, σ) :: Γ) ((x, v) :: ρ) := by
  intro y w hfind
  simp only [Env.find?, List.find?] at hfind
  cases hxy : (x == y) with
  | true =>
      rw [hxy] at hfind
      simp only [Option.map] at hfind
      obtain rfl := Option.some.inj hfind
      refine ⟨σ, ?_, hv⟩
      simp only [TyCtx.find?, List.find?]
      rw [hxy]
      rfl
  | false =>
      rw [hxy] at hfind
      obtain ⟨σ', hσ', hty⟩ := hρ y w hfind
      refine ⟨σ', ?_, hty⟩
      simp only [TyCtx.find?, List.find?] at hσ' ⊢
      rw [hxy]
      exact hσ'

/-- 単相環境拡張(λ 適用・fix 展開) -/
theorem envTyped_cons {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {ρ : Env} {x : String} {v : Value} {τ : Ty}
    (hv : ValueTy SD SP SF v τ) (hρ : EnvTyped SD SP SF Γ ρ) :
    EnvTyped SD SP SF ((x, Scheme.mono τ) :: Γ) ((x, v) :: ρ) :=
  envTyped_cons_scheme (fun τ' hi => by rw [inst_mono hi]; exact hv) hρ

/-- 型付き代入は toCtx で環境型付けになる(matchAll の本体評価環境用) -/
theorem envTyped_of_substTyped {SD : SigD} {SP : SigP} {SF : SigF}
    {Δ : BindCtx} {θ : Subst} (h : SubstTyped SD SP SF Δ θ) :
    EnvTyped SD SP SF (BindCtx.toCtx Δ) θ := by
  refine envTyped_of_bindings ?_ h.2
  intro pr hpr
  rw [h.1, List.mem_reverse]
  exact List.mem_map_of_mem hpr

/-! ## 値レベルの強制追随(3 コアーションの値対応物) -/

theorem valueTy_coerce2 {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) {v : Value} {τs : List Ty}
    (h : ValueTy SD SP SF v (.prod (τs.map Ty.matcher))) :
    ValueTy SD SP SF v (.matcher (.prod τs)) := by
  obtain ⟨vs, rfl, hlen, hall⟩ := canonical_prod hwfD h
  refine ValueTy.prodMatcher (by simpa using hlen) ?_
  intro pr hpr
  refine hall (pr.1, Ty.matcher pr.2) ?_
  rw [zip_map_right']
  exact List.mem_map_of_mem hpr

theorem valueTy_coerce3 {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) {v : Value} {prs : List (Ty × Ty)}
    (h : ValueTy SD SP SF v (.prod (prs.map fun pr => Ty.slot pr.1 pr.2))) :
    ValueTy SD SP SF v (.slot (.prod (prs.map (·.1))) (.prod (prs.map (·.2)))) := by
  obtain ⟨vs, rfl, hlen, hall⟩ := canonical_prod hwfD h
  refine ValueTy.prodSlot (by simpa using hlen) ?_
  intro pr hpr
  refine hall (pr.1, Ty.slot pr.2.1 pr.2.2) ?_
  rw [zip_map_right']
  exact List.mem_map_of_mem hpr

/-! ## リスト値・プリミティブの型付け -/

theorem mkListV_typed {SD : SigD} {SP : SigP} {SF : SigF} (hL : ListSigOK SD) :
    ∀ {l : List Value} {τ : Ty}, (∀ x ∈ l, ValueTy SD SP SF x τ) →
    ValueTy SD SP SF (mkListV l) (Ty.listT τ)
  | [], τ, _ =>
      ValueTy.ctor (ts := [τ]) hL.1 rfl (by intro pr hpr; cases hpr)
  | v :: l, τ, h => by
      have hh := h v (by simp)
      have ht := mkListV_typed hL (l := l) (τ := τ)
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
      refine ValueTy.ctor (ts := [τ]) hL.2.1 rfl ?_
      intro pr hpr
      simp only [List.map_cons, List.map_nil, List.zip_cons_cons,
        List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact hh
      · rcases hpr with rfl | hpr
        · exact ht
        · simp at hpr

theorem primEval_typed_append {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    {v₁ v₂ v : Value} {τ : Ty}
    (h1 : ValueTy SD SP SF v₁ (Ty.listT τ)) (h2 : ValueTy SD SP SF v₂ (Ty.listT τ))
    (h : primEval .append [v₁, v₂] = some v) :
    ValueTy SD SP SF v (Ty.listT τ) := by
  simp only [primEval] at h
  obtain ⟨l₁, hl₁, h⟩ := bind_eq_some h
  obtain ⟨l₂, hl₂, h⟩ := bind_eq_some h
  obtain rfl := pure_eq_some h
  obtain ⟨l₁', hl₁', he₁⟩ := canonical_list hwfD hL h1 τ rfl
  obtain ⟨l₂', hl₂', he₂⟩ := canonical_list hwfD hL h2 τ rfl
  rw [hl₁] at hl₁'
  rw [hl₂] at hl₂'
  obtain rfl := Option.some.inj hl₁'
  obtain rfl := Option.some.inj hl₂'
  refine mkListV_typed hL ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact he₁ x hx
  · exact he₂ x hx

theorem primEval_typed_splits {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    {v₀ v : Value} {τ : Ty}
    (h0 : ValueTy SD SP SF v₀ (Ty.listT τ))
    (h : primEval .splits [v₀] = some v) :
    ValueTy SD SP SF v (Ty.listT (.prod [Ty.listT τ, Ty.listT τ])) := by
  simp only [primEval] at h
  obtain ⟨l, hl, h⟩ := bind_eq_some h
  obtain rfl := pure_eq_some h
  obtain ⟨l', hl', he⟩ := canonical_list hwfD hL h0 τ rfl
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  refine mkListV_typed hL ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  refine ValueTy.tuple rfl ?_
  intro pr hpr
  simp only [List.zip_cons_cons, List.mem_cons] at hpr
  rcases hpr with rfl | hpr
  · exact mkListV_typed hL fun x hx => he x (List.take_subset _ _ hx)
  · rcases hpr with rfl | hpr
    · exact mkListV_typed hL fun x hx => he x (List.drop_subset _ _ hx)
    · simp at hpr

/-! ## ctor 式の強制不可能性(Σ_D 整形性の下で prod/matcher 型に付かない) -/

theorem ctor_not_prod {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {c : String} {es : List Expr} {τs : List Ty}
    (hwfD : SigDWF SD) (h : HasTy SD SP SF Γ (.ctor c es) (.prod τs)) : False := by
  generalize hτ : (Ty.prod τs : Ty) = τx at h
  cases h with
  | ctor hfind hlen htys =>
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at hτ
      simp [Ty.instSig, Ty.applyTS] at hτ
  | coerceMatcherToSlot _ _ _ _ => exact Ty.noConfusion hτ
  | coerceTupleMatcher _ => exact Ty.noConfusion hτ
  | coerceSlotTuple _ => exact Ty.noConfusion hτ

theorem ctor_not_matcher {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {c : String} {es : List Expr} {τm : Ty}
    (hwfD : SigDWF SD) (h : HasTy SD SP SF Γ (.ctor c es) (.matcher τm)) : False := by
  generalize hτ : (Ty.matcher τm : Ty) = τx at h
  cases h with
  | ctor hfind hlen htys =>
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at hτ
      simp [Ty.instSig, Ty.applyTS] at hτ
  | coerceMatcherToSlot _ _ _ _ => exact Ty.noConfusion hτ
  | coerceTupleMatcher hpre => exact ctor_not_prod hwfD hpre
  | coerceSlotTuple _ => exact Ty.noConfusion hτ

/-! ## Theorem 5.6(a) -/

/-- **Theorem 5.6(a) (式評価の型付け)**(**oracle 分解で証明済み**)。
    Γ ⊢ e : τ で ρ が Γ で型付けられ、ρ, e ⇓ v ならば v : τ。
    oracle:`hb` = 5.6(b)、`hgen` = HM 一般化補題(rigidity 制限つき;Stage 2)、
    `hinit` = matchAll 初期状態の整型(vp-scoped + スロット witness 合成)。
    モジュール docstring を参照。 -/
theorem type_safety_a
    {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    (hb : ∀ {Γ' : TyCtx} {Δ : BindCtx} {s ss}, Step SF s ss →
       WTState SD SP SF Γ' s Δ → ∀ s' ∈ ss, WTState SD SP SF Γ' s' Δ)
    (hgen : ∀ {Γ' : TyCtx} {ρ' : Env} {e₁ : Expr} {v₁ : Value} {τ₁ : Ty}
       {L : List TyVar},
       Eval SF ρ' e₁ v₁ → EnvTyped SD SP SF Γ' ρ' → HasTy SD SP SF Γ' e₁ τ₁ →
       (∀ a ∈ L, a ∉ ftvCtx Γ') →
       ∀ τ', Scheme.Inst ⟨L, τ₁⟩ τ' → ValueTy SD SP SF v₁ τ')
    (hinit : ∀ {Γ' : TyCtx} {p : Pattern} {v_m v_t : Value}
       {τ_p τ_t : Ty} {Δ : BindCtx},
       PatTy SD SP SF Γ' [] [] p τ_p τ_t Δ →
       ValueTy SD SP SF v_m (.slot τ_p τ_t) →
       ValueTy SD SP SF v_t τ_t →
       WTStack SD SP SF Γ' [] [] [.atom ⟨p, v_m, v_t⟩] Δ)
    {ρ : Env} {e : Expr} {v : Value} {Γ : TyCtx} {τ : Ty}
    (hev : Eval SF ρ e v)
    (hρ : EnvTyped SD SP SF Γ ρ)
    (hty : HasTy SD SP SF Γ e τ) :
    ValueTy SD SP SF v τ := by
  refine Eval.rec (SF := SF)
    (motive_1 := fun ρ e v _ => ∀ (Γ : TyCtx) (τ : Ty), EnvTyped SD SP SF Γ ρ →
       HasTy SD SP SF Γ e τ → ValueTy SD SP SF v τ)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?evar ?elam ?efix ?eapp ?elit ?etuple ?ector ?eprim ?eletE ?esmth ?emtch ?emall
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    hev Γ τ hρ hty
  case evar =>
    intro ρ x v hfind Γ τ hρ hty
    -- 変数の土台:任意の型付け τ' に対する EnvTyped 検索
    have hbase : ∀ τ', HasTy SD SP SF Γ (.var x) τ' → ValueTy SD SP SF v τ' := by
      intro τ' h
      cases h with
      | var hσ hi => exact envTyped_inst hρ x v _ τ' hfind hσ hi
      | coerceMatcherToSlot hpre hren how huni =>
          cases hpre with
          | var hσ hi => exact ValueTy.slotV (envTyped_inst hρ x v _ _ hfind hσ hi) hren how huni
          | coerceTupleMatcher hpre2 =>
              cases hpre2 with
              | var hσ hi =>
                  exact ValueTy.slotV
                    (valueTy_coerce2 hwfD (envTyped_inst hρ x v _ _ hfind hσ hi))
                    hren how huni
      | coerceTupleMatcher hpre =>
          cases hpre with
          | var hσ hi => exact valueTy_coerce2 hwfD (envTyped_inst hρ x v _ _ hfind hσ hi)
      | coerceSlotTuple hpre =>
          cases hpre with
          | var hσ hi => exact valueTy_coerce3 hwfD (envTyped_inst hρ x v _ _ hfind hσ hi)
    exact hbase τ hty
  case elam =>
    intro ρ x e Γ τ hρ hty
    cases hty with
    | lam hbody =>
        exact ValueTy.closure Γ (envTyped_dom hρ) (envTyped_inst hρ)
          (fun _ => hbody) (fun f hf => nomatch hf)
    | coerceMatcherToSlot hpre _ _ _ =>
        cases hpre with
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case efix =>
    intro ρ f x e Γ τ hρ hty
    cases hty with
    | fixE hbody =>
        refine ValueTy.closure Γ (envTyped_dom hρ) (envTyped_inst hρ)
          (fun h => nomatch h) ?_
        intro g hg
        injection hg with hg
        subst hg
        exact hbody
    | coerceMatcherToSlot hpre _ _ _ =>
        cases hpre with
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case eapp =>
    intro ρ e₁ e₂ self ρ' x eb v₂ v hev₁ hev₂ hev₃ ih₁ ih₂ ih₃ Γ τ hρ hty
    -- 適用の土台:任意の (τ₁', τc) の関数型付けに対して
    have hcore : ∀ τ₁' τc, HasTy SD SP SF Γ e₁ (.fn τ₁' τc) →
        HasTy SD SP SF Γ e₂ τ₁' → ValueTy SD SP SF v τc := by
      intro τ₁' τc h1 h2
      have hclo := ih₁ Γ (.fn τ₁' τc) hρ h1
      have hv₂ := ih₂ Γ τ₁' hρ h2
      cases hclo with
      | closure Γc hdom hinst hnone hsome =>
          have hρc : EnvTyped SD SP SF Γc ρ' := envTyped_of_parts hdom hinst
          cases self with
          | none =>
              exact ih₃ _ τc (envTyped_cons hv₂ hρc) (hnone rfl)
          | some f =>
              have hself : ValueTy SD SP SF (.closure (some f) ρ' x eb)
                  (.fn τ₁' τc) :=
                ValueTy.closure Γc hdom hinst (fun h => nomatch h)
                  (fun g hg => by injection hg with hg; subst hg; exact hsome f rfl)
              exact ih₃ _ τc
                (envTyped_cons hv₂ (envTyped_cons hself hρc)) (hsome f rfl)
    cases hty with
    | app h1 h2 => exact hcore _ _ h1 h2
    | coerceMatcherToSlot hpre hren how huni =>
        cases hpre with
        | app h1 h2 => exact ValueTy.slotV (hcore _ _ h1 h2) hren how huni
        | coerceTupleMatcher hpre2 =>
            cases hpre2 with
            | app h1 h2 =>
                exact ValueTy.slotV (valueTy_coerce2 hwfD (hcore _ _ h1 h2))
                  hren how huni
    | coerceTupleMatcher hpre =>
        cases hpre with
        | app h1 h2 => exact valueTy_coerce2 hwfD (hcore _ _ h1 h2)
    | coerceSlotTuple hpre =>
        cases hpre with
        | app h1 h2 => exact valueTy_coerce3 hwfD (hcore _ _ h1 h2)
  case elit =>
    intro ρ n Γ τ hρ hty
    cases hty with
    | lit => exact ValueTy.lit
    | coerceMatcherToSlot hpre _ _ _ =>
        cases hpre with
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case etuple =>
    intro ρ es vs hlen hall ih Γ τ hρ hty
    -- タプルの土台:成分型列 τs' に対して
    have hcore : ∀ τs' : List Ty, es.length = τs'.length →
        (∀ pr ∈ es.zip τs', HasTy SD SP SF Γ pr.1 pr.2) →
        ValueTy SD SP SF (.tuple vs) (.prod τs') := by
      intro τs' hlen' htys
      refine ValueTy.tuple (by omega) ?_
      -- vs.zip τs' の各成分:es を経由して型付ける
      have main : ∀ (es' : List Expr) (vs' : List Value) (τs'' : List Ty),
          es'.length = vs'.length → es'.length = τs''.length →
          (∀ pr ∈ es'.zip vs', ∀ (Γ' : TyCtx) (τ' : Ty), EnvTyped SD SP SF Γ' ρ →
            HasTy SD SP SF Γ' pr.1 τ' → ValueTy SD SP SF pr.2 τ') →
          (∀ pr ∈ es'.zip τs'', HasTy SD SP SF Γ pr.1 pr.2) →
          ∀ pr ∈ vs'.zip τs'', ValueTy SD SP SF pr.1 pr.2 := by
        intro es'
        induction es' with
        | nil =>
            intro vs' τs'' h1 h2 _ _ pr hpr
            cases vs' with
            | cons _ _ => simp at h1
            | nil => cases hpr
        | cons e' es' ihes =>
            intro vs' τs'' h1 h2 hihs htys pr hpr
            cases vs' with
            | nil => simp at h1
            | cons v' vs' =>
              cases τs'' with
              | nil => simp at h2
              | cons τ'' τs'' =>
                simp only [List.zip_cons_cons, List.mem_cons] at hpr
                rcases hpr with rfl | hpr
                · exact hihs (e', v') (by simp [List.zip_cons_cons]) Γ τ'' hρ
                    (htys (e', τ'') (by simp [List.zip_cons_cons]))
                · exact ihes vs' τs'' (by simpa using h1) (by simpa using h2)
                    (fun q hq => hihs q (by simp [List.zip_cons_cons]; exact .inr hq))
                    (fun q hq => htys q (by simp [List.zip_cons_cons]; exact .inr hq))
                    pr hpr
      exact main es vs τs' hlen hlen' ih htys
    cases hty with
    | tuple hlen' htys => exact hcore _ hlen' htys
    | coerceMatcherToSlot hpre hren how huni =>
        cases hpre with
        | coerceTupleMatcher hpre2 =>
            cases hpre2 with
            | tuple hlen' htys =>
                exact ValueTy.slotV (valueTy_coerce2 hwfD (hcore _ hlen' htys))
                  hren how huni
    | coerceTupleMatcher hpre =>
        cases hpre with
        | tuple hlen' htys => exact valueTy_coerce2 hwfD (hcore _ hlen' htys)
    | coerceSlotTuple hpre =>
        cases hpre with
        | tuple hlen' htys => exact valueTy_coerce3 hwfD (hcore _ hlen' htys)
  case ector =>
    intro ρ c es vs hlen hall ih Γ τ hρ hty
    have hcore : ∀ (sig : CtorSig) (ts : List Ty),
        List.find? (fun pr => pr.1 == c) SD = some (c, sig) →
        es.length = sig.args.length →
        (∀ pr ∈ es.zip (sig.args.map (Ty.instSig ts)), HasTy SD SP SF Γ pr.1 pr.2) →
        ValueTy SD SP SF (.ctor c vs) (Ty.instSig ts sig.res) := by
      intro sig ts hfind hlen' htys
      refine ValueTy.ctor hfind (by omega) ?_
      have main : ∀ (es' : List Expr) (vs' : List Value) (τs'' : List Ty),
          es'.length = vs'.length → es'.length = τs''.length →
          (∀ pr ∈ es'.zip vs', ∀ (Γ' : TyCtx) (τ' : Ty), EnvTyped SD SP SF Γ' ρ →
            HasTy SD SP SF Γ' pr.1 τ' → ValueTy SD SP SF pr.2 τ') →
          (∀ pr ∈ es'.zip τs'', HasTy SD SP SF Γ pr.1 pr.2) →
          ∀ pr ∈ vs'.zip τs'', ValueTy SD SP SF pr.1 pr.2 := by
        intro es'
        induction es' with
        | nil =>
            intro vs' τs'' h1 h2 _ _ pr hpr
            cases vs' with
            | cons _ _ => simp at h1
            | nil => cases hpr
        | cons e' es' ihes =>
            intro vs' τs'' h1 h2 hihs htys pr hpr
            cases vs' with
            | nil => simp at h1
            | cons v' vs' =>
              cases τs'' with
              | nil => simp at h2
              | cons τ'' τs'' =>
                simp only [List.zip_cons_cons, List.mem_cons] at hpr
                rcases hpr with rfl | hpr
                · exact hihs (e', v') (by simp [List.zip_cons_cons]) Γ τ'' hρ
                    (htys (e', τ'') (by simp [List.zip_cons_cons]))
                · exact ihes vs' τs'' (by simpa using h1) (by simpa using h2)
                    (fun q hq => hihs q (by simp [List.zip_cons_cons]; exact .inr hq))
                    (fun q hq => htys q (by simp [List.zip_cons_cons]; exact .inr hq))
                    pr hpr
      exact main es vs _ hlen (by simpa using hlen') ih htys
    -- ctor 式の結論型は instSig(データ形);強制の premise(prod/matcher)には
    -- Σ_D 整形性の下で到達しない
    cases hty with
    | ctor hfind hlen' htys => exact hcore _ _ hfind hlen' htys
    | coerceMatcherToSlot hpre _ _ _ => exact absurd hpre (fun h => ctor_not_matcher hwfD h)
    | coerceTupleMatcher hpre => exact absurd hpre (fun h => ctor_not_prod hwfD h)
    | coerceSlotTuple hpre => exact absurd hpre (fun h => ctor_not_prod hwfD h)
  case eprim =>
    intro ρ op es vs v hlen hall hprim ih Γ τ hρ hty
    cases hty with
    | primAppend h1 h2 =>
        rename_i e₁ e₂ τel
        -- es は規則の形 [e₁, e₂] に固定される;vs を長さで分解
        cases vs with
        | nil => simp at hlen
        | cons v₁ vs' =>
          cases vs' with
          | nil => simp at hlen
          | cons v₂ vs'' =>
            cases vs'' with
            | cons _ _ => simp at hlen
            | nil =>
              have hv₁ := ih (e₁, v₁) (by simp [List.zip_cons_cons]) Γ
                (Ty.listT τel) hρ h1
              have hv₂ := ih (e₂, v₂) (by simp [List.zip_cons_cons]) Γ
                (Ty.listT τel) hρ h2
              exact primEval_typed_append hwfD hL hv₁ hv₂ hprim
    | primSplits h0 =>
        rename_i e₀ τel
        cases vs with
        | nil => simp at hlen
        | cons v₀ vs' =>
          cases vs' with
          | cons _ _ => simp at hlen
          | nil =>
            have hv₀ := ih (e₀, v₀) (by simp [List.zip_cons_cons]) Γ
              (Ty.listT τel) hρ h0
            exact primEval_typed_splits hwfD hL hv₀ hprim
    | coerceMatcherToSlot hpre _ _ _ =>
        cases hpre with
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case eletE =>
    intro ρ x e₁ e₂ v₁ v hev₁ hev₂ ih₁ ih₂ Γ τ hρ hty
    have hcore : ∀ (τc τ₁' : Ty) (L' : List TyVar),
        HasTy SD SP SF Γ e₁ τ₁' → (∀ a ∈ L', a ∉ ftvCtx Γ) →
        HasTy SD SP SF ((x, ⟨L', τ₁'⟩) :: Γ) e₂ τc → ValueTy SD SP SF v τc := by
      intro τc τ₁' L' h1 hLf h2
      exact ih₂ _ τc
        (envTyped_cons_scheme (hgen hev₁ hρ h1 hLf) hρ) h2
    cases hty with
    | letE h1 hLf h2 => exact hcore _ _ _ h1 hLf h2
    | coerceMatcherToSlot hpre hren how huni =>
        cases hpre with
        | letE h1 hLf h2 => exact ValueTy.slotV (hcore _ _ _ h1 hLf h2) hren how huni
        | coerceTupleMatcher hpre2 =>
            cases hpre2 with
            | letE h1 hLf h2 =>
                exact ValueTy.slotV (valueTy_coerce2 hwfD (hcore _ _ _ h1 hLf h2))
                  hren how huni
    | coerceTupleMatcher hpre =>
        cases hpre with
        | letE h1 hLf h2 => exact valueTy_coerce2 hwfD (hcore _ _ _ h1 hLf h2)
    | coerceSlotTuple hpre =>
        cases hpre with
        | letE h1 hLf h2 => exact valueTy_coerce3 hwfD (hcore _ _ _ h1 hLf h2)
  case esmth =>
    intro ρ Γ τ hρ hty
    cases hty with
    | something => exact ValueTy.something
    | coerceMatcherToSlot hpre hren how huni =>
        cases hpre with
        | something => exact ValueTy.slotV ValueTy.something hren how huni
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case emtch =>
    intro ρ cls Γ τ hρ hty
    cases hty with
    | matcherE hclsty hcons =>
        exact ValueTy.matcherV Γ (envTyped_dom hρ) (envTyped_inst hρ)
          (HasTy.matcherE hclsty hcons)
    | coerceMatcherToSlot hpre hren how huni =>
        cases hpre with
        | matcherE hclsty hcons =>
            exact ValueTy.slotV
              (ValueTy.matcherV Γ (envTyped_dom hρ) (envTyped_inst hρ)
                (HasTy.matcherE hclsty hcons)) hren how huni
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  case emall =>
    intro ρ e_t e_m p body v_t v_m θs vs hev_t hev_m hsearch hlen hall
      ih_t ih_m _ih_search ih_all Γ τ hρ hty
    cases hty with
    | matchAll hty_t hp hty_m hty_body =>
        rename_i τ_t τ_p Δ τ_r
        have hvt := ih_t Γ τ_t hρ hty_t
        have hvm := ih_m Γ (.slot τ_p τ_t) hρ hty_m
        -- 初期状態の整型(oracle)から探索の反復で各解の代入型付けへ
        have hwtinit : WTState SD SP SF Γ ⟨[.atom ⟨p, v_m, v_t⟩], ρ, []⟩ Δ :=
          ⟨hρ, [], substTyped_nil, hinit hp hvm hvt⟩
        have hsubst : ∀ θ ∈ θs, SubstTyped SD SP SF Δ θ := by
          intro θ hθ
          obtain ⟨ρ', hreach⟩ := search_mem_reaches hsearch θ hθ
          exact terminal_subst_typed
            (reaches_preservation (fun {s ss} hst hwt => hb hst hwt) hreach hwtinit)
        refine mkListV_typed hL ?_
        intro x hx
        obtain ⟨θ, hzip⟩ := exists_mem_zip_right hlen hx
        have hθmem := mem_left_of_zip hzip
        have hst := hsubst θ hθmem
        refine ih_all (θ, x) hzip _ τ_r ?_ hty_body
        exact envTyped_append (envTyped_of_substTyped hst)
          (bindings_cover hst.2) hρ
    | coerceMatcherToSlot hpre _ _ _ =>
        cases hpre with
        | coerceTupleMatcher hpre2 => cases hpre2
    | coerceTupleMatcher hpre => cases hpre
    | coerceSlotTuple hpre => cases hpre
  all_goals intros; trivial

/-! ## Theorem 5.6(b) へ向けた規則別保存補題 -/

/-- MS-MNODE-DONE の保存:空の内側スタックを畳む(**証明済み**)。
    接尾辞前提から rem = [] が従い、q-premise の PatTys nil で Δ が素通しになる。 -/
theorem preserve_mnodeDone {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {S : List Tree} {ρf : Env} {θf : Subst} {piE : PiEnv}
    {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTState SD SP SF Γ ⟨.mnode [] ρf θf piE :: S, ρ, θ⟩ Δgoal) :
    WTState SD SP SF Γ ⟨S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | mnode rem duals Γf Δθf Δfin hj hocc hq hd1 hd2 hθf hinner =>
      have hrem : rem = [] := by
        cases rem with
        | nil => rfl
        | cons pr rem' => exact nomatch hocc
      subst hrem
      cases hq
      exact ⟨hρ, Δ₀, hθ, hrest⟩

/-- **Theorem 5.6(b) (マッチング状態保存)**。
    s → [s₁, …, s_l] かつ ⊢ s : Δ_goal ok ならば各 sᵢ について ⊢ sᵢ : Δ_goal ok。
    未機械化(README ロードマップ [b-3] HM 代入補題・[b-4] vp-scoped の
    threaded 伝播・[b-5] 結合帰納)。 -/
theorem type_safety_b
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {ss : List MState} {Δgoal : BindCtx}
    (hSigF : SigFWF SD SP SF Γ)
    (hstep : Step SF s ss)
    (hwt : WTState SD SP SF Γ s Δgoal) :
    ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal := by
  sorry

end TypePM
