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

/-! ## ~x 出現列の保存(WT-MNODE 接尾辞不変量の維持層)

内側スタックの 1 ステップが `stackEmbedOccs` を変えないことを、
PPM 抽出 → MAtom 規則 → Step 規則の 3 層で示す。
or 分岐だけは出現を落としうるので、線形性側条件 `noEmbedInOr`
(or の両分枝は embed を含まない;PATFUN-DEF の側条件)が効く。 -/

theorem stackEmbedOccs_append : ∀ (S₁ S₂ : List Tree),
    stackEmbedOccs (S₁ ++ S₂) = stackEmbedOccs S₁ ++ stackEmbedOccs S₂
  | [], _ => rfl
  | t :: S₁, S₂ => by
      simp [stackEmbedOccs, stackEmbedOccs_append S₁ S₂]

theorem embedVarsList_append : ∀ (l₁ l₂ : List Pattern),
    embedVarsList (l₁ ++ l₂) = embedVarsList l₁ ++ embedVarsList l₂
  | [], _ => rfl
  | p :: l₁, l₂ => by
      simp [embedVarsList, embedVarsList_append l₁ l₂]

theorem stackEmbedOccs_atoms : ∀ (as : List Atom),
    stackEmbedOccs (as.map .atom) = embedVarsList (as.map (·.p))
  | [] => rfl
  | a :: as => by
      simp [stackEmbedOccs, treeEmbedOccs, embedVarsList, stackEmbedOccs_atoms as]

/-- 3 重 zip で作った原子列のパターン成分は元のパターン列 -/
theorem zip3_atoms_ps : ∀ (ps : List Pattern) (ms vs : List Value),
    ps.length = ms.length → ms.length = vs.length →
    (((ps.zip (ms.zip vs)).map fun x => (⟨x.1, x.2.1, x.2.2⟩ : Atom)).map (·.p)) = ps
  | [], _, _, _, _ => by simp
  | p :: ps, [], _, h1, _ => by simp at h1
  | p :: ps, m :: ms, [], _, h2 => by simp at h2
  | p :: ps, m :: ms, v :: vs, h1, h2 => by
      simp [List.zip_cons_cons,
        zip3_atoms_ps ps ms vs (by simpa using h1) (by simpa using h2)]

theorem decodeTuple_length : ∀ {k : Nat} {v : Value} {l : List Value},
    decodeTuple k v = some l → l.length = k := by
  intro k v l h
  unfold decodeTuple at h
  split at h
  · next hk =>
      obtain rfl := Option.some.inj h.symm
      simpa using (by simpa using hk : k = 1).symm
  · split at h
    · next vs =>
        split at h
        · next hlen =>
            obtain rfl := Option.some.inj h
            simpa using hlen
        · exact nomatch h
    · exact nomatch h

theorem mapM_mem_inv {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h => by
      obtain rfl := Option.some.inj (h : some [] = some l')
      intro b hb
      cases hb
  | a :: l, l', h => by
      rw [List.mapM_cons] at h
      obtain ⟨b, hb, h⟩ := bind_eq_some h
      obtain ⟨l'', hl'', h⟩ := bind_eq_some h
      obtain rfl := pure_eq_some h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨a, by simp, hb⟩
      · obtain ⟨a', ha', hfa'⟩ := mapM_mem_inv hl'' c hc
        exact ⟨a', List.mem_cons_of_mem _ ha', hfa'⟩

/-! PPM 抽出は ~x の出現列を保存する(pp の構造帰納) -/
mutual
theorem ppm_occs {SF : SigF} :
    ∀ (pp : PPat) {ρ : Env} {p : Pattern} {ps' : List Pattern} {ρp : Env},
    PPM SF ρ pp p (some (ps', ρp)) → embedVarsList ps' = p.embedVars
  | .hole, _, p, _, _, hm => by
      cases hm
      simp [embedVarsList]
  | .wild, _, _, _, _, hm => by cases hm; rfl
  | .pval y, _, _, _, _, hm => by cases hm; rfl
  | .ctor c pps, _, _, _, _, hm => by
      cases hm with
      | ctor hl1 hl2 hall =>
        simp only [Pattern.embedVars]
        exact ppm_occs_list pps hl1 hl2 hall
  | .tuple pps, _, _, _, _, hm => by
      cases hm with
      | tuple hl1 hl2 hall =>
        simp only [Pattern.embedVars]
        exact ppm_occs_list pps hl1 hl2 hall

theorem ppm_occs_list {SF : SigF} :
    ∀ (pps : List PPat) {ρ : Env} {ps : List Pattern}
      {rs : List (List Pattern × Env)},
    pps.length = ps.length → (pps.zip ps).length = rs.length →
    (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
    embedVarsList ((rs.map (·.1)).flatten) = embedVarsList ps
  | [], _, ps, rs, hl1, hl2, _ => by
      cases ps with
      | cons _ _ => simp at hl1
      | nil =>
        cases rs with
        | cons _ _ => simp at hl2
        | nil => rfl
  | pp :: pps, _, ps, rs, hl1, hl2, hall => by
      cases ps with
      | nil => simp at hl1
      | cons p ps' =>
        cases rs with
        | nil => simp [List.zip_cons_cons] at hl2
        | cons r rs' =>
          obtain ⟨nexts, ρpc⟩ := r
          have hh : PPM SF _ pp p (some (nexts, ρpc)) :=
            hall ((pp, p), (nexts, ρpc)) (by simp [List.zip_cons_cons])
          simp only [List.map_cons, List.flatten_cons]
          rw [embedVarsList_append, ppm_occs pp hh,
              ppm_occs_list pps (by simpa using hl1)
                (by simpa [List.zip_cons_cons] using hl2)
                (fun tr htr => hall tr
                  (by simp [List.zip_cons_cons]; exact .inr htr))]
          rfl
end

/-- MAtom の各継続は消費された原子のパターンの ~x 出現列を保存する
    (or 分岐は `noEmbedInOr` により両分枝とも出現なし)。 -/
theorem matom_occs {SF : SigF} {ρ : Env} {p : Pattern} {m v : Value}
    {conts : List (List Atom)} {θ' : Subst}
    (hma : MAtom SF ρ p m v conts θ') :
    p.noEmbedInOr = true →
    ∀ as ∈ conts, stackEmbedOccs (as.map .atom) = p.embedVars := by
  refine MAtom.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ p _ _ conts _ _ => p.noEmbedInOr = true →
       ∀ as ∈ conts, stackEmbedOccs (as.map .atom) = p.embedVars)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?someWC ?someVar ?someValEq ?someValNeq ?mand ?mor ?mtuple ?mprodSome
    ?mppfail ?mdpfail ?mmatcher
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    hma
  case someWC =>
    intro ρ v _ as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case someVar =>
    intro ρ x v _ as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case someValEq =>
    intro ρ e v ve _hev _hsE _ih _hno as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case someValNeq =>
    intro ρ e v ve _hev _hsE _ih _hno as has
    cases has
  case mand =>
    intro ρ p₁ p₂ m v _ as has
    simp only [List.mem_singleton] at has
    subst has
    simp [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars]
  case mor =>
    intro ρ p₁ p₂ m v hno as has
    simp only [Pattern.noEmbedInOr, Bool.and_eq_true,
      List.isEmpty_iff] at hno
    obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hno
    simp only [List.mem_cons, List.mem_singleton] at has
    rcases has with rfl | rfl | hfalse
    · simp [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars, h1, h2]
    · simp [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars, h1, h2]
    · cases hfalse
  case mtuple =>
    intro ρ ps ms vs hl1 hl2 _ as has
    simp only [List.mem_singleton] at has
    subst has
    rw [stackEmbedOccs_atoms, zip3_atoms_ps ps ms vs hl1 hl2]
    rfl
  case mprodSome =>
    intro ρ p ms v _hprim _ as has
    simp only [List.mem_singleton] at has
    subst has
    simp [stackEmbedOccs, treeEmbedOccs]
  case mppfail =>
    intro ρ ρm p v pp M arms cls conts θ' _hpc _hppm _hma _ihppm ihma
    exact fun hno as has => ihma hno as has
  case mdpfail =>
    intro ρ ρm p v pp M dp N arms cls ps' ρp conts θ'
      _hpc _hppm _hpd _hma _ihppm ihma
    exact fun hno as has => ihma hno as has
  case mmatcher =>
    intro ρ ρm p v pp M dp N arms cls ps' ρp ρd vN tuples vss vM ms
      _hpc hppm _hpd _hevN hlist hvss _hevM hms
      _ihppm _ihevN _ihevM
    intro _ as has
    simp only [List.mem_map] at has
    obtain ⟨vs, hvs, rfl⟩ := has
    have hlms : ms.length = ps'.length := decodeTuple_length hms
    have hlvs : vs.length = ps'.length := by
      obtain ⟨t, _, hdec⟩ := mapM_mem_inv hvss vs hvs
      exact decodeTuple_length hdec
    rw [stackEmbedOccs_atoms,
        zip3_atoms_ps ps' ms vs hlms.symm (by omega)]
    exact ppm_occs pp hppm
  all_goals intros; trivial

/-! ### noEmbedInOr の維持と Step 水準の出現列保存 -/

theorem noEmbedInOrList_mem : ∀ {ps : List Pattern}, noEmbedInOrList ps = true →
    ∀ p ∈ ps, p.noEmbedInOr = true := by
  intro ps h p hp
  induction ps with
  | nil => cases hp
  | cons q ps ih =>
      simp only [noEmbedInOrList, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact ih h.2 hp

theorem noEmbedInOrList_of_forall : ∀ {ps : List Pattern},
    (∀ p ∈ ps, p.noEmbedInOr = true) → noEmbedInOrList ps = true
  | [], _ => rfl
  | p :: ps, h => by
      simp only [noEmbedInOrList, Bool.and_eq_true]
      exact ⟨h p (by simp), noEmbedInOrList_of_forall
        (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

theorem stackNoOr_append : ∀ (S₁ S₂ : List Tree),
    stackNoOr (S₁ ++ S₂) = (stackNoOr S₁ && stackNoOr S₂)
  | [], S₂ => by simp [stackNoOr]
  | t :: S₁, S₂ => by
      simp [stackNoOr, stackNoOr_append S₁ S₂, Bool.and_assoc]

theorem stackNoOr_atoms : ∀ (as : List Atom),
    stackNoOr (as.map .atom) = noEmbedInOrList (as.map (·.p))
  | [] => rfl
  | a :: as => by
      simp [stackNoOr, treeNoOr, noEmbedInOrList, stackNoOr_atoms as]

/-! PPM 抽出は noEmbedInOr を保存する(部分パターン閉性) -/
mutual
theorem ppm_noOr {SF : SigF} :
    ∀ (pp : PPat) {ρ : Env} {p : Pattern} {ps' : List Pattern} {ρp : Env},
    PPM SF ρ pp p (some (ps', ρp)) → p.noEmbedInOr = true →
    ∀ q ∈ ps', q.noEmbedInOr = true
  | .hole, _, p, _, _, hm, hno => by
      cases hm
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact hno
  | .wild, _, _, _, _, hm, _ => by
      cases hm
      intro q hq
      cases hq
  | .pval y, _, _, _, _, hm, _ => by
      cases hm
      intro q hq
      cases hq
  | .ctor c pps, _, _, _, _, hm, hno => by
      cases hm with
      | ctor hl1 hl2 hall =>
        simp only [Pattern.noEmbedInOr] at hno
        exact ppm_noOr_list pps hl1 hl2 hall hno
  | .tuple pps, _, _, _, _, hm, hno => by
      cases hm with
      | tuple hl1 hl2 hall =>
        simp only [Pattern.noEmbedInOr] at hno
        exact ppm_noOr_list pps hl1 hl2 hall hno

theorem ppm_noOr_list {SF : SigF} :
    ∀ (pps : List PPat) {ρ : Env} {ps : List Pattern}
      {rs : List (List Pattern × Env)},
    pps.length = ps.length → (pps.zip ps).length = rs.length →
    (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
    noEmbedInOrList ps = true →
    ∀ q ∈ (rs.map (·.1)).flatten, q.noEmbedInOr = true
  | [], _, ps, rs, hl1, hl2, _, _ => by
      cases ps with
      | cons _ _ => simp at hl1
      | nil =>
        cases rs with
        | cons _ _ => simp at hl2
        | nil => intro q hq; simp at hq
  | pp :: pps, _, ps, rs, hl1, hl2, hall, hno => by
      cases ps with
      | nil => simp at hl1
      | cons p ps' =>
        cases rs with
        | nil => simp [List.zip_cons_cons] at hl2
        | cons r rs' =>
          obtain ⟨nexts, ρpc⟩ := r
          have hh : PPM SF _ pp p (some (nexts, ρpc)) :=
            hall ((pp, p), (nexts, ρpc)) (by simp [List.zip_cons_cons])
          simp only [noEmbedInOrList, Bool.and_eq_true] at hno
          intro q hq
          simp only [List.map_cons, List.flatten_cons, List.mem_append] at hq
          rcases hq with hq | hq
          · exact ppm_noOr pp hh hno.1 q hq
          · exact ppm_noOr_list pps (by simpa using hl1)
              (by simpa [List.zip_cons_cons] using hl2)
              (fun tr htr => hall tr
                (by simp [List.zip_cons_cons]; exact .inr htr)) hno.2 q hq
end

/-- MAtom の各継続のパターンは noEmbedInOr を保つ -/
theorem matom_noOr {SF : SigF} {ρ : Env} {p : Pattern} {m v : Value}
    {conts : List (List Atom)} {θ' : Subst}
    (hma : MAtom SF ρ p m v conts θ') :
    p.noEmbedInOr = true →
    ∀ as ∈ conts, noEmbedInOrList (as.map (·.p)) = true := by
  refine MAtom.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ p _ _ conts _ _ => p.noEmbedInOr = true →
       ∀ as ∈ conts, noEmbedInOrList (as.map (·.p)) = true)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?nWC ?nVar ?nValEq ?nValNeq ?nand ?nor ?ntuple ?nprodSome
    ?nppfail ?ndpfail ?nmatcher
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    hma
  case nWC =>
    intro ρ v _ as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case nVar =>
    intro ρ x v _ as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case nValEq =>
    intro ρ e v ve _hev _hsE _ih _hno as has
    simp only [List.mem_singleton] at has
    subst has
    rfl
  case nValNeq =>
    intro ρ e v ve _hev _hsE _ih _hno as has
    cases has
  case nand =>
    intro ρ p₁ p₂ m v hno as has
    simp only [List.mem_singleton] at has
    subst has
    simp only [Pattern.noEmbedInOr, Bool.and_eq_true] at hno
    simp [noEmbedInOrList, hno.1, hno.2]
  case nor =>
    intro ρ p₁ p₂ m v hno as has
    simp only [Pattern.noEmbedInOr, Bool.and_eq_true] at hno
    obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := hno
    simp only [List.mem_cons] at has
    rcases has with rfl | rfl | hfalse
    · simp [noEmbedInOrList, h3]
    · simp [noEmbedInOrList, h4]
    · cases hfalse
  case ntuple =>
    intro ρ ps ms vs hl1 hl2 hno as has
    simp only [List.mem_singleton] at has
    subst has
    rw [zip3_atoms_ps ps ms vs hl1 hl2]
    simpa [Pattern.noEmbedInOr] using hno
  case nprodSome =>
    intro ρ p ms v _hprim hno as has
    simp only [List.mem_singleton] at has
    subst has
    simp [noEmbedInOrList, hno]
  case nppfail =>
    intro ρ ρm p v pp M arms cls conts θ' _hpc _hppm _hma _ihppm ihma
    exact fun hno as has => ihma hno as has
  case ndpfail =>
    intro ρ ρm p v pp M dp N arms cls ps' ρp conts θ'
      _hpc _hppm _hpd _hma _ihppm ihma
    exact fun hno as has => ihma hno as has
  case nmatcher =>
    intro ρ ρm p v pp M dp N arms cls ps' ρp ρd vN tuples vss vM ms
      _hpc hppm _hpd _hevN _hlist hvss _hevM hms
      _ihppm _ihevN _ihevM
    intro hno as has
    simp only [List.mem_map] at has
    obtain ⟨vs, hvs, rfl⟩ := has
    have hlms : ms.length = ps'.length := decodeTuple_length hms
    have hlvs : vs.length = ps'.length := by
      obtain ⟨t, _, hdec⟩ := mapM_mem_inv hvss vs hvs
      exact decodeTuple_length hdec
    rw [zip3_atoms_ps ps' ms vs hlms.symm (by omega)]
    exact noEmbedInOrList_of_forall (ppm_noOr pp hppm hno)
  all_goals intros; trivial

/-! ### Π の解決の整列(パターン関数展開時の出現列計算) -/

theorem zip_map_fst : ∀ (l₁ : List String) (l₂ : List Pattern),
    l₁.length = l₂.length → (l₁.zip l₂).map (·.1) = l₁
  | [], _, _ => by simp
  | y :: l₁, [], h => by simp at h
  | y :: l₁, q :: l₂, h => by
      simp [List.zip_cons_cons, zip_map_fst l₁ l₂ (by simpa using h)]

theorem zip_map_snd : ∀ (l₁ : List String) (l₂ : List Pattern),
    l₁.length = l₂.length → (l₁.zip l₂).map (·.2) = l₂
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | y :: l₁, [], h => by simp at h
  | y :: l₁, q :: l₂, h => by
      simp [List.zip_cons_cons, zip_map_snd l₁ l₂ (by simpa using h)]

theorem zip_find_self : ∀ (params : List String) (qs : List Pattern),
    params.Nodup → params.length = qs.length →
    ∀ pr ∈ params.zip qs,
      List.find? (fun x => x.1 == pr.1) (params.zip qs) = some pr
  | [], _, _, _ => by intro pr hpr; simp at hpr
  | y :: params, qs, hnd, hlen => by
      cases qs with
      | nil => simp at hlen
      | cons q qs =>
        intro pr hpr
        obtain ⟨hy, hnd'⟩ := List.nodup_cons.mp hnd
        simp only [List.zip_cons_cons, List.mem_cons] at hpr
        rcases hpr with rfl | hpr
        · simp [List.find?]
        · have hpr1 : pr.1 ∈ params := (List.of_mem_zip hpr).1
          have hne : (y == pr.1) = false := by
            simp only [beq_eq_false_iff_ne]
            exact fun e => hy (e ▸ hpr1)
          simp only [List.zip_cons_cons, List.find?]
          rw [show ((y, q).1 == pr.1) = false from hne]
          exact zip_find_self params qs hnd' (by simpa using hlen) pr hpr

theorem flatMap_resolve_pointwise :
    ∀ (prs : List (String × Pattern)) (piE : PiEnv),
    (∀ pr ∈ prs, List.find? (fun x => x.1 == pr.1) piE = some pr) →
    ((prs.map (·.1)).flatMap fun y =>
      match List.find? (fun x => x.1 == y) piE with
      | some (_, q) => q.embedVars
      | none => [y]) = embedVarsList (prs.map (·.2))
  | [], _, _ => rfl
  | pr :: prs, piE, h => by
      obtain ⟨y, q⟩ := pr
      simp only [List.map_cons, List.flatMap_cons]
      rw [h (y, q) (by simp)]
      simp only [embedVarsList]
      rw [flatMap_resolve_pointwise prs piE
        (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **Step は ~x の出現列と noEmbedInOr を保存する**(接尾辞不変量の維持;
    or 分岐は noEmbedInOr、パターン関数展開は linearity+仮引数相異で整列)。 -/
theorem step_occs {SF : SigF}
    (hSF : ∀ pr ∈ SF, pr.2.body.embedVars = pr.2.params ∧
       pr.2.body.noEmbedInOr = true ∧ pr.2.params.Nodup)
    {s : MState} {ss : List MState} (hstep : Step SF s ss) :
    stackNoOr s.S = true →
    ∀ s' ∈ ss, stackEmbedOccs s'.S = stackEmbedOccs s.S ∧
      stackNoOr s'.S = true := by
  refine Step.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun s ss _ => stackNoOr s.S = true →
       ∀ s' ∈ ss, stackEmbedOccs s'.S = stackEmbedOccs s.S ∧
         stackNoOr s'.S = true)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?sreduce ?spatfun ?smstep ?smvarpat ?smdone
    ?_ ?_
    hstep
  case sreduce =>
    intro S ρ θ p m v conts θ' hma _ihma hno s' hs'
    simp only [List.mem_map] at hs'
    obtain ⟨as, has, rfl⟩ := hs'
    simp only [stackNoOr, treeNoOr, Bool.and_eq_true] at hno
    obtain ⟨hp, hS⟩ := hno
    constructor
    · show stackEmbedOccs (as.map .atom ++ S) = _
      rw [stackEmbedOccs_append, stackEmbedOccs_atoms]
      have h := matom_occs hma hp as has
      rw [stackEmbedOccs_atoms] at h
      rw [h]
      simp [stackEmbedOccs, treeEmbedOccs]
    · show stackNoOr (as.map .atom ++ S) = true
      rw [stackNoOr_append, stackNoOr_atoms, matom_noOr hma hp as has, hS]
      rfl
  case spatfun =>
    intro S ρ θ f qs m v sig hfind hlen hno s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    simp only [stackNoOr, treeNoOr, Pattern.noEmbedInOr,
      Bool.and_eq_true] at hno
    obtain ⟨hqs, hS⟩ := hno
    obtain ⟨hlin0, hbno0, hnd0⟩ := hSF _ (List.mem_of_find?_eq_some hfind)
    have hlin : sig.body.embedVars = sig.params := hlin0
    have hbno : sig.body.noEmbedInOr = true := hbno0
    have hnd : sig.params.Nodup := hnd0
    have hself := zip_find_self sig.params qs hnd hlen
    constructor
    · simp only [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars,
        List.append_nil]
      congr 1
      have hfst := zip_map_fst sig.params qs hlen
      have hsnd := zip_map_snd sig.params qs hlen
      rw [hlin]
      calc sig.params.flatMap _
          = ((sig.params.zip qs).map (·.1)).flatMap _ := by rw [hfst]; rfl
        _ = embedVarsList ((sig.params.zip qs).map (·.2)) :=
            flatMap_resolve_pointwise _ _ hself
        _ = embedVarsList qs := by rw [hsnd]
    · simp only [stackNoOr, treeNoOr, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, hS⟩
      · simp [hbno]
      · rw [List.all_eq_true]
        intro pr hpr
        exact noEmbedInOrList_mem hqs _ (List.of_mem_zip hpr).2
  case smstep =>
    intro S ρ θ t Srest ρf θf piE ss hcond hstep' ih hno s' hs'
    simp only [List.mem_map] at hs'
    obtain ⟨s'', hs'', rfl⟩ := hs'
    simp only [stackNoOr, treeNoOr, Bool.and_eq_true] at hno
    obtain ⟨⟨hin, hpiE⟩, hS⟩ := hno
    have hin' : stackNoOr (({ S := t :: Srest, ρ := ρf, θ := θf } : MState)).S
        = true := by
      simp only [stackNoOr, Bool.and_eq_true]
      exact hin
    obtain ⟨hocc'', hno''⟩ := ih hin' s'' hs''
    constructor
    · simp only [stackEmbedOccs, treeEmbedOccs]
      rw [show stackEmbedOccs s''.S = stackEmbedOccs (t :: Srest) from hocc'']
      rfl
    · simp only [stackNoOr, treeNoOr, Bool.and_eq_true]
      exact ⟨⟨hno'', hpiE⟩, hS⟩
  case smvarpat =>
    intro S ρ θ y q m v Srest ρf θf piE hfind hno s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    simp only [stackNoOr, treeNoOr, Bool.and_eq_true] at hno
    obtain ⟨⟨hin, hpiE⟩, hS⟩ := hno
    constructor
    · simp only [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars,
        List.singleton_append, List.flatMap_cons, hfind, List.append_assoc]
    · simp only [stackNoOr, treeNoOr, Bool.and_eq_true]
      have hq : q.noEmbedInOr = true := by
        have hmem := List.mem_of_find?_eq_some hfind
        have := List.all_eq_true.mp hpiE _ hmem
        simpa using this
      exact ⟨hq, ⟨hin.2, hpiE⟩, hS⟩
      -- ↑ hin の分解形は build で確定させる
  case smdone =>
    intro S ρ θ ρf θf piE hno s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    simp only [stackNoOr, treeNoOr, Bool.and_eq_true] at hno
    exact ⟨by simp [stackEmbedOccs, treeEmbedOccs], hno.2⟩
  all_goals intros; trivial

/-! ## Theorem 5.6(b) へ向けた規則別保存補題 -/

/-- WTStack の連結(Δ スレッディングを継ぐ) -/
theorem wtStack_append {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} : ∀ {S₁ : List Tree} {Δ₀ Δ₁ Δ₂ : BindCtx} {S₂ : List Tree},
    WTStack SD SP SF Γ Φ Δ₀ S₁ Δ₁ → WTStack SD SP SF Γ Φ Δ₁ S₂ Δ₂ →
    WTStack SD SP SF Γ Φ Δ₀ (S₁ ++ S₂) Δ₂
  | [], _, _, _, _, h₁, h₂ => by cases h₁; simpa using h₂
  | t :: S₁, _, _, _, _, h₁, h₂ => by
      cases h₁ with
      | cons ht hS => exact WTStack.cons ht (wtStack_append hS h₂)

/-! ### fresh 変数の具体的供給(再建で something の添字などに使う) -/

def freshFor (τ : Ty) : TyVar := τ.ftv.foldr max 0 + 1

theorem foldr_max_ge : ∀ (l : List TyVar) {a : TyVar}, a ∈ l → a ≤ l.foldr max 0
  | b :: l, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (foldr_max_ge l h) (Nat.le_max_right _ _)

theorem freshFor_not_mem (τ : Ty) : freshFor τ ∉ τ.ftv := by
  intro h
  have h2 := foldr_max_ge _ h
  have h3 : τ.ftv.foldr max 0 + 1 ≤ τ.ftv.foldr max 0 := by
    simpa [freshFor] using h2
  exact Nat.not_succ_le_self _ h3

theorem applyTS_single_not_mem {τ σ : Ty} {a : TyVar} (h : a ∉ τ.ftv) :
    τ.applyTS [(a, σ)] = τ := by
  have hcong := applyTS_congr τ (θ := [(a, σ)]) (θ' := []) ?_
  · rw [hcong, applyTS_nil]
  · intro b hb
    have hba : (a == b) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun e => h (e ▸ hb)
    simp [TySubst.appVar, List.find?, hba]

/-- fresh 変数と任意の型は単一化可能 -/
theorem unifiable_var_fresh (τ : Ty) : Unifiable (.var (freshFor τ)) τ := by
  refine ⟨[(freshFor τ, τ)], ?_⟩
  show TySubst.appVar _ _ = τ.applyTS _
  rw [applyTS_single_not_mem (freshFor_not_mem τ)]
  simp [TySubst.appVar, List.find?]

/-- 変数はそれ自身への改名を持つ -/
theorem renamesTo_var_refl (a : TyVar) : RenamesTo (.var a) (.var a) :=
  ⟨id, fun _ _ h => h, by simp [Ty.applyRen]⟩

/-- 変数は自分自身の one-way instance(空代入) -/
theorem oneWay_var_refl (a : TyVar) : OneWay (.var a) (.var a) := by
  refine ⟨[], ?_, applyTS_nil _⟩
  intro b hb
  simp [TySubst.dom] at hb

/-! ### MS-REDUCE の易ケース群(継続の再建が文脈素通し・単一束縛のもの) -/

/-- MS-SOME-WC の保存 -/
theorem preserve_someWC {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {v : Value} {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.wild, .something, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc hp hm hren how htm hok hv hvp =>
        cases hp
        exact ⟨hρ, Δ₀, hθ, hrest⟩

/-- MS-SOME-VAL-EQ の保存(値パターン成功;NEQ は継続が空なので義務なし) -/
theorem preserve_someValEq {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {e : Expr} {v : Value} {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.pval e, .something, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc hp hm hren how htm hok hv hvp =>
        cases hp
        exact ⟨hρ, Δ₀, hθ, hrest⟩

/-- MS-SOME-VAR の保存:束縛 x ↦ v の追加。WT-ATOM の値型が τt に
    固定されているので、束縛の型付けが宣言型と直接一致する。 -/
theorem preserve_someVar {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {x : String} {v : Value} {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.pvar x, .something, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨S, ρ, (x, v) :: θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc hp hm hren how htm hok hv hvp =>
        cases hp with
        | pvar hx =>
          refine ⟨hρ, _, ⟨?_, ?_⟩, hrest⟩
          · simp only [List.map_append, List.map_cons, List.map_nil,
              List.reverse_cons, hθ.1]
          · intro pr hpr
            rcases List.mem_append.mp hpr with hpr | hpr
            · obtain ⟨w, hfind, hty⟩ := hθ.2 pr hpr
              refine ⟨w, ?_, hty⟩
              simp only [Env.find?, List.find?]
              have hxne : (x == pr.1) = false := by
                simp only [beq_eq_false_iff_ne]
                exact fun h => hx pr hpr h.symm
              rw [hxne]
              simpa [Env.find?] using hfind
            · simp only [List.mem_singleton] at hpr
              subst hpr
              exact ⟨v, by simp [Env.find?, List.find?], hv⟩

/-- MS-PROD-SOME の保存:素形パターンの積マッチャー原子は something 原子へ。
    パターンの構造添字と something の添字を同じ fresh 変数に取り直す。 -/
theorem preserve_prodSome {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {p : Pattern} {ms : List Value} {v : Value}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hprim : p.isPrimForm = true)
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p, .tuple ms, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p, .something, v⟩ :: S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc hp hm hren how htm hok hv hvp =>
        rename_i τp τt τm τm'
        cases p with
        | pvar x =>
            cases hp with
            | pvar hx =>
              refine ⟨hρ, Δ₀, hθ, WTStack.cons
                (WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
                  rfl (PatTy.pvar (τp := .var (freshFor _)) hx) ValueTy.something
                  (renamesTo_var_refl _) (oneWay_var_refl _)
                  (unifiable_var_fresh _) MatcherOK.something ?_ trivial) hrest⟩
              exact hv
        | wild =>
            cases hp
            exact ⟨hρ, Δ₀, hθ, WTStack.cons
              (WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
                rfl (PatTy.wild (τp := .var (freshFor _))) ValueTy.something
                (renamesTo_var_refl _) (oneWay_var_refl _)
                (unifiable_var_fresh _) MatcherOK.something hv trivial) hrest⟩
        | pval e =>
            cases hp with
            | pval hty =>
              exact ⟨hρ, Δ₀, hθ, WTStack.cons
                (WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
                  rfl (PatTy.pval (τp := .var (freshFor _)) hty) ValueTy.something
                  (renamesTo_var_refl _) (oneWay_var_refl _)
                  (unifiable_var_fresh _) MatcherOK.something hv trivial) hrest⟩
        | pctor c ps => simp [Pattern.isPrimForm] at hprim
        | ptuple ps => simp [Pattern.isPrimForm] at hprim
        | pand p₁ p₂ => simp [Pattern.isPrimForm] at hprim
        | por p₁ p₂ => simp [Pattern.isPrimForm] at hprim
        | papp f qs => simp [Pattern.isPrimForm] at hprim
        | embed y => simp [Pattern.isPrimForm] at hprim
    | atomAnd h₁ h₂ => simp [Pattern.isPrimForm] at hprim
    | atomOr h₁ h₂ => simp [Pattern.isPrimForm] at hprim
    | atomTuple hlen1 hlen2 hcomp => simp [Pattern.isPrimForm] at hprim

/-- MS-TUPLE の保存(WT-ATOM-TUPLE 型付けの原子):継続はちょうど成分原子列。 -/
theorem preserve_tuple {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {ps : List Pattern} {ms vs : List Value}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ
      ⟨.atom ⟨.ptuple ps, .tuple ms, .tuple vs⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ
      ⟨((ps.zip (ms.zip vs)).map fun x => .atom ⟨x.1, x.2.1, x.2.2⟩) ++ S, ρ, θ⟩
      Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc _ _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomTuple hlen1 hlen2 hcomp =>
        exact ⟨hρ, Δ₀, hθ, wtStack_append hcomp hrest⟩

/-- MS-MNODE-DONE の保存:空の内側スタックを畳む(**証明済み**)。
    接尾辞前提から rem = [] が従い、q-premise の PatTys nil で Δ が素通しになる。 -/
theorem preserve_mnodeDone {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {S : List Tree} {ρf : Env} {θf : Subst} {piE : PiEnv}
    {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.mnode [] ρf θf piE :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨S, ρ, θ⟩ Δgoal := by
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

/-- MS-AND の保存(WT-ATOM-AND):継続はちょうど 2 つの成分原子。 -/
theorem preserve_and {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {p₁ p₂ : Pattern} {m v : Value}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.pand p₁ p₂, m, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p₁, m, v⟩ :: .atom ⟨p₂, m, v⟩ :: S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc _ _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomAnd h₁ h₂ =>
        exact ⟨hρ, Δ₀, hθ, WTStack.cons h₁ (WTStack.cons h₂ hrest)⟩

/-- MS-OR の保存(左分枝) -/
theorem preserve_or_left {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {p₁ p₂ : Pattern} {m v : Value}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.por p₁ p₂, m, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p₁, m, v⟩ :: S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc _ _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomOr h₁ h₂ => exact ⟨hρ, Δ₀, hθ, WTStack.cons h₁ hrest⟩

/-- MS-OR の保存(右分枝) -/
theorem preserve_or_right {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {p₁ p₂ : Pattern} {m v : Value}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.por p₁ p₂, m, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p₂, m, v⟩ :: S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atom hsc _ _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomOr h₁ h₂ => exact ⟨hρ, Δ₀, hθ, WTStack.cons h₂ hrest⟩

/-- Theorem 5.6(b) の Φ 一般化形。Step の結合再帰子(motive_4)で帰納し、
    MS-MNODE-STEP の内側再帰に帰納法の仮定を供給する。
    仮定 `hSF` は PATFUN-DEF の意味論側条件(線形性・noEmbedInOr・仮引数相異)、
    `stackNoOr` は or 分岐が ~x を落とさないための状態不変量
    (site パターンは embed-free、本体は noOr なので到達状態で成立;
    維持は `step_occs` が同時に示す)。
    **14 分岐のうち 10(MS-SOME-WC/VAR/VAL-EQ/VAL-NEQ・MS-AND・MS-OR・
    MS-TUPLE・MS-PROD-SOME・MS-MNODE-DONE・MS-MNODE-STEP)は証明済み**。
    残る sorry は MS-MATCHER 系 3([b-4] 後続 vp transport+[b-5.5]
    役割別 τt 取り直し)と MS-PATFUN-ENTER / MS-MNODE-VARPAT
    ([b-3] 双対スキームのインスタンス化)。 -/
theorem type_safety_b_at
    {SD : SigD} {SP : SigP} {SF : SigF}
    (hSF : ∀ pr ∈ SF, pr.2.body.embedVars = pr.2.params ∧
       pr.2.body.noEmbedInOr = true ∧ pr.2.params.Nodup)
    {s : MState} {ss : List MState}
    (hstep : Step SF s ss) :
    ∀ (Γ : TyCtx) (Φ : PatParamCtx) (Δgoal : BindCtx),
      stackNoOr s.S = true →
      WTStateAt SD SP SF Γ Φ s Δgoal →
      ∀ s' ∈ ss, WTStateAt SD SP SF Γ Φ s' Δgoal := by
  refine Step.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun s ss _ =>
      ∀ (Γ : TyCtx) (Φ : PatParamCtx) (Δgoal : BindCtx),
        stackNoOr s.S = true →
        WTStateAt SD SP SF Γ Φ s Δgoal →
        ∀ s' ∈ ss, WTStateAt SD SP SF Γ Φ s' Δgoal)
    (motive_5 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?reduce ?patfun ?mstep ?mvarpat ?mdone
    ?_ ?_
    hstep
  case reduce =>
    intro S ρ θ p m v conts θ' hma _ihma
    intro Γ Φ Δgoal _hno hwt s' hs'
    simp only [List.mem_map] at hs'
    obtain ⟨as, has, rfl⟩ := hs'
    cases hma with
    | someWC =>
        simp only [List.mem_singleton] at has
        subst has
        simpa using preserve_someWC hwt
    | someVar =>
        simp only [List.mem_singleton] at has
        subst has
        simpa using preserve_someVar hwt
    | someValEq hev hsE =>
        simp only [List.mem_singleton] at has
        subst has
        simpa using preserve_someValEq hwt
    | someValNeq hev hsE => cases has
    | and =>
        simp only [List.mem_singleton] at has
        subst has
        simpa using preserve_and hwt
    | or =>
        simp only [List.mem_cons] at has
        rcases has with rfl | rfl | h
        · simpa using preserve_or_left hwt
        · simpa using preserve_or_right hwt
        · cases h
    | tuple hl1 hl2 =>
        simp only [List.mem_singleton] at has
        subst has
        have h := preserve_tuple hwt
        simpa [List.map_map, Function.comp_def] using h
    | prodSome hprim =>
        simp only [List.mem_singleton] at has
        subst has
        simpa using preserve_prodSome hprim hwt
    | matcherPPFail hpc hppm hma' => sorry
    | matcherDPFail hpc hppm hpd hma' => sorry
    | matcher hpc hppm hpd hevN hlist hvss hevM hms => sorry
  case patfun =>
    intro S ρ θ f qs m v sig hfind hlen
    intro Γ Φ Δgoal hno hwt s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    sorry
  case mstep =>
    intro S ρ θ t Srest ρf θf piE ss hcond hstep' ih
    intro Γ Φ Δgoal hno hwt s' hs'
    simp only [List.mem_map] at hs'
    obtain ⟨s'', hs'', rfl⟩ := hs'
    obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
    -- 内側スタックの noEmbedInOr(接尾辞不変量の維持に使う)
    simp only [stackNoOr, treeNoOr, Bool.and_eq_true] at hno
    obtain ⟨⟨hnoIn, hnoPi⟩, hnoS⟩ := hno
    cases hstack with
    | cons htree hrest =>
      cases htree with
      | mnode rem duals Γf Δθf Δfin hj hocc hq hd1 hd2 hθf hinner =>
        have hwtIn : WTStateAt SD SP SF Γf ((rem.map (·.1)).zip duals)
            ⟨t :: Srest, ρf, θf⟩ Δfin :=
          ⟨envTyped_of_parts hd1 hd2, Δθf, hθf, hinner⟩
        have hnoIn' : stackNoOr (({ S := t :: Srest, ρ := ρf, θ := θf } :
            MState)).S = true := by
          simp only [stackNoOr, Bool.and_eq_true]
          exact hnoIn
        obtain ⟨_, Δθf', hθf', hinner'⟩ := ih Γf _ Δfin hnoIn' hwtIn s'' hs''
        -- 接尾辞不変量の維持:内側 1 ステップは ~x 出現列を保存する(step_occs)
        obtain ⟨hoccEq, _⟩ := step_occs hSF hstep' hnoIn' s'' hs''
        have hocc' : stackEmbedOccs s''.S = rem.map (·.1) := by
          rw [show stackEmbedOccs s''.S = stackEmbedOccs (t :: Srest) from hoccEq]
          exact hocc
        exact ⟨hρ, Δ₀, hθ,
          WTStack.cons (WTTree.mnode rem duals Γf Δθf' Δfin hj hocc' hq hd1 hd2
            hθf' hinner') hrest⟩
  case mvarpat =>
    intro S ρ θ y q m v Srest ρf θf piE hfind
    intro Γ Φ Δgoal hno hwt s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    sorry
  case mdone =>
    intro S ρ θ ρf θf piE
    intro Γ Φ Δgoal _hno hwt s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    exact preserve_mnodeDone hwt
  all_goals intros; trivial

/-- **Theorem 5.6(b) (マッチング状態保存)**。
    s → [s₁, …, s_l] かつ ⊢ s : Δ_goal ok ならば各 sᵢ について ⊢ sᵢ : Δ_goal ok。
    (`type_safety_b_at` の Φ = [] 特殊化。hSigF は残 sorry 分岐
    (MS-PATFUN-ENTER の双対スキーム実現)で使う予定の interface。) -/
theorem type_safety_b
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {ss : List MState} {Δgoal : BindCtx}
    (hSigF : SigFWF SD SP SF Γ)
    (hstep : Step SF s ss)
    (hno : stackNoOr s.S = true)
    (hwt : WTState SD SP SF Γ s Δgoal) :
    ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal :=
  type_safety_b_at
    (fun pr hpr => ⟨(hSigF pr hpr).linearity, (hSigF pr hpr).noOr,
      (hSigF pr hpr).paramsNodup⟩)
    hstep Γ [] Δgoal hno hwt

end TypePM
