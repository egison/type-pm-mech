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

(b) `type_safety_b` は**全 14 分岐証明済み**(oracle hevG・hclorc・hinstF は
[b-5] 結合帰納法/[b-6] インスタンス輸送で放電;README ロードマップ)。
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

/-! ### 到達状態の stackNoOr 確立(site パターンは Φ = [] で embed-free) -/

mutual
/-- Φ = [] の双対導出は ~x を含まない(PAT-EMBED の find? が空で失敗) -/
theorem patTy_nil_embedFree {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} :
    ∀ (p : Pattern) {Δ Δ' : BindCtx} {τp τt : Ty},
    PatTy SD SP SF Γ [] Δ p τp τt Δ' → p.embedVars = []
  | .pvar x, _, _, _, _, _ => rfl
  | .wild, _, _, _, _, _ => rfl
  | .pval e, _, _, _, _, _ => rfl
  | .embed y, _, _, _, _, h => by
      cases h with
      | embed hf => exact nomatch hf
  | .pctor c ps, _, _, _, _, h => by
      cases h with
      | pctor _ hps _ _ =>
          simpa [Pattern.embedVars] using patTys_nil_embedFree ps hps
  | .pand p₁ p₂, _, _, _, _, h => by
      cases h with
      | pand h₁ h₂ =>
          simp [Pattern.embedVars, patTy_nil_embedFree p₁ h₁,
            patTy_nil_embedFree p₂ h₂]
  | .por p₁ p₂, _, _, _, _, h => by
      cases h with
      | por h₁ h₂ =>
          simp [Pattern.embedVars, patTy_nil_embedFree p₁ h₁,
            patTy_nil_embedFree p₂ h₂]
  | .papp f qs, _, _, _, _, h => by
      cases h with
      | papp _ hqs _ _ =>
          simpa [Pattern.embedVars] using patTys_nil_embedFree qs hqs
  | .ptuple ps, _, _, _, _, h => by
      cases h with
      | ptuple hps =>
          simpa [Pattern.embedVars] using patTys_nil_embedFree ps hps

theorem patTys_nil_embedFree {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} :
    ∀ (ps : List Pattern) {duals : List (Ty × Ty)} {Δ Δ' : BindCtx},
    PatTys SD SP SF Γ [] Δ ps duals Δ' → embedVarsList ps = []
  | [], _, _, _, _ => rfl
  | p :: ps, _, _, _, h => by
      cases h with
      | cons hp hps =>
          simp [embedVarsList, patTy_nil_embedFree p hp,
            patTys_nil_embedFree ps hps]
end

mutual
/-- embed-free なら noEmbedInOr は自明に成立 -/
theorem noEmbedInOr_of_embedFree : ∀ (p : Pattern),
    p.embedVars = [] → p.noEmbedInOr = true
  | .pvar _, _ => rfl
  | .wild, _ => rfl
  | .pval _, _ => rfl
  | .embed _, _ => rfl
  | .pctor c ps, h => by
      simp only [Pattern.embedVars] at h
      simpa [Pattern.noEmbedInOr] using noEmbedInOrList_of_embedFree ps h
  | .pand p₁ p₂, h => by
      simp only [Pattern.embedVars, List.append_eq_nil_iff] at h
      simp [Pattern.noEmbedInOr, noEmbedInOr_of_embedFree p₁ h.1,
        noEmbedInOr_of_embedFree p₂ h.2]
  | .por p₁ p₂, h => by
      simp only [Pattern.embedVars, List.append_eq_nil_iff] at h
      simp [Pattern.noEmbedInOr, h.1, h.2,
        noEmbedInOr_of_embedFree p₁ h.1, noEmbedInOr_of_embedFree p₂ h.2]
  | .papp f qs, h => by
      simp only [Pattern.embedVars] at h
      simpa [Pattern.noEmbedInOr] using noEmbedInOrList_of_embedFree qs h
  | .ptuple ps, h => by
      simp only [Pattern.embedVars] at h
      simpa [Pattern.noEmbedInOr] using noEmbedInOrList_of_embedFree ps h

theorem noEmbedInOrList_of_embedFree : ∀ (ps : List Pattern),
    embedVarsList ps = [] → noEmbedInOrList ps = true
  | [], _ => rfl
  | p :: ps, h => by
      simp only [embedVarsList, List.append_eq_nil_iff] at h
      simp [noEmbedInOrList, noEmbedInOr_of_embedFree p h.1,
        noEmbedInOrList_of_embedFree ps h.2]
end

/-- match site の初期 1 原子スタックは stackNoOr を満たす -/
theorem stackNoOr_init {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {p : Pattern} {m v : Value} {τp τt : Ty} {Δ : BindCtx}
    (hp : PatTy SD SP SF Γ [] [] p τp τt Δ) :
    stackNoOr [.atom ⟨p, m, v⟩] = true := by
  simp [stackNoOr, treeNoOr,
    noEmbedInOr_of_embedFree p (patTy_nil_embedFree p hp)]

/-- (b) の noOr つき反復((a) の EV-MATCHALL で使用;oracle は
    「noOr を保存しつつ WT を保存する」連言形で受け取る) -/
theorem reaches_preservation_noOr {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {Δgoal : BindCtx}
    (hb : ∀ {s ss}, Step SF s ss → stackNoOr s.S = true →
       WTState SD SP SF Γ s Δgoal →
       ∀ s' ∈ ss, stackNoOr s'.S = true ∧ WTState SD SP SF Γ s' Δgoal)
    {s s' : MState}
    (hr : Reaches SF s s') (hno : stackNoOr s.S = true)
    (hwt : WTState SD SP SF Γ s Δgoal) :
    WTState SD SP SF Γ s' Δgoal := by
  induction hr with
  | refl => exact hwt
  | step hstep hmem _ ih =>
      obtain ⟨hno', hwt'⟩ := hb hstep hno hwt _ hmem
      exact ih hno' hwt'

/-- **Theorem 5.6(a) (式評価の型付け)**(**oracle 分解で証明済み**)。
    Γ ⊢ e : τ で ρ が Γ で型付けられ、ρ, e ⇓ v ならば v : τ。
    oracle:`hb` = 5.6(b)、`hgen` = HM 一般化補題(rigidity 制限つき;Stage 2)、
    `hinit` = matchAll 初期状態の整型(vp-scoped + スロット witness 合成)。
    モジュール docstring を参照。 -/
theorem type_safety_a
    {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hL : ListSigOK SD)
    (hb : ∀ {Γ' : TyCtx} {Δ : BindCtx} {s ss}, Step SF s ss →
       stackNoOr s.S = true → WTState SD SP SF Γ' s Δ →
       ∀ s' ∈ ss, stackNoOr s'.S = true ∧ WTState SD SP SF Γ' s' Δ)
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
            (reaches_preservation_noOr (fun {s ss} hst hno hwt => hb hst hno hwt)
              hreach (stackNoOr_init hp) hwtinit)
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

/-- キー相異なら find? はその要素自身を返す -/
theorem find?_eq_of_nodup_keys {α} : ∀ {l : List (String × α)} {y : String} {q : α},
    (l.map (·.1)).Nodup → (y, q) ∈ l →
    List.find? (fun x => x.1 == y) l = some (y, q)
  | [], _, _, _, h => nomatch h
  | (y', q') :: l, y, q, hnd, hmem => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hy', hnd'⟩ := hnd
      rcases List.mem_cons.mp hmem with heq | hmem
      · injection heq with h1 h2
        subst h1
        subst h2
        simp [List.find?]
      · have hymem : y ∈ l.map (·.1) := by
          exact List.mem_map_of_mem hmem
        have hne : (y' == y) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun e => hy' (e ▸ hymem)
        simp only [List.find?]
        rw [show ((y', q').1 == y) = false from hne]
        exact find?_eq_of_nodup_keys hnd' hmem

/-! ### 原子の整型ビルダー(パターン形状で scalar / And / Or / Tuple を選ぶ)

(b) の再建の中核:双対検査の premise 一式から、パターンの形に応じて
適切な WT-ATOM 変種を組み立てる。and/or は子へ、タプル×積マッチャー値は
成分ごとに再帰する(双対検査条件は上の成分分割補題で分配)。 -/

mutual
theorem buildAtom {SD : SigD} {SP : SigP} {SF : SigF} (hwfD : SigDWF SD) :
    ∀ (p : Pattern) {Γ : TyCtx} {Φ : PatParamCtx} {Δ Δ' : BindCtx}
      {m v : Value} {τp τt τm τm' : Ty},
    PatTy SD SP SF Γ Φ Δ p τp τt Δ' →
    ValueTy SD SP SF m (.matcher τm) →
    RenamesTo τm τm' → OneWay τp τm' → StructReaches τp τt → Unifiable τm τt →
    MatcherOK SD SP m → ValueTy SD SP SF v τt →
    WTTree SD SP SF Γ Φ Δ (.atom ⟨p, m, v⟩) Δ'
  | .pand p₁ p₂, _, _, _, _, _, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      cases hp with
      | pand hp₁ hp₂ =>
        exact WTTree.atomAnd
          (buildAtom hwfD p₁ hp₁ hm hren how hreach htm hok hv)
          (buildAtom hwfD p₂ hp₂ hm hren how hreach htm hok hv)
  | .por p₁ p₂, _, _, _, _, _, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      cases hp with
      | por hp₁ hp₂ =>
        exact WTTree.atomOr
          (buildAtom hwfD p₁ hp₁ hm hren how hreach htm hok hv)
          (buildAtom hwfD p₂ hp₂ hm hren how hreach htm hok hv)
  | .ptuple ps, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      cases m with
      | tuple ms =>
          cases hp with
          | ptuple hps =>
            rename_i duals
            obtain ⟨τs, hτm, hlenms, hcomp⟩ := valueTy_tuple_matcher_inv hm
            subst hτm
            obtain ⟨l', hl', hlenl⟩ := renamesTo_prod hren
            subst hl'
            obtain ⟨hlen2, hrencomp⟩ := renamesTo_prod_comp hren
            obtain ⟨hlen3, howcomp⟩ := oneWay_prod_comp how
            have hunicomp := unifiable_prod_comp htm (by
              have := patTys_length hps
              simp only [List.length_map] at hlen3 ⊢
              omega)
            obtain ⟨vs, rfl, hlenv, hvcomp⟩ := canonical_prod hwfD hv
            have hokall : ∀ m' ∈ ms, MatcherOK SD SP m' := by
              cases hok with
              | prod hall => exact hall
            have hreachcomp : ∀ pr ∈ duals, StructReaches pr.1 pr.2 := by
              intro pr hpr
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpr
              have h3 := structReaches_prod hreach
                (i := j) (by simpa using hj) (by simpa using hj)
              simpa [List.getElem_map] using h3
            refine WTTree.atomTuple ?_ ?_ ?_
            · have := patTys_length hps
              simp only [List.length_map] at hlen3
              omega
            · have := patTys_length hps
              simp only [List.length_map] at hlen3 hlenv
              omega
            · exact buildAtoms hwfD ps hps hreachcomp hlenms hcomp hlen2 hrencomp
                (by simpa using hlen3) howcomp hunicomp hokall
                (by simpa using hlenv) hvcomp
                (by have := patTys_length hps
                    simp only [List.length_map] at hlen3
                    omega)
      | matcherV ρm cls =>
          cases hp with
          | ptuple hps =>
            exact WTTree.atom rfl (PatTy.ptuple hps) hm hren how hreach htm hok hv
      | something =>
          cases hp with
          | ptuple hps =>
            exact WTTree.atom rfl (PatTy.ptuple hps) hm hren how hreach htm hok hv
      | lit n =>
          cases hp with
          | ptuple hps =>
            exact WTTree.atom rfl (PatTy.ptuple hps) hm hren how hreach htm hok hv
      | ctor c vs =>
          cases hp with
          | ptuple hps =>
            exact WTTree.atom rfl (PatTy.ptuple hps) hm hren how hreach htm hok hv
      | closure self ρc x e =>
          cases hp with
          | ptuple hps =>
            exact WTTree.atom rfl (PatTy.ptuple hps) hm hren how hreach htm hok hv
  | .pvar x, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv
  | .wild, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv
  | .pval e, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv
  | .pctor c ps, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv
  | .papp f qs, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv
  | .embed y, _, _, _, _, m, _, _, _, _, _, hp, hm, hren, how, hreach, htm, hok, hv => by
      exact WTTree.atom (by cases m <;> rfl) hp hm hren how hreach htm hok hv

theorem buildAtoms {SD : SigD} {SP : SigP} {SF : SigF} (hwfD : SigDWF SD) :
    ∀ (ps : List Pattern) {Γ : TyCtx} {Φ : PatParamCtx} {Δ Δ' : BindCtx}
      {duals : List (Ty × Ty)} {ms : List Value} {τs τs' : List Ty}
      {vs : List Value},
    PatTys SD SP SF Γ Φ Δ ps duals Δ' →
    (∀ pr ∈ duals, StructReaches pr.1 pr.2) →
    ms.length = τs.length →
    (∀ pr ∈ ms.zip τs, ValueTy SD SP SF pr.1 (.matcher pr.2)) →
    τs.length = τs'.length →
    (∀ pr ∈ τs.zip τs', RenamesTo pr.1 pr.2) →
    (duals.map (·.1)).length = τs'.length →
    (∀ pr ∈ (duals.map (·.1)).zip τs', OneWay pr.1 pr.2) →
    (∀ pr ∈ τs.zip (duals.map (·.2)), Unifiable pr.1 pr.2) →
    (∀ m' ∈ ms, MatcherOK SD SP m') →
    vs.length = (duals.map (·.2)).length →
    (∀ pr ∈ vs.zip (duals.map (·.2)), ValueTy SD SP SF pr.1 pr.2) →
    ps.length = ms.length →
    WTStack SD SP SF Γ Φ Δ
      ((ps.zip (ms.zip vs)).map fun x => .atom ⟨x.1, x.2.1, x.2.2⟩) Δ'
  | [], _, _, _, _, _, ms, _, _, vs, hps, _, _, _, _, _, _, _, _, _, _, _, hlp => by
      cases hps
      cases ms with
      | cons _ _ => simp at hlp
      | nil => exact WTStack.nil
  | p :: ps, _, _, _, _, duals, ms, τs, τs', vs, hps, hreaches, hl1, hmall, hl2, hrall,
      hl3, hoall, huall, hokall, hl4, hvall, hlp => by
      cases hps with
      | cons hph hpst =>
        rename_i Δmid pr0 dualst
        cases ms with
        | nil => simp at hlp
        | cons m₀ ms' =>
          cases τs with
          | nil => simp at hl1
          | cons τm₀ τst =>
            cases τs' with
            | nil => simp at hl2
            | cons τm₀' τst' =>
              cases vs with
              | nil => simp at hl4
              | cons v₀ vst =>
                simp only [List.zip_cons_cons, List.map_cons] at *
                refine WTStack.cons
                  (buildAtom hwfD p hph
                    (hmall (m₀, τm₀) (by simp [List.zip_cons_cons]))
                    (hrall (τm₀, τm₀') (by simp [List.zip_cons_cons]))
                    (hoall (pr0.1, τm₀') (by simp [List.zip_cons_cons]))
                    (hreaches pr0 (List.mem_cons_self ..))
                    (huall (τm₀, pr0.2) (by simp [List.zip_cons_cons]))
                    (hokall m₀ (by simp))
                    (hvall (v₀, pr0.2) (by simp [List.zip_cons_cons]))) ?_
                exact buildAtoms hwfD ps hpst
                  (fun q hq => hreaches q (List.mem_cons_of_mem _ hq))
                  (by simpa using hl1)
                  (fun q hq => hmall q (by simp [List.zip_cons_cons]; exact .inr hq))
                  (by simpa using hl2)
                  (fun q hq => hrall q (by simp [List.zip_cons_cons]; exact .inr hq))
                  (by simpa using hl3)
                  (fun q hq => hoall q (by simp [List.zip_cons_cons]; exact .inr hq))
                  (fun q hq => huall q (by simp [List.zip_cons_cons]; exact .inr hq))
                  (fun m' hm' => hokall m' (by simp; exact .inr hm'))
                  (by simpa using hl4)
                  (fun q hq => hvall q (by simp [List.zip_cons_cons]; exact .inr hq))
                  (by simpa using hlp)
end

/-! ### スロット値の万能原子ビルダー(slot_atom)

buildAtom のスロット版:m がスロット型で型付く値でありさえすれば、
パターン形状に応じて WT-ATOM 変種を組む。witness が単一マッチャー
(slotV 反転)なら buildAtom へ(⊑ は到達不変量と slot の ⊑ の
`oneWay_trans` 合成)、積スロット(prodSlot 反転)なら and/or は子へ、
ptuple は成分ごとに再帰、それ以外は WT-ATOM-SLOT でスロットのまま担ぐ。
MS-MATCHER の後続原子再建と MS-MNODE-VARPAT の積スロット原子転送の中核。 -/

/-- スロットの ⊑ をパターン構造添字起点へ:σ が標的の改名なら到達不変量と
    合成(oneWay_trans)、σ = τp(site 由来)なら slot の ⊑ がそのまま -/
theorem slot_left_how {τp τt σ τm'' : Ty}
    (hreach : StructReaches τp τt) (hσ : RenamesTo τt σ ∨ σ = τp)
    (howσ : OneWay σ τm'') : OneWay τp τm'' := by
  rcases hσ with hσr | rfl
  · exact oneWay_trans (hreach σ hσr) howσ
  · exact howσ

mutual
theorem slot_atom {SD : SigD} {SP : SigP} {SF : SigF} (hwfD : SigDWF SD) :
    ∀ (p : Pattern) {Γ : TyCtx} {Φ : PatParamCtx} {Δ Δ' : BindCtx}
      {m v : Value} {τp τt σ : Ty},
    PatTy SD SP SF Γ Φ Δ p τp τt Δ' →
    StructReaches τp τt →
    ValueTy SD SP SF m (.slot σ τt) →
    (RenamesTo τt σ ∨ σ = τp) →
    ValueTy SD SP SF v τt →
    WTTree SD SP SF Γ Φ Δ (.atom ⟨p, m, v⟩) Δ'
  | .pand p₁ p₂, _, _, _, _, _, _, _, _, _, hp, hreach, hslot, hσ, hv => by
      cases hp with
      | pand hp₁ hp₂ =>
        exact WTTree.atomAnd
          (slot_atom hwfD p₁ hp₁ hreach hslot hσ hv)
          (slot_atom hwfD p₂ hp₂ hreach hslot hσ hv)
  | .por p₁ p₂, _, _, _, _, _, _, _, _, _, hp, hreach, hslot, hσ, hv => by
      cases hp with
      | por hp₁ hp₂ =>
        exact WTTree.atomOr
          (slot_atom hwfD p₁ hp₁ hreach hslot hσ hv)
          (slot_atom hwfD p₂ hp₂ hreach hslot hσ hv)
  | .ptuple ps, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ |
        ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD (.ptuple ps) hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · cases hp with
        | ptuple hps =>
          rename_i duals
          have hsnd : duals.map (·.2) = prs.map (·.2) := by
            injection hτp
          obtain ⟨vs, rfl, hlenv, hvcomp⟩ := canonical_prod hwfD hv
          have hlend : duals.length = prs.length := by
            have := congrArg List.length hsnd
            simpa using this
          have hlenp := patTys_length hps
          have hreachcomp : ∀ pr ∈ duals, StructReaches pr.1 pr.2 := by
            intro pr hpr
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpr
            have h3 := structReaches_prod hreach
              (i := j) (by simpa using hj) (by simpa using hj)
            simpa [List.getElem_map] using h3
          have hσcomp : ∀ pr ∈ duals.zip prs,
              RenamesTo pr.1.2 pr.2.1 ∨ pr.2.1 = pr.1.1 := by
            rcases hσ with hσr | hσe
            · have hσ' : RenamesTo (.prod (duals.map (·.2))) (.prod (prs.map (·.1))) := by
                rw [← hσp]
                exact hσr
              have hcomp' := (renamesTo_prod_comp hσ').2
              intro pr hpr
              left
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
              have hid : i < duals.length := by
                simp only [List.length_zip] at hi
                omega
              have hip : i < prs.length := by
                simp only [List.length_zip] at hi
                omega
              rw [List.getElem_zip]
              have h5 := hcomp' ((duals.map (·.2))[i]'(by simpa using hid),
                (prs.map (·.1))[i]'(by simpa using hip)) (by
                  rw [show ((duals.map (·.2))[i]'(by simpa using hid),
                    (prs.map (·.1))[i]'(by simpa using hip))
                    = ((duals.map (·.2)).zip (prs.map (·.1)))[i]'(by
                        simp only [List.length_zip, List.length_map]
                        omega) from (List.getElem_zip ..).symm]
                  exact List.getElem_mem _)
              simpa [List.getElem_map] using h5
            · -- σ = τp = prod(duals-fst):prs-fst = duals-fst
              have he : (prs.map (·.1)) = (duals.map (·.1)) := by
                have h6 : (Ty.prod (prs.map (·.1))) = .prod (duals.map (·.1)) := by
                  rw [← hσp, hσe]
                injection h6
              intro pr hpr
              right
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
              have hid : i < duals.length := by
                simp only [List.length_zip] at hi
                omega
              have hip : i < prs.length := by
                simp only [List.length_zip] at hi
                omega
              rw [List.getElem_zip]
              have h7 := List.getElem_of_eq he (by simpa using hip)
              simpa [List.getElem_map] using h7
          refine WTTree.atomTuple ?_ ?_ ?_
          · omega
          · simp only [List.length_map] at hlenv
            omega
          · exact slot_atoms hwfD ps hps hreachcomp hsnd hlen hcomp hσcomp
              (by simpa using hlenv) hvcomp (by omega)
  | .pvar x, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv
  | .wild, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv
  | .pval e, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv
  | .pctor c ps, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv
  | .papp f qs, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv
  | .embed y, _, _, _, _, _, _, _, _, σ, hp, hreach, hslot, hσ, hv => by
      rcases slot_value_inv hwfD hslot with
        ⟨τm, τm'', hm, hren, howσ, huni, hok⟩ | ⟨ms, prs, rfl, hσp, hτp, hlen, hcomp⟩
      · exact buildAtom hwfD _ hp hm hren
          (slot_left_how hreach hσ howσ) hreach huni hok hv
      · exact WTTree.atomSlot rfl hp hreach hslot hσ hv

theorem slot_atoms {SD : SigD} {SP : SigP} {SF : SigF} (hwfD : SigDWF SD) :
    ∀ (ps : List Pattern) {Γ : TyCtx} {Φ : PatParamCtx} {Δ Δ' : BindCtx}
      {duals : List (Ty × Ty)} {ms vs : List Value} {prs : List (Ty × Ty)},
    PatTys SD SP SF Γ Φ Δ ps duals Δ' →
    (∀ pr ∈ duals, StructReaches pr.1 pr.2) →
    duals.map (·.2) = prs.map (·.2) →
    ms.length = prs.length →
    (∀ pr ∈ ms.zip prs, ValueTy SD SP SF pr.1 (.slot pr.2.1 pr.2.2)) →
    (∀ pr ∈ duals.zip prs, RenamesTo pr.1.2 pr.2.1 ∨ pr.2.1 = pr.1.1) →
    vs.length = duals.length →
    (∀ pr ∈ vs.zip (duals.map (·.2)), ValueTy SD SP SF pr.1 pr.2) →
    ps.length = ms.length →
    WTStack SD SP SF Γ Φ Δ
      ((ps.zip (ms.zip vs)).map fun x => .atom ⟨x.1, x.2.1, x.2.2⟩) Δ'
  | [], _, _, _, _, _, ms, _, _, hps, _, _, _, _, _, _, _, hlp => by
      cases hps
      cases ms with
      | cons _ _ => simp at hlp
      | nil => exact WTStack.nil
  | p :: ps, _, _, _, _, duals, ms, vs, prs, hps, hreaches, hsnd, hl1, hmall,
      hrall, hl2, hvall, hlp => by
      cases hps with
      | cons hph hpst =>
        rename_i Δmid pr0 dualst
        cases ms with
        | nil => simp at hlp
        | cons m₀ ms' =>
          cases prs with
          | nil => simp at hl1
          | cons q₀ prst =>
            cases vs with
            | nil => simp at hl2
            | cons v₀ vst =>
              simp only [List.map_cons, List.cons.injEq] at hsnd
              obtain ⟨hsnd0, hsndt⟩ := hsnd
              simp only [List.zip_cons_cons, List.map_cons] at *
              refine WTStack.cons
                (slot_atom hwfD p hph
                  (hreaches pr0 (List.mem_cons_self ..))
                  (by rw [hsnd0]
                      exact hmall (m₀, q₀) (by simp [List.zip_cons_cons]))
                  (hrall (pr0, q₀) (by simp [List.zip_cons_cons]))
                  (hvall (v₀, pr0.2) (by simp [List.zip_cons_cons]))) ?_
              exact slot_atoms hwfD ps hpst
                (fun q hq => hreaches q (List.mem_cons_of_mem _ hq))
                hsndt
                (by simpa using hl1)
                (fun q hq => hmall q (by simp [List.zip_cons_cons]; exact .inr hq))
                (fun q hq => hrall q (by simp [List.zip_cons_cons]; exact .inr hq))
                (by simpa using hl2)
                (fun q hq => hvall q (by simp [List.zip_cons_cons]; exact .inr hq))
                (by simpa using hlp)
end

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
    | atom hsc hp hm hren how _hreach htm hok hv =>
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
    | atom hsc hp hm hren how _hreach htm hok hv =>
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
    | atom hsc hp hm hren how _hreach htm hok hv =>
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

/-- 素形パターンの something 原子を fresh 構造添字で組む
    (PAT-VAR/WILD/VALUE の構造側の自由度 = §4.2 fresh-leaf 構成を使い、
    something の内在型変数と同じ fresh 変数へ取り直す;MS-PROD-SOME 保存の再建) -/
theorem something_atom {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {Δ Δ' : BindCtx} {p : Pattern} {v : Value} {τp τt : Ty}
    (hprim : p.isPrimForm = true)
    (hp : PatTy SD SP SF Γ Φ Δ p τp τt Δ')
    (hv : ValueTy SD SP SF v τt) :
    WTTree SD SP SF Γ Φ Δ (.atom ⟨p, .something, v⟩) Δ' := by
  cases p with
  | pvar x =>
      cases hp with
      | pvar hx =>
        exact WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
          rfl (PatTy.pvar (τp := .var (freshFor _)) hx) ValueTy.something
          (renamesTo_var_refl _) (oneWay_var_refl _) structReaches_var
          (unifiable_var_fresh _) MatcherOK.something hv
  | wild =>
      cases hp
      exact WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
        rfl (PatTy.wild (τp := .var (freshFor _))) ValueTy.something
        (renamesTo_var_refl _) (oneWay_var_refl _) structReaches_var
        (unifiable_var_fresh _) MatcherOK.something hv
  | pval e =>
      cases hp with
      | pval hty =>
        exact WTTree.atom (τm := .var (freshFor _)) (τm' := .var (freshFor _))
          rfl (PatTy.pval (τp := .var (freshFor _)) hty) ValueTy.something
          (renamesTo_var_refl _) (oneWay_var_refl _) structReaches_var
          (unifiable_var_fresh _) MatcherOK.something hv
  | pctor c ps => simp [Pattern.isPrimForm] at hprim
  | ptuple ps => simp [Pattern.isPrimForm] at hprim
  | pand p₁ p₂ => simp [Pattern.isPrimForm] at hprim
  | por p₁ p₂ => simp [Pattern.isPrimForm] at hprim
  | papp f qs => simp [Pattern.isPrimForm] at hprim
  | embed y => simp [Pattern.isPrimForm] at hprim

/-- MS-PROD-SOME の保存:素形パターンの積マッチャー原子は something 原子へ
    (scalar 形・スロット形とも `something_atom` で再建)。 -/
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
    | atom hsc hp hm hren how _hreach htm hok hv =>
        exact ⟨hρ, Δ₀, hθ, WTStack.cons (something_atom hprim hp hv) hrest⟩
    | atomAnd h₁ h₂ => simp [Pattern.isPrimForm] at hprim
    | atomOr h₁ h₂ => simp [Pattern.isPrimForm] at hprim
    | atomTuple hlen1 hlen2 hcomp => simp [Pattern.isPrimForm] at hprim
    | atomSlot hsc hp hreach hslot hσ hv =>
        exact ⟨hρ, Δ₀, hθ, WTStack.cons (something_atom hprim hp hv) hrest⟩

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
    | atom hsc _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomSlot hsc _ _ _ _ _ => simp [atomScalarOK] at hsc
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
    | mnode rem duals Γf Δθf Δfin Φf hj hnd hocc hq hforall hreachΦ hd1 hd2 hθf hinner =>
      have hrem : rem = [] := by
        cases rem with
        | nil => rfl
        | cons pr rem' => exact nomatch hocc
      subst hrem
      cases hq
      exact ⟨hρ, Δ₀, hθ, hrest⟩

/-- MS-MNODE-VARPAT の保存:~y を Π(y) = q に差し替えて外側へ押し出す。
    q の双対型付けは WT-MNODE の q-premise 先頭、マッチャー側の premise は
    内側 embed 原子のもの(PAT-EMBED の Φf 対と q-premise の双対対は
    RemInPhi で一致)をそのまま移し、`buildAtom` で形に応じて組む。 -/
theorem preserve_mnodeVarpat {SD : SigD} {SP : SigP} {SF : SigF}
    {Γ : TyCtx} {Φ : PatParamCtx} (hwfD : SigDWF SD)
    {y : String} {q : Pattern} {m v : Value} {Srest : List Tree}
    {ρf : Env} {θf : Subst} {piE : PiEnv}
    {S : List Tree} {ρ : Env} {θ : Subst} {Δgoal : BindCtx}
    (hfind : List.find? (fun pr => pr.1 == y) piE = some (y, q))
    (hwt : WTStateAt SD SP SF Γ Φ
      ⟨.mnode (.atom ⟨.embed y, m, v⟩ :: Srest) ρf θf piE :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ
      ⟨.atom ⟨q, m, v⟩ :: .mnode Srest ρf θf piE :: S, ρ, θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | mnode rem duals Γf Δθf Δfin Φf hj hnd hocc hq hforall hreachΦ hd1 hd2 hθf hinner =>
      cases rem with
      | nil => simp [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars] at hocc
      | cons re rem' =>
        obtain ⟨ykey, q'⟩ := re
        have hocc2 : y :: stackEmbedOccs Srest = ykey :: rem'.map (·.1) := by
          simpa [stackEmbedOccs, treeEmbedOccs, Pattern.embedVars] using hocc
        injection hocc2 with hykey hoccrest
        subst hykey
        obtain ⟨j, hj⟩ := hj
        have hmem : (y, q') ∈ piE := by
          have h1 : (y, q') ∈ piE.drop j := by rw [← hj]; simp
          exact List.mem_of_mem_drop h1
        have hfind' := find?_eq_of_nodup_keys hnd hmem
        have hqq : q = q' := by
          have h2 := Option.some.inj (hfind.symm.trans hfind')
          exact congrArg Prod.snd h2
        subst hqq
        cases hq with
        | cons hqhead hqtail =>
          obtain ⟨hfhead, hftail⟩ := hforall
          cases hinner with
          | cons hemb hinnerrest =>
            cases hemb with
            | atom hsc hpEmb hm hren how hreachE htm hok hv =>
                cases hpEmb with
                | embed hpfind =>
                  rename_i pr
                  have hpd := congrArg Prod.snd
                    (Option.some.inj (hpfind.symm.trans hfhead))
                  subst hpd
                  refine ⟨hρ, Δ₀, hθ, WTStack.cons
                    (buildAtom hwfD q hqhead hm hren how hreachE htm hok hv)
                    (WTStack.cons ?_ hrest)⟩
                  refine WTTree.mnode rem' _ Γf Δθf Δfin Φf
                    ⟨j+1, ?_⟩ hnd hoccrest hqtail hftail hreachΦ hd1 hd2 hθf hinnerrest
                  calc rem' = ((y, q) :: rem').drop 1 := rfl
                    _ = (piE.drop j).drop 1 := by rw [hj]
                    _ = piE.drop (j + 1) := by rw [List.drop_drop]
            | atomSlot hscE hpEmb hreachE hslotE hσE hv =>
                cases hpEmb with
                | embed hpfind =>
                  rename_i pr
                  have hpd := congrArg Prod.snd
                    (Option.some.inj (hpfind.symm.trans hfhead))
                  subst hpd
                  refine ⟨hρ, Δ₀, hθ, WTStack.cons
                    (slot_atom hwfD q hqhead hreachE hslotE hσE hv)
                    (WTStack.cons ?_ hrest)⟩
                  refine WTTree.mnode rem' _ Γf Δθf Δfin Φf
                    ⟨j+1, ?_⟩ hnd hoccrest hqtail hftail hreachΦ hd1 hd2 hθf hinnerrest
                  calc rem' = ((y, q) :: rem').drop 1 := rfl
                    _ = (piE.drop j).drop 1 := by rw [hj]
                    _ = piE.drop (j + 1) := by rw [List.drop_drop]

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
    | atom hsc _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomSlot hsc _ _ _ _ _ => simp [atomScalarOK] at hsc
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
    | atom hsc _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomSlot hsc _ _ _ _ _ => simp [atomScalarOK] at hsc
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
    | atom hsc _ _ _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomSlot hsc _ _ _ _ _ => simp [atomScalarOK] at hsc
    | atomOr h₁ h₂ => exact ⟨hρ, Δ₀, hθ, WTStack.cons h₂ hrest⟩

/-! ### MS-MATCHER 歩行の支持補題([b-5.5] の部品)

* `ppm_some_shapeOK` — pp ≈ p 成功なら shape 一致(τt 節型付け oracle は
  shape 一致節に制限して仮定するので、発火節への適用にこれを使う)
* `ppty_refresh_renames` — PP-Con/PP-Tuple の refresh 対は構造注釈 =
  標的の改名(slot_atom の hσ 供給)
* `decodeTuple_typed` — アーム本体の分解値の成分型付け
* `decodeM_typed` — 次マッチャー式の分解評価値のスロット型付け
* `walk_env_typed` — アーム本体 N の評価環境 ρd ++ ρp ++ ρm の型付け合成 -/

mutual
theorem ppm_some_shapeOK {SF : SigF} :
    ∀ (pp : PPat) {ρ : Env} {p : Pattern} {r : List Pattern × Env},
    PPM SF ρ pp p (some r) → ppShapeOK pp p = true
  | .hole, _, _, _, hm => by cases hm; rfl
  | .wild, _, _, _, hm => by cases hm; rfl
  | .pval y, _, _, _, hm => by cases hm; rfl
  | .ctor c pps, _, _, _, hm => by
      cases hm with
      | ctor hl1 hl2 hall =>
          simp only [ppShapeOK, beq_self_eq_true, Bool.true_and]
          exact ppm_some_shapeOK_list pps hl1 hl2 hall
  | .tuple pps, _, _, _, hm => by
      cases hm with
      | tuple hl1 hl2 hall =>
          simp only [ppShapeOK]
          exact ppm_some_shapeOK_list pps hl1 hl2 hall

theorem ppm_some_shapeOK_list {SF : SigF} :
    ∀ (pps : List PPat) {ρ : Env} {ps : List Pattern}
      {rs : List (List Pattern × Env)},
    pps.length = ps.length → (pps.zip ps).length = rs.length →
    (∀ tr ∈ (pps.zip ps).zip rs, PPM SF ρ tr.1.1 tr.1.2 (some tr.2)) →
    ppShapeOKList pps ps = true
  | [], _, ps, rs, hl1, _, _ => by
      cases ps with
      | nil => rfl
      | cons _ _ => simp at hl1
  | pp :: pps, _, ps, rs, hl1, hl2, hall => by
      cases ps with
      | nil => simp at hl1
      | cons p ps =>
          cases rs with
          | nil => simp [List.zip_cons_cons] at hl2
          | cons r rs =>
              simp only [ppShapeOKList, Bool.and_eq_true]
              refine ⟨ppm_some_shapeOK pp
                (hall ((pp, p), r) (by simp [List.zip_cons_cons])), ?_⟩
              exact ppm_some_shapeOK_list pps (by simpa using hl1)
                (by simpa [List.zip_cons_cons] using hl2)
                (fun tr htr => hall tr (by simp [List.zip_cons_cons]; exact .inr htr))
end

/-- refresh 対(PP-Con/PP-Tuple の premise)から:外側対の構造注釈は標的の改名 -/
theorem ppty_refresh_renames {pairs pairs' : List (Ty × Ty)}
    (hlen : pairs.length = pairs'.length)
    (href : ∀ pr ∈ pairs.zip pairs', pr.1.2 = pr.2.2 ∧ FreshLike pr.1.2 pr.2.1) :
    ∀ pr ∈ pairs', RenamesTo pr.2 pr.1 := by
  intro pr hpr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
  have hip : i < pairs.length := by omega
  have hiz : i < (pairs.zip pairs').length := by
    simp only [List.length_zip]
    omega
  have hf := href (pairs.zip pairs')[i] (List.getElem_mem hiz)
  rw [List.getElem_zip] at hf
  obtain ⟨heq, hfl⟩ := hf
  rw [← heq]
  exact hfl

/-- 分解値の成分型付け:t : prodK τs(|τs| = k)の k 分解は τs で成分ごとに型付く -/
theorem decodeTuple_typed {SD : SigD} {SP : SigP} {SF : SigF} (hwfD : SigDWF SD)
    {k : Nat} {t : Value} {vs : List Value} {τs : List Ty}
    (hd : decodeTuple k t = some vs)
    (hlen : τs.length = k)
    (ht : ValueTy SD SP SF t (prodK τs)) :
    vs.length = k ∧ ∀ pr ∈ vs.zip τs, ValueTy SD SP SF pr.1 pr.2 := by
  by_cases h1 : k = 1
  · subst h1
    simp only [decodeTuple, beq_self_eq_true, if_true, Option.some.injEq] at hd
    subst hd
    cases τs with
    | nil => simp at hlen
    | cons τ τs' =>
      cases τs' with
      | cons _ _ => simp at hlen
      | nil =>
        refine ⟨rfl, ?_⟩
        intro pr hpr
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hpr
        subst hpr
        simpa [prodK] using ht
  · have hk : (k == 1) = false := by simpa using h1
    have hne : τs.length ≠ 1 := by omega
    rw [prodK_of_len_ne_one hne] at ht
    cases t with
    | tuple ts =>
        simp only [decodeTuple, hk, Bool.false_eq_true, if_false] at hd
        by_cases h2 : ts.length = k
        · rw [if_pos (by simpa using h2)] at hd
          obtain rfl := Option.some.inj hd
          obtain ⟨vs', heq, hlen', hcomp⟩ := canonical_prod hwfD ht
          injection heq with heq'
          subst heq'
          exact ⟨h2, hcomp⟩
        · rw [if_neg (by simpa using h2)] at hd
          exact nomatch hd
    | lit n => simp [decodeTuple, hk] at hd
    | ctor c vs' => simp [decodeTuple, hk] at hd
    | closure self ρc x e => simp [decodeTuple, hk] at hd
    | matcherV ρm cls => simp [decodeTuple, hk] at hd
    | something => simp [decodeTuple, hk] at hd

/-- 次マッチャー式の分解評価:decomposeME の各成分のスロット型付けから、
    評価値の decodeTuple 分解の各成分のスロット型付けを得る -/
theorem decodeM_typed {SD : SigD} {SP : SigP} {SF : SigF} {Γm : TyCtx} {ρm : Env}
    (ha : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → EnvTyped SD SP SF Γ' ρ' →
       HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    (hρm : EnvTyped SD SP SF Γm ρm)
    {M : Expr} {k : Nat} {Ms : List Expr} {vM : Value} {ms : List Value}
    {pairs : List (Ty × Ty)}
    (hde : decomposeME M k = some Ms)
    (hlenp : pairs.length = k)
    (hslots : ∀ pr ∈ Ms.zip pairs, HasTy SD SP SF Γm pr.1 (.slot pr.2.1 pr.2.2))
    (hev : Eval SF ρm M vM)
    (hdt : decodeTuple k vM = some ms) :
    ms.length = k ∧ ∀ pr ∈ ms.zip pairs, ValueTy SD SP SF pr.1 (.slot pr.2.1 pr.2.2) := by
  by_cases h1 : k = 1
  · subst h1
    simp only [decomposeME, beq_self_eq_true, if_true, Option.some.injEq] at hde
    simp only [decodeTuple, beq_self_eq_true, if_true, Option.some.injEq] at hdt
    subst hde
    subst hdt
    cases pairs with
    | nil => simp at hlenp
    | cons pr₀ prt =>
      cases prt with
      | cons _ _ => simp at hlenp
      | nil =>
        refine ⟨rfl, ?_⟩
        intro q hq
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
        subst hq
        exact ha hev hρm (hslots (M, pr₀) (by simp [List.zip_cons_cons]))
  · have hk : (k == 1) = false := by simpa using h1
    cases M with
    | tuple es =>
        simp only [decomposeME, hk, Bool.false_eq_true, if_false] at hde
        by_cases h2 : es.length = k
        · rw [if_pos (by simpa using h2)] at hde
          obtain rfl := Option.some.inj hde
          cases hev with
          | tuple hlenv hall =>
              rename_i vms
              simp only [decodeTuple, hk, Bool.false_eq_true, if_false] at hdt
              rw [if_pos (by simp only [beq_iff_eq]; omega)] at hdt
              obtain rfl := Option.some.inj hdt
              refine ⟨by omega, ?_⟩
              intro q hq
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
              have hiv : i < vms.length := by
                simp only [List.length_zip] at hi
                omega
              have hipr : i < pairs.length := by
                simp only [List.length_zip] at hi
                omega
              have hie : i < es.length := by omega
              rw [List.getElem_zip]
              have hev_i : Eval SF ρm es[i] vms[i] := by
                have hz : i < (es.zip vms).length := by
                  simp only [List.length_zip]
                  omega
                have := hall (es.zip vms)[i] (List.getElem_mem hz)
                rwa [List.getElem_zip] at this
              have hslot_i : HasTy SD SP SF Γm es[i] (.slot pairs[i].1 pairs[i].2) := by
                have hz : i < (es.zip pairs).length := by
                  simp only [List.length_zip]
                  omega
                have := hslots (es.zip pairs)[i] (List.getElem_mem hz)
                rwa [List.getElem_zip] at this
              exact ha hev_i hρm hslot_i
        · rw [if_neg (by simpa using h2)] at hde
          exact nomatch hde
    | var x => simp [decomposeME, hk] at hde
    | lam x e => simp [decomposeME, hk] at hde
    | app e₁ e₂ => simp [decomposeME, hk] at hde
    | lit n => simp [decomposeME, hk] at hde
    | letE x e₁ e₂ => simp [decomposeME, hk] at hde
    | fix f x e => simp [decomposeME, hk] at hde
    | ctor c es => simp [decomposeME, hk] at hde
    | prim op es => simp [decomposeME, hk] at hde
    | matchAll e₁ e₂ p e₃ => simp [decomposeME, hk] at hde
    | matcher cls => simp [decomposeME, hk] at hde
    | something => simp [decomposeME, hk] at hde

/-- アーム本体 N の評価環境 ρd ++ ρp ++ ρm の型付け(ArmsTy の文脈形に対応) -/
theorem walk_env_typed {SD : SigD} {SP : SigP} {SF : SigF} {Γm : TyCtx}
    {ρm ρd ρp : Env} {Γij Δi : BindCtx}
    (hρm : EnvTyped SD SP SF Γm ρm)
    (hddom : ∀ pr ∈ ρd, pr.1 ∈ Γij.map (·.1))
    (hdbind : ∀ pr ∈ Γij, ∃ v, Env.find? ρd pr.1 = some v ∧ ValueTy SD SP SF v pr.2)
    (hpdom : ∀ pr ∈ ρp, pr.1 ∈ Δi.map (·.1))
    (hpbind : ∀ pr ∈ Δi, ∃ v, Env.find? ρp pr.1 = some v ∧ ValueTy SD SP SF v pr.2) :
    EnvTyped SD SP SF (BindCtx.toCtx Γij ++ BindCtx.toCtx Δi ++ Γm)
      (ρd ++ ρp ++ ρm) := by
  have h₁ := envTyped_of_bindings hddom hdbind
  have h₂ := envTyped_of_bindings hpdom hpbind
  have h12 := envTyped_append h₁ (bindings_cover hdbind) h₂
  refine envTyped_append h12 ?_ hρm
  intro y hy
  simp only [TyCtx.find?] at hy
  cases hfd : List.find? (fun pr => pr.1 == y) (BindCtx.toCtx Γij) with
  | some pr =>
      have hd := bindings_cover hdbind y (by simp [TyCtx.find?, hfd])
      cases hρd : Env.find? ρd y with
      | none => exact absurd hρd hd
      | some w =>
          have : Env.find? (ρd ++ ρp) y = some w := Env.find?_append_left hρd
          simp [this]
  | none =>
      rw [list_find?_append_none hfd] at hy
      have hp := bindings_cover hpbind y (by simpa [TyCtx.find?] using hy)
      cases hρd : Env.find? ρd y with
      | some w =>
          have : Env.find? (ρd ++ ρp) y = some w := Env.find?_append_left hρd
          simp [this]
      | none =>
          have hstep : Env.find? (ρd ++ ρp) y = Env.find? ρp y := by
            apply Env.find?_append_right
            intro pr hpr heq
            have : Env.find? ρd pr.1 ≠ none := by
              simp only [Env.find?]
              cases hf : List.find? (fun q => q.1 == pr.1) ρd with
              | none =>
                  have := List.find?_eq_none.mp hf pr hpr
                  simp at this
              | some _ => simp
            rw [heq] at this
            exact this hρd
          rw [hstep]
          exact hp

/-! ### バアホール節の除外不変量(論文 C.3「by clause order」の歩行版)

構成子/タプルパターンの歩行はバアホール節($ 節、catch-all 含む)に達する
前に、shape の合う一般形節で必ず発火する(一般形節の pp は穴だけなので
PPM が失敗しえない)。これを「対応する一般形節が現在の節接尾辞中で
最初のバアホール節より前に残っている」という不変量として carry する。
初期確立 = WT-ATOM の構造前提(⊑ が τm の頭を揃える、論文 2360 行の議論)
+ Def 4.2(3) Coverage + (2′) holeAfterGenerals。 -/

/-- pp 列に gpp があり、その前にバアホールが無い -/
def GeneralBeforeHoles (pps : List PPat) (gpp : PPat) : Prop :=
  ∃ i, ∃ h : i < pps.length, pps[i] = gpp ∧
    ∀ j, (h' : j < pps.length) → j < i → pps[j] ≠ PPat.hole

theorem generalBeforeHoles_of_mem_order : ∀ {pps : List PPat} {gpp : PPat},
    gpp ∈ pps →
    (∀ i, (h : i < pps.length) → pps[i] = PPat.hole → gpp ∈ pps.take i) →
    GeneralBeforeHoles pps gpp
  | [], gpp, hmem, _ => nomatch hmem
  | pp₀ :: rest, gpp, hmem, hord => by
      by_cases hh : pp₀ = PPat.hole
      · exfalso
        have := hord 0 (by simp) (by simpa using hh)
        simp at this
      · by_cases hg : pp₀ = gpp
        · exact ⟨0, by simp, by simpa using hg, fun j h' hj => by omega⟩
        · have hmem' : gpp ∈ rest := by
            rcases List.mem_cons.mp hmem with heq | hm'
            · exact absurd heq.symm hg
            · exact hm'
          have hord' : ∀ i, (h : i < rest.length) → rest[i] = PPat.hole →
              gpp ∈ rest.take i := by
            intro i h hi
            have h2 := hord (i + 1) (by simpa using Nat.succ_lt_succ h)
              (by simpa using hi)
            rw [List.take_succ_cons] at h2
            rcases List.mem_cons.mp h2 with heq | hm'
            · exact absurd heq.symm hg
            · exact hm'
          obtain ⟨i, h, hgi, hnoh⟩ :=
            generalBeforeHoles_of_mem_order hmem' hord'
          refine ⟨i + 1, by simpa using Nat.succ_lt_succ h,
            by simpa using hgi, ?_⟩
          intro j h' hj
          cases j with
          | zero => simpa using hh
          | succ j' =>
              have := hnoh j' (by simpa using Nat.lt_of_succ_lt_succ h') (by omega)
              simpa using this

theorem generalBeforeHoles_tail {pp₀ : PPat} {rest : List PPat} {gpp : PPat}
    (h : GeneralBeforeHoles (pp₀ :: rest) gpp) (hne : pp₀ ≠ gpp) :
    GeneralBeforeHoles rest gpp := by
  obtain ⟨i, hi, hg, hnoh⟩ := h
  cases i with
  | zero => exact absurd (by simpa using hg) hne
  | succ i' =>
      refine ⟨i', Nat.lt_of_succ_lt_succ hi, by simpa using hg, ?_⟩
      intro j h' hj
      have := hnoh (j + 1) (by simpa using Nat.succ_lt_succ h') (by omega)
      simpa using this

theorem generalBeforeHoles_hole_head {pp₀ : PPat} {rest : List PPat} {gpp : PPat}
    (h : GeneralBeforeHoles (pp₀ :: rest) gpp) (hh : pp₀ = PPat.hole)
    (hne : gpp ≠ PPat.hole) : False := by
  obtain ⟨i, hi, hg, hnoh⟩ := h
  cases i with
  | zero => exact hne ((by simpa using hg : pp₀ = gpp) ▸ hh)
  | succ i' =>
      have := hnoh 0 (by simp) (by omega)
      simp only [List.getElem_cons_zero] at this
      exact this hh

/-- 一般形節の pp は同じ構成子・同アリティのパターンに必ず shape 一致する -/
theorem ppShapeOKList_replicate : ∀ (ps : List Pattern),
    ppShapeOKList (List.replicate ps.length .hole) ps = true
  | [] => rfl
  | p :: ps => by
      simp only [List.length_cons, List.replicate_succ, ppShapeOKList,
        ppShapeOK, Bool.true_and]
      exact ppShapeOKList_replicate ps

theorem ppShapeOK_generalPP {c : String} {ps : List Pattern} {k : Nat}
    (hlen : ps.length = k) :
    ppShapeOK (generalPP c k) (.pctor c ps) = true := by
  subst hlen
  simp only [generalPP, ppShapeOK, beq_self_eq_true, Bool.true_and]
  exact ppShapeOKList_replicate ps

theorem ppShapeOK_generalTuple {ps : List Pattern} {k : Nat}
    (hlen : ps.length = k) :
    ppShapeOK (PPat.tuple (List.replicate k .hole)) (.ptuple ps) = true := by
  subst hlen
  simp only [ppShapeOK]
  exact ppShapeOKList_replicate ps

/-- 除外不変量:p が構成子/タプル形なら対応する一般形節が
    接尾辞の pp 列でバアホールより前に残る -/
def ExclInv (SP : SigP) (p : Pattern) (cls : List Clause) : Prop :=
  (∀ c ps sig, p = .pctor c ps →
     List.find? (fun pr => pr.1 == c) SP = some (c, sig) →
     GeneralBeforeHoles (cls.map (·.1)) (generalPP c sig.args.length)) ∧
  (∀ ps, p = .ptuple ps →
     GeneralBeforeHoles (cls.map (·.1)) (PPat.tuple (List.replicate ps.length .hole)))

/-- 除外不変量の初期確立(WT-ATOM の構造前提+Def 4.2(3)+(2′)) -/
theorem exclInv_init {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} {Δ Δ' : BindCtx} (hwfP : SigPWF SP)
    {p : Pattern} {ρm : Env} {cls : List Clause} {τp τt τm τm' : Ty}
    (hp : PatTy SD SP SF Γ Φ Δ p τp τt Δ')
    (hm : ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm))
    (hren : RenamesTo τm τm') (how : OneWay τp τm') :
    ExclInv SP p cls := by
  have hcons := valueTy_matcherV_consistent hm
  constructor
  · intro c ps sig hpe hfind
    subst hpe
    cases hp with
    | pctor hfind' hps hstr htgt =>
        rename_i sig₁ ss ts duals
        have hsig : sig₁ = sig :=
          congrArg (·.2) (Option.some.inj (hfind'.symm.trans hfind))
        subst hsig
        obtain ⟨⟨n, hres⟩, -⟩ := hwfP _ (List.mem_of_find?_eq_some hfind)
        obtain ⟨θ, -, happ⟩ := how
        rw [hres] at happ
        simp only [Ty.instSig, Ty.applyTS] at happ
        obtain ⟨l₀, hτm, -⟩ := renamesTo_data_inv hren happ.symm
        subst hτm
        have hhm : Ty.headMatches sig₁.res (.data n l₀) = true := by
          rw [hres]
          simp [Ty.headMatches]
        obtain ⟨M, arms, hmem⟩ :=
          hcons.coverage _ (List.mem_of_find?_eq_some hfind) hhm
        apply generalBeforeHoles_of_mem_order (List.mem_map.mpr ⟨_, hmem, rfl⟩)
        intro i h hi
        have h' : i < cls.length := by simpa using h
        rw [List.getElem_map] at hi
        obtain ⟨M', arms', hmem'⟩ :=
          (hcons.holeAfterGenerals i h' hi).1 _ (List.mem_of_find?_eq_some hfind) hhm
        rw [← List.map_take]
        exact List.mem_map.mpr ⟨_, hmem', rfl⟩
  · intro ps hpe
    subst hpe
    cases hp with
    | ptuple hps =>
        rename_i duals
        obtain ⟨θ, -, happ⟩ := how
        simp only [Ty.applyTS] at happ
        obtain ⟨l₀, hτm, hlen₀⟩ := renamesTo_prod_inv hren happ.symm
        subst hτm
        obtain ⟨M, arms, hmem⟩ := hcons.coverageProd l₀ rfl
        have hlar : l₀.length = ps.length := by
          rw [hlen₀, applyTSList_length]
          simp only [List.length_map]
          exact (patTys_length hps).symm
        rw [← hlar]
        apply generalBeforeHoles_of_mem_order (List.mem_map.mpr ⟨_, hmem, rfl⟩)
        intro i h hi
        have h' : i < cls.length := by simpa using h
        rw [List.getElem_map] at hi
        obtain ⟨M', arms', hmem'⟩ := (hcons.holeAfterGenerals i h' hi).2 l₀ rfl
        rw [← List.map_take]
        exact List.mem_map.mpr ⟨_, hmem', rfl⟩
/-- 除外不変量の PP-FAIL 維持:shape 一致する一般形節は PPM が失敗しえない
    (穴は何にでも一致)ので、失敗した先頭節は対応する一般形節ではない -/
theorem exclInv_ppfail {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {Φ : PatParamCtx} {Δ Δ' : BindCtx}
    {p : Pattern} {τp τt : Ty} {pp : PPat} {M : Expr}
    {arms : List (DPat × Expr)} {cls : List Clause}
    (hp : PatTy SD SP SF Γ Φ Δ p τp τt Δ')
    (hshape : ppShapeOK pp p = false)
    (hex : ExclInv SP p ((pp, M, arms) :: cls)) :
    ExclInv SP p cls := by
  obtain ⟨h1, h2⟩ := hex
  constructor
  · intro c ps sig hpe hfind
    have hg := h1 c ps sig hpe hfind
    simp only [List.map_cons] at hg
    refine generalBeforeHoles_tail hg ?_
    intro hpp
    subst hpe
    subst hpp
    cases hp with
    | pctor hfind' hps hstr htgt =>
        rename_i sig₁ ss ts duals
        have hsig : sig₁ = sig :=
          congrArg (·.2) (Option.some.inj (hfind'.symm.trans hfind))
        subst hsig
        have hlen : ps.length = sig₁.args.length := by
          have ha := patTys_length hps
          have hb := congrArg List.length hstr
          simp only [List.length_map] at hb
          omega
        rw [ppShapeOK_generalPP hlen] at hshape
        exact nomatch hshape
  · intro ps hpe
    have hg := h2 ps hpe
    simp only [List.map_cons] at hg
    refine generalBeforeHoles_tail hg ?_
    intro hpp
    subst hpe
    subst hpp
    rw [ppShapeOK_generalTuple rfl] at hshape
    exact nomatch hshape

/-! ### MS-MATCHER 系の節歩行保存([b-5.5] 本体)

MAtom.rec(motive_3 のみ非自明)。不変量は節接尾辞に membership 単調
(hclat/hppnd/harmnd)+除外不変量 ExclInv(PP-FAIL で先頭を落として維持)。
oracle:`hevG` = 評価型付け(∀ρ'∀Γ' 形;[b-6] で結合帰納法から放電)、
`hclat` = shape 一致節の τt での節型付け(値の内在節型付けの τt インスタンス
への輸送;[b-6] で放電)。発火時は論文 C.3 の場合分けどおり:
非バアホール節 = refresh 対で slot_atoms、バアホール節 = prim なら fresh
構造添字で scalar 再建・pctor/ptuple は ExclInv が矛盾で排除。 -/

theorem matom_matcher_preserve {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hevG : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    {ρθ : Env} {p₀ : Pattern} {m₀ v₀ : Value}
    {conts : List (List Atom)} {θ'' : Subst}
    (hma : MAtom SF ρθ p₀ m₀ v₀ conts θ'') :
    ∀ {Γ : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty}
      {ρm : Env} {cls : List Clause} {Γm : TyCtx},
    m₀ = .matcherV ρm cls →
    p₀.isClauseForm = true →
    PatTy SD SP SF Γ Φ Δ₀ p₀ τp τt Δ' →
    StructReaches τp τt →
    ValueTy SD SP SF v₀ τt →
    EnvTyped SD SP SF Γm ρm →
    (∀ cl ∈ cls, ppShapeOK cl.1 p₀ = true → ClauseTy SD SP SF Γm τt cl) →
    (∀ cl ∈ cls, ∀ {τ' : Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx},
       PPTy SP cl.1 τ' pairs Δpp → (Δpp.map (·.1)).Nodup) →
    (∀ cl ∈ cls, ∀ arm ∈ cl.2.2, ∀ {τ' : Ty} {Γij : List (String × Ty)},
       PDTy SD arm.1 τ' Γij → (Γij.map (·.1)).Nodup) →
    ExclInv SP p₀ cls →
    θ'' = [] ∧ ∀ as ∈ conts, WTStack SD SP SF Γ Φ Δ₀ (as.map Tree.atom) Δ' := by
  refine MAtom.rec (SF := SF)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ p₀ m₀ v₀ conts θ'' _ =>
      ∀ {Γ : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty}
        {ρm : Env} {cls : List Clause} {Γm : TyCtx},
      m₀ = .matcherV ρm cls →
      p₀.isClauseForm = true →
      PatTy SD SP SF Γ Φ Δ₀ p₀ τp τt Δ' →
      StructReaches τp τt →
      ValueTy SD SP SF v₀ τt →
      EnvTyped SD SP SF Γm ρm →
      (∀ cl ∈ cls, ppShapeOK cl.1 p₀ = true → ClauseTy SD SP SF Γm τt cl) →
      (∀ cl ∈ cls, ∀ {τ' : Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx},
         PPTy SP cl.1 τ' pairs Δpp → (Δpp.map (·.1)).Nodup) →
      (∀ cl ∈ cls, ∀ arm ∈ cl.2.2, ∀ {τ' : Ty} {Γij : List (String × Ty)},
         PDTy SD arm.1 τ' Γij → (Γij.map (·.1)).Nodup) →
      ExclInv SP p₀ cls →
      θ'' = [] ∧ ∀ as ∈ conts, WTStack SD SP SF Γ Φ Δ₀ (as.map Tree.atom) Δ')
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
    intro ρ v
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case someVar =>
    intro ρ x v
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case someValEq =>
    intro ρ e v ve _hev _hsE _ih
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case someValNeq =>
    intro ρ e v ve _hev _hsE _ih
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case mand =>
    intro ρ p₁ p₂ m v
    intro _ _ _ _ _ _ _ _ _ _ hpc _ _ _ _ _ _ _ _
    simp [Pattern.isClauseForm] at hpc
  case mor =>
    intro ρ p₁ p₂ m v
    intro _ _ _ _ _ _ _ _ _ _ hpc _ _ _ _ _ _ _ _
    simp [Pattern.isClauseForm] at hpc
  case mtuple =>
    intro ρ ps ms vs hl1 hl2
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case mprodSome =>
    intro ρ p ms v _hprim
    intro _ _ _ _ _ _ _ _ _ hme _ _ _ _ _ _ _ _ _
    exact nomatch hme
  case mppfail =>
    intro ρ ρm₀ p v pp M arms cls₀ conts θ' _hpc hppm _hma _ihppm ihma
    intro Γ Φ Δ₀ Δ' τp τt ρm cls Γm hme hpc' hp hreach hv henv hclat hppnd harmnd hexcl
    injection hme with hρ hcls
    subst hρ
    subst hcls
    have hshape : ppShapeOK pp p = false := by
      cases hppm with
      | fail hs => exact hs
    exact ihma rfl hpc' hp hreach hv henv
      (fun cl hcl hsh => hclat cl (List.mem_cons_of_mem _ hcl) hsh)
      (fun cl hcl => hppnd cl (List.mem_cons_of_mem _ hcl))
      (fun cl hcl => harmnd cl (List.mem_cons_of_mem _ hcl))
      (exclInv_ppfail hp hshape hexcl)
  case mdpfail =>
    intro ρ ρm₀ p v pp M dp N arms cls₀ ps' ρp conts θ'
      _hpc _hppm _hpd _hma _ihppm ihma
    intro Γ Φ Δ₀ Δ' τp τt ρm cls Γm hme hpc' hp hreach hv henv hclat hppnd harmnd hexcl
    injection hme with hρ hcls
    subst hρ
    subst hcls
    refine ihma rfl hpc' hp hreach hv henv ?_ ?_ ?_ hexcl
    · intro cl hcl hsh
      rcases List.mem_cons.mp hcl with rfl | hcl'
      · have hcl0 := hclat _ (List.mem_cons_self ..) hsh
        cases hcl0 with
        | mk hppty hdec hslots harms0 =>
            cases harms0 with
            | cons _ _ harmst =>
                exact ClauseTy.mk hppty hdec hslots harmst
      · exact hclat cl (List.mem_cons_of_mem _ hcl') hsh
    · intro cl hcl
      rcases List.mem_cons.mp hcl with rfl | hcl'
      · exact fun hppty => hppnd _ (List.mem_cons_self ..) hppty
      · exact fun hppty => hppnd cl (List.mem_cons_of_mem _ hcl') hppty
    · intro cl hcl arm harm
      rcases List.mem_cons.mp hcl with rfl | hcl'
      · exact fun hpd' => harmnd _ (List.mem_cons_self ..) arm
          (List.mem_cons_of_mem _ harm) hpd'
      · exact fun hpd' => harmnd cl (List.mem_cons_of_mem _ hcl') arm harm hpd'
  case mmatcher =>
    intro ρ ρm₀ p v pp M dp N arms cls₀ ps' ρp ρd vN tuples vss vM ms
      hpc₀ hppm hpd hevN hlist hvss hevM hms
      _ihppm _ihevN _ihevM
    intro Γ Φ Δ₀ Δ' τp τt ρm cls Γm hme hpc' hp hreach hv henv hclat hppnd harmnd hexcl
    injection hme with hρ hcls
    subst hρ
    subst hcls
    refine ⟨rfl, ?_⟩
    intro as has
    simp only [List.mem_map] at has
    obtain ⟨vs, hvs, rfl⟩ := has
    -- 発火節の τt 型付け(shape 一致は PPM 成功から)
    have hshape := ppm_some_shapeOK pp hppm
    have hcl := hclat _ (List.mem_cons_self ..) hshape
    cases hcl with
    | mk hppty hdec hslots harms0 =>
        rename_i pairs Δi Ms
        cases harms0 with
        | cons hPD hNty harmst =>
            rename_i Γij
            -- Lem 5.4(強化版;原子環境の評価型付けは hevG から)
            obtain ⟨⟨duals, hduals, hsnd, hdreach⟩, hρpdom, hρpbind⟩ :=
              ppp_core pp hwfP (fun hev hty => hevG hev hty) hppty hp hreach hppm
            have hlen54 := ppm_length pp hppm hppty
            -- アーム本体の評価値の型付けとリスト分解
            have hvN := hevG hevN hNty
            obtain ⟨l, hlistv, hlty⟩ := canonical_list hwfD hL hvN _ rfl
            rw [hlist] at hlistv
            obtain rfl := Option.some.inj hlistv
            -- この vs の分解元タプル
            obtain ⟨t, htmem, htdec⟩ := mapM_mem_inv hvss vs hvs
            obtain ⟨hvslen, hvscomp⟩ := decodeTuple_typed hwfD htdec
              (by simp only [List.length_map]; omega) (hlty t htmem)
            -- 次マッチャー分解のスロット型付け
            rw [hlen54] at hms
            obtain ⟨hmslen, hmscomp⟩ := decodeM_typed
              (fun hev _ hty => hevG hev hty) henv hdec rfl hslots hevM hms
            -- pp の形で分岐
            cases pp with
            | wild =>
                cases hppm
                cases hppty
                cases hduals
                simpa using (WTStack.nil : WTStack SD SP SF Γ Φ Δ₀ [] Δ₀)
            | pval y =>
                cases hppm
                cases hppty
                cases hduals
                simpa using (WTStack.nil : WTStack SD SP SF Γ Φ Δ₀ [] Δ₀)
            | hole =>
                -- バアホール節:後続は (p, vM, t) の 1 原子
                cases hppm
                cases hppty
                rename_i a
                -- ms = [vM]・vs = [t]
                simp [decodeTuple] at hms htdec
                subst hms
                subst htdec
                -- スロット値 vM : slot (var a) τt
                have hslotv : ValueTy SD SP SF vM (.slot (.var a) τt) :=
                  hmscomp (vM, (.var a, τt)) (by simp [List.zip_cons_cons])
                have hvt : ValueTy SD SP SF t τt := by
                  have := hvscomp (t, τt) (by simp [List.zip_cons_cons])
                  simpa using this
                rcases slot_value_inv hwfD hslotv with
                  ⟨τm₁, τm₁'', hm₁, hren₁, _, htm₁, hok₁⟩ |
                  ⟨ms', prs, heqv, hσp, hτp, hlenp, hcompp⟩
                · -- 単一マッチャー:p の形で分岐(prim = fresh 再導出、
                  -- pctor/ptuple = 除外不変量の矛盾)
                  cases p with
                  | pand p₁ p₂ => simp [Pattern.isClauseForm] at hpc'
                  | por p₁ p₂ => simp [Pattern.isClauseForm] at hpc'
                  | papp f qs => simp [Pattern.isClauseForm] at hpc'
                  | embed z => simp [Pattern.isClauseForm] at hpc'
                  | pctor c psargs =>
                      exfalso
                      cases hp with
                      | pctor hfind' hps hstr htgt =>
                          rename_i sig₁ ss ts duals₁
                          have hg := hexcl.1 c psargs (c, sig₁).2 rfl hfind'
                          simp only [List.map_cons] at hg
                          exact generalBeforeHoles_hole_head hg rfl
                            (by simp [generalPP])
                  | ptuple psargs =>
                      exfalso
                      have hg := hexcl.2 psargs rfl
                      simp only [List.map_cons] at hg
                      exact generalBeforeHoles_hole_head hg rfl (by simp)
                  | pvar x =>
                      cases hp with
                      | pvar hx =>
                        refine WTStack.cons (WTTree.atom
                          (τm := τm₁) (τm' := τm₁'')
                          rfl (PatTy.pvar (τp := .var (freshFor τt)) hx)
                          hm₁ hren₁ oneWay_var_left structReaches_var
                          htm₁ hok₁ hvt) ?_
                        simpa using WTStack.nil
                  | wild =>
                      cases hp
                      refine WTStack.cons (WTTree.atom
                        (τm := τm₁) (τm' := τm₁'')
                        rfl (PatTy.wild (τp := .var (freshFor τt)))
                        hm₁ hren₁ oneWay_var_left structReaches_var
                        htm₁ hok₁ hvt) ?_
                      simpa using WTStack.nil
                  | pval e =>
                      cases hp with
                      | pval hty =>
                        refine WTStack.cons (WTTree.atom
                          (τm := τm₁) (τm' := τm₁'')
                          rfl (PatTy.pval (τp := .var (freshFor τt)) hty)
                          hm₁ hren₁ oneWay_var_left structReaches_var
                          htm₁ hok₁ hvt) ?_
                        simpa using WTStack.nil
                · -- 積スロット:σ = var は prod 形と両立しない
                  exact absurd hσp (by simp)
            | ctor c pps =>
                cases hppty with
                | ctor hfindpp hpps hlenp hrefresh =>
                    have hrenpairs := ppty_refresh_renames hlenp hrefresh
                    have hlend := patTys_length hduals
                    have hlenpr : duals.length = pairs.length := by
                      have := congrArg List.length hsnd
                      simpa using this
                    have hrall : ∀ pr ∈ duals.zip pairs,
                        RenamesTo pr.1.2 pr.2.1 ∨ pr.2.1 = pr.1.1 := by
                      intro pr hpr
                      left
                      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
                      have hid : i < duals.length := by
                        simp only [List.length_zip] at hi
                        omega
                      have hip : i < pairs.length := by
                        simp only [List.length_zip] at hi
                        omega
                      rw [List.getElem_zip]
                      have h2 : duals[i].2 = pairs[i].2 := by
                        have := List.getElem_of_eq hsnd (by simpa using hid)
                        simpa [List.getElem_map] using this
                      rw [h2]
                      exact hrenpairs pairs[i] (pairs.getElem_mem hip)
                    have hstack := slot_atoms hwfD ps' (vs := vs) hduals hdreach hsnd
                      hmslen hmscomp hrall
                      (by omega)
                      (by rw [hsnd]; exact hvscomp)
                      (by omega)
                    simpa [List.map_map, Function.comp_def] using hstack
            | tuple pps =>
                cases hppty with
                | tuple hpps hlenp hrefresh =>
                    have hrenpairs := ppty_refresh_renames hlenp hrefresh
                    have hlend := patTys_length hduals
                    have hlenpr : duals.length = pairs.length := by
                      have := congrArg List.length hsnd
                      simpa using this
                    have hrall : ∀ pr ∈ duals.zip pairs,
                        RenamesTo pr.1.2 pr.2.1 ∨ pr.2.1 = pr.1.1 := by
                      intro pr hpr
                      left
                      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
                      have hid : i < duals.length := by
                        simp only [List.length_zip] at hi
                        omega
                      have hip : i < pairs.length := by
                        simp only [List.length_zip] at hi
                        omega
                      rw [List.getElem_zip]
                      have h2 : duals[i].2 = pairs[i].2 := by
                        have := List.getElem_of_eq hsnd (by simpa using hid)
                        simpa [List.getElem_map] using this
                      rw [h2]
                      exact hrenpairs pairs[i] (pairs.getElem_mem hip)
                    have hstack := slot_atoms hwfD ps' (vs := vs) hduals hdreach hsnd
                      hmslen hmscomp hrall
                      (by omega)
                      (by rw [hsnd]; exact hvscomp)
                      (by omega)
                    simpa [List.map_map, Function.comp_def] using hstack
  all_goals intros; trivial

/-- MS-MATCHER 系 3 規則の状態レベル保存(歩行補題の状態への持ち上げ)。
    oracle `hclorc` は「マッチャー値の shape 一致節は使用点の標的型 τt でも
    型付く」(値の内在節型付けの τt インスタンスへの輸送;[b-6] で放電)。 -/
theorem preserve_matcher_step {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hevG : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    (hclorc : ∀ {ρm : Env} {cls : List Clause} {τm τt : Ty} {p : Pattern},
       ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm) →
       Unifiable τm τt → p.isClauseForm = true →
       ∃ Γm, EnvTyped SD SP SF Γm ρm ∧
         ∀ cl ∈ cls, ppShapeOK cl.1 p = true → ClauseTy SD SP SF Γm τt cl)
    {Γ : TyCtx} {Φ : PatParamCtx} {p : Pattern} {ρm : Env} {cls : List Clause}
    {v : Value} {S : List Tree} {ρ : Env} {θ θ' : Subst}
    {conts : List (List Atom)} {Δgoal : BindCtx}
    (hpc : p.isClauseForm = true)
    (hma : MAtom SF (θ ++ ρ) p (.matcherV ρm cls) v conts θ')
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨p, .matcherV ρm cls, v⟩ :: S, ρ, θ⟩ Δgoal) :
    ∀ as ∈ conts,
      WTStateAt SD SP SF Γ Φ ⟨as.map .atom ++ S, ρ, θ' ++ θ⟩ Δgoal := by
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    cases htree with
    | atomAnd h₁ h₂ => simp [Pattern.isClauseForm] at hpc
    | atomOr h₁ h₂ => simp [Pattern.isClauseForm] at hpc
    | atom hsc hp hm hren how hreach htm hok hv =>
        obtain ⟨Γm, henv, hclat⟩ := hclorc hm htm hpc
        have hcons := valueTy_matcherV_consistent hm
        obtain ⟨hz, hstacks⟩ := matom_matcher_preserve hwfD hwfP hL hevG hma
          rfl hpc hp hreach hv henv hclat
          (fun cl hcl {τ' pairs Δpp} hppty => hcons.ppBindNodup cl hcl hppty)
          (fun cl hcl arm harm {τ' Γij} hpd => hcons.armBindNodup cl hcl arm harm hpd)
          (exclInv_init hwfP hp hm hren how)
        subst hz
        intro as has
        exact ⟨hρ, Δ₀, by simpa using hθ, wtStack_append (hstacks as has) hrest⟩

/-! ### MS-PATFUN-ENTER の保存([b-3]) -/

/-- 位置ごとの find? 解決から RemInPhi を組む(Φf は固定なので添字一般化) -/
theorem remInPhi_of_forall {Φf : PatParamCtx} : ∀ {rem : PiEnv} {duals : List (Ty × Ty)},
    rem.length = duals.length →
    (∀ i, (h1 : i < rem.length) → (h2 : i < duals.length) →
       List.find? (fun x => x.1 == rem[i].1) Φf = some (rem[i].1, duals[i])) →
    RemInPhi Φf rem duals
  | [], [], _, _ => trivial
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | pr :: rem, d :: duals, hl, hfind => by
      refine ⟨?_, remInPhi_of_forall (by simpa using hl) ?_⟩
      · have := hfind 0 (by simp) (by simp)
        simpa using this
      · intro i h1 h2
        have := hfind (i + 1) (by simpa using Nat.succ_lt_succ h1)
          (by simpa using Nat.succ_lt_succ h2)
        simpa using this

/-- 鍵つき zip の fst 射影(双対列版) -/
theorem zip_map_fst' {α : Type _} : ∀ (l₁ : List String) (l₂ : List α),
    l₁.length = l₂.length → (l₁.zip l₂).map (·.1) = l₁
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | y :: l₁, [], h => by simp at h
  | y :: l₁, q :: l₂, h => by
      simp [List.zip_cons_cons, zip_map_fst' l₁ l₂ (by simpa using h)]

/-- MS-PATFUN-ENTER の保存。oracle `hinstF`([b-3] 双対スキームの
    インスタンス化;[b-6] で放電):PATFUN-DEF の記録本体導出を呼出しの
    ss/ts でインスタンス化した、実引数双対列(到達不変量つき)と
    Φf = params.zip duals での本体双対導出(マッチャー添字は再フレッシュ化)。
    m 側前提(hm/hren/how/htm/hok/hreach/hv)は本体原子の双対が呼出し原子と
    同一 (τp ▷ τt) なので**素通しで転送**され、scalar なら buildAtom・
    積スロットなら slot_atom で内側原子を組む。 -/
theorem preserve_patfunEnter {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD)
    (hSF : ∀ pr ∈ SF, pr.2.body.embedVars = pr.2.params ∧
       pr.2.body.noEmbedInOr = true ∧ pr.2.params.Nodup)
    (hinstF : ∀ {f : String} {sig : PatFunSig} {qs : List Pattern}
       {Γ : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty},
       List.find? (fun pr => pr.1 == f) SF = some (f, sig) →
       PatTy SD SP SF Γ Φ Δ₀ (.papp f qs) τp τt Δ' →
       ∃ duals Δfin,
         PatTys SD SP SF Γ Φ Δ₀ qs duals Δ' ∧
         (∀ pr ∈ duals, StructReaches pr.1 pr.2) ∧
         PatTy SD SP SF Γ (sig.params.zip duals) [] sig.body τp τt Δfin)
    {Γ : TyCtx} {Φ : PatParamCtx} {f : String} {qs : List Pattern}
    {m v : Value} {sig : PatFunSig} {S : List Tree} {ρ : Env} {θ : Subst}
    {Δgoal : BindCtx}
    (hfind : List.find? (fun pr => pr.1 == f) SF = some (f, sig))
    (hlen : sig.params.length = qs.length)
    (hwt : WTStateAt SD SP SF Γ Φ ⟨.atom ⟨.papp f qs, m, v⟩ :: S, ρ, θ⟩ Δgoal) :
    WTStateAt SD SP SF Γ Φ
      ⟨.mnode [.atom ⟨sig.body, m, v⟩] ρ [] (sig.params.zip qs) :: S, ρ, θ⟩
      Δgoal := by
  obtain ⟨hlin, -, hnd⟩ := hSF _ (List.mem_of_find?_eq_some hfind)
  obtain ⟨hρ, Δ₀, hθ, hstack⟩ := hwt
  cases hstack with
  | cons htree hrest =>
    have hd1 : ∀ y w, Env.find? ρ y = some w → ∃ σ, TyCtx.find? Γ y = some σ := by
      intro y w hf
      obtain ⟨σ, hσ, -⟩ := hρ y w hf
      exact ⟨σ, hσ⟩
    have hd2 : ∀ y w σ τ', Env.find? ρ y = some w → TyCtx.find? Γ y = some σ →
        σ.Inst τ' → ValueTy SD SP SF w τ' := by
      intro y w σ τ' hf hΓ hinst
      obtain ⟨σ', hσ', hall⟩ := hρ y w hf
      obtain rfl := Option.some.inj (hσ'.symm.trans hΓ)
      exact hall τ' hinst
    cases htree with
    | atom hsc hp hm hren how hreach htm hok hv =>
        obtain ⟨duals, Δfin, hqs, hdreach, hbody⟩ := hinstF hfind hp
        have hlq : qs.length = duals.length := patTys_length hqs
        refine ⟨hρ, Δ₀, hθ, WTStack.cons ?_ hrest⟩
        refine WTTree.mnode (sig.params.zip qs) duals Γ [] Δfin
          (sig.params.zip duals) ⟨0, rfl⟩ ?_ ?_ ?_ ?_ ?_ hd1 hd2 substTyped_nil ?_
        · rw [zip_map_fst _ _ hlen]
          exact hnd
        · simp only [stackEmbedOccs, treeEmbedOccs, List.append_nil]
          rw [hlin, zip_map_fst _ _ hlen]
        · rw [zip_map_snd _ _ hlen]
          exact hqs
        · apply remInPhi_of_forall
          · simp only [List.length_zip]
            omega
          · intro i h1 h2
            have hip : i < sig.params.length := by
              simp only [List.length_zip] at h1
              omega
            have hid : i < duals.length := h2
            have h3 : (sig.params.zip qs)[i].1 = sig.params[i] := by
              rw [List.getElem_zip]
            rw [h3]
            apply find?_eq_of_nodup_keys
            · rw [zip_map_fst' _ _ (by omega)]
              exact hnd
            · have h4 : (sig.params.zip duals)[i]'(by
                  simp only [List.length_zip]; omega) = (sig.params[i], duals[i]) :=
                List.getElem_zip ..
              rw [← h4]
              exact List.getElem_mem _
        · intro pr hpr
          exact hdreach pr.2 (List.of_mem_zip hpr).2
        · exact WTStack.cons
            (buildAtom hwfD sig.body hbody hm hren how hreach htm hok hv)
            WTStack.nil
    | atomSlot hsc hp hreach hslot hσ hv =>
        obtain ⟨duals, Δfin, hqs, hdreach, hbody⟩ := hinstF hfind hp
        have hlq : qs.length = duals.length := patTys_length hqs
        refine ⟨hρ, Δ₀, hθ, WTStack.cons ?_ hrest⟩
        refine WTTree.mnode (sig.params.zip qs) duals Γ [] Δfin
          (sig.params.zip duals) ⟨0, rfl⟩ ?_ ?_ ?_ ?_ ?_ hd1 hd2 substTyped_nil ?_
        · rw [zip_map_fst _ _ hlen]
          exact hnd
        · simp only [stackEmbedOccs, treeEmbedOccs, List.append_nil]
          rw [hlin, zip_map_fst _ _ hlen]
        · rw [zip_map_snd _ _ hlen]
          exact hqs
        · apply remInPhi_of_forall
          · simp only [List.length_zip]
            omega
          · intro i h1 h2
            have hip : i < sig.params.length := by
              simp only [List.length_zip] at h1
              omega
            have hid : i < duals.length := h2
            have h3 : (sig.params.zip qs)[i].1 = sig.params[i] := by
              rw [List.getElem_zip]
            rw [h3]
            apply find?_eq_of_nodup_keys
            · rw [zip_map_fst' _ _ (by omega)]
              exact hnd
            · have h4 : (sig.params.zip duals)[i]'(by
                  simp only [List.length_zip]; omega) = (sig.params[i], duals[i]) :=
                List.getElem_zip ..
              rw [← h4]
              exact List.getElem_mem _
        · intro pr hpr
          exact hdreach pr.2 (List.of_mem_zip hpr).2
        · exact WTStack.cons
            (slot_atom hwfD sig.body hbody hreach hslot hσ hv)
            WTStack.nil

/-- Theorem 5.6(b) の Φ 一般化形。Step の結合再帰子(motive_4)で帰納し、
    MS-MNODE-STEP の内側再帰に帰納法の仮定を供給する。
    仮定 `hSF` は PATFUN-DEF の意味論側条件(線形性・noEmbedInOr・仮引数相異)、
    `stackNoOr` は or 分岐が ~x を落とさないための状態不変量
    (site パターンは embed-free、本体は noOr なので到達状態で成立;
    維持は `step_occs` が同時に示す)。
    **全 14 分岐証明済み**(MS-SOME 系 4・MS-AND・MS-OR・MS-TUPLE・
    MS-PROD-SOME・MS-MNODE 系 3・MS-MATCHER 系 3 = 節歩行補題
    `matom_matcher_preserve` 経由・MS-PATFUN-ENTER = `preserve_patfunEnter`)。
    oracle は 3 つ:`hevG`(評価型付け;[b-5] で (a) との結合帰納法から)、
    `hclorc`(shape 一致節の τt 節型付け輸送)、`hinstF`(双対スキームの
    インスタンス化 [b-3])—— 後 2 者は [b-6] のインスタンス輸送で放電する。 -/
theorem type_safety_b_at
    {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hevG : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    (hclorc : ∀ {ρm : Env} {cls : List Clause} {τm τt : Ty} {p : Pattern},
       ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm) →
       Unifiable τm τt → p.isClauseForm = true →
       ∃ Γm, EnvTyped SD SP SF Γm ρm ∧
         ∀ cl ∈ cls, ppShapeOK cl.1 p = true → ClauseTy SD SP SF Γm τt cl)
    (hinstF : ∀ {f : String} {sig : PatFunSig} {qs : List Pattern}
       {Γ : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty},
       List.find? (fun pr => pr.1 == f) SF = some (f, sig) →
       PatTy SD SP SF Γ Φ Δ₀ (.papp f qs) τp τt Δ' →
       ∃ duals Δfin,
         PatTys SD SP SF Γ Φ Δ₀ qs duals Δ' ∧
         (∀ pr ∈ duals, StructReaches pr.1 pr.2) ∧
         PatTy SD SP SF Γ (sig.params.zip duals) [] sig.body τp τt Δfin)
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
    | matcherPPFail hpc hppm hma' =>
        exact preserve_matcher_step hwfD hwfP hL hevG hclorc hpc
          (MAtom.matcherPPFail hpc hppm hma') hwt as has
    | matcherDPFail hpc hppm hpd hma' =>
        exact preserve_matcher_step hwfD hwfP hL hevG hclorc hpc
          (MAtom.matcherDPFail hpc hppm hpd hma') hwt as has
    | matcher hpc hppm hpd hevN hlist hvss hevM hms =>
        exact preserve_matcher_step hwfD hwfP hL hevG hclorc hpc
          (MAtom.matcher hpc hppm hpd hevN hlist hvss hevM hms) hwt as has
  case patfun =>
    intro S ρ θ f qs m v sig hfind hlen
    intro Γ Φ Δgoal _hno hwt s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    exact preserve_patfunEnter hwfD hSF hinstF hfind hlen hwt
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
      | mnode rem duals Γf Δθf Δfin Φf hj hnd hocc hq hforall hreachΦ hd1 hd2 hθf hinner =>
        have hwtIn : WTStateAt SD SP SF Γf Φf
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
          WTStack.cons (WTTree.mnode rem duals Γf Δθf' Δfin Φf hj hnd hocc' hq
            hforall hreachΦ hd1 hd2 hθf' hinner') hrest⟩
  case mvarpat =>
    intro S ρ θ y q m v Srest ρf θf piE hfind
    intro Γ Φ Δgoal _hno hwt s' hs'
    simp only [List.mem_singleton] at hs'
    subst hs'
    exact preserve_mnodeVarpat hwfD hfind hwt
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
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hevG : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    (hclorc : ∀ {ρm : Env} {cls : List Clause} {τm τt : Ty} {p : Pattern},
       ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm) →
       Unifiable τm τt → p.isClauseForm = true →
       ∃ Γm, EnvTyped SD SP SF Γm ρm ∧
         ∀ cl ∈ cls, ppShapeOK cl.1 p = true → ClauseTy SD SP SF Γm τt cl)
    (hinstF : ∀ {f : String} {sig : PatFunSig} {qs : List Pattern}
       {Γ' : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty},
       List.find? (fun pr => pr.1 == f) SF = some (f, sig) →
       PatTy SD SP SF Γ' Φ Δ₀ (.papp f qs) τp τt Δ' →
       ∃ duals Δfin,
         PatTys SD SP SF Γ' Φ Δ₀ qs duals Δ' ∧
         (∀ pr ∈ duals, StructReaches pr.1 pr.2) ∧
         PatTy SD SP SF Γ' (sig.params.zip duals) [] sig.body τp τt Δfin)
    {s : MState} {ss : List MState} {Δgoal : BindCtx}
    (hSigF : SigFWF SD SP SF Γ)
    (hstep : Step SF s ss)
    (hno : stackNoOr s.S = true)
    (hwt : WTState SD SP SF Γ s Δgoal) :
    ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal :=
  type_safety_b_at hwfD hwfP hL hevG hclorc hinstF
    (fun pr hpr => ⟨(hSigF pr hpr).linearity, (hSigF pr hpr).noOr,
      (hSigF pr hpr).paramsNodup⟩)
    hstep Γ [] Δgoal hno hwt

/-! ## 最終形:Theorem 5.6 (Type Safety) のパッケージ

(a)(b) を oracle 前提つきで束ねる。oracle は論文の証明規約の形式的
インターフェース:

* `hgen` — HM の一般化補題(§4.6 の rigidity 制限つき;Stage 2 = Algorithm W)。
* `hsiteReach` — site 双対導出の構造添字は fresh-leaf 構成(§4.2 の
  「independent fresh leaves」規約)。旧 hinit oracle はこれと
  `initial_atom_wt` で**完全放電**した。
* `hclorc` / `hinstF` — 値が持つ内在型付け(節型付け・記録本体導出)の
  使用点インスタンスへの輸送。論文 Notation 節「Reading the relations
  across a derivation」の prevailing-substitution 規約に対応([b-6])。
* `hevG` — 評価型付けの ∀ρ'∀Γ' 形。(b)→(a) 方向はこのパッケージで
  閉じている(`step_occs`+`type_safety_b_at`)が、(a)→(b) 方向
  (hevG 自身の放電)は (a) との結合帰納法 [b-5] の残項目。 -/

/-- match site の初期原子の整型(旧 hinit oracle の放電核):
    site スロットは σ = τp なので `slot_atom` の site 分岐一発。 -/
theorem initial_atom_wt {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    (hwfD : SigDWF SD)
    {p : Pattern} {v_m v_t : Value} {τp τt : Ty} {Δ : BindCtx}
    (hp : PatTy SD SP SF Γ [] [] p τp τt Δ)
    (hreach : StructReaches τp τt)
    (hm : ValueTy SD SP SF v_m (.slot τp τt))
    (hv : ValueTy SD SP SF v_t τt) :
    WTStack SD SP SF Γ [] [] [.atom ⟨p, v_m, v_t⟩] Δ :=
  WTStack.cons (slot_atom hwfD p hp hreach hm (.inr rfl) hv) WTStack.nil

/-- **Theorem 5.6 (Type Safety)**:評価の型保存 (a) とマッチング状態保存 (b)。
    oracle 前提はモジュール docstring と README のロードマップを参照。 -/
theorem type_safety {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    (hwfD : SigDWF SD) (hwfP : SigPWF SP) (hL : ListSigOK SD)
    (hSigF : SigFWF SD SP SF Γ)
    (hevG : ∀ {ρ' : Env} {Γ' : TyCtx} {e : Expr} {w : Value} {τ' : Ty},
       Eval SF ρ' e w → HasTy SD SP SF Γ' e τ' → ValueTy SD SP SF w τ')
    (hgen : ∀ {Γ' : TyCtx} {ρ' : Env} {e₁ : Expr} {v₁ : Value} {τ₁ : Ty}
       {L : List TyVar},
       Eval SF ρ' e₁ v₁ → EnvTyped SD SP SF Γ' ρ' → HasTy SD SP SF Γ' e₁ τ₁ →
       (∀ a ∈ L, a ∉ ftvCtx Γ') →
       ∀ τ', Scheme.Inst ⟨L, τ₁⟩ τ' → ValueTy SD SP SF v₁ τ')
    (hsiteReach : ∀ {Γ' : TyCtx} {p : Pattern} {τp τt : Ty} {Δ : BindCtx},
       PatTy SD SP SF Γ' [] [] p τp τt Δ → StructReaches τp τt)
    (hclorc : ∀ {ρm : Env} {cls : List Clause} {τm τt : Ty} {p : Pattern},
       ValueTy SD SP SF (.matcherV ρm cls) (.matcher τm) →
       Unifiable τm τt → p.isClauseForm = true →
       ∃ Γm, EnvTyped SD SP SF Γm ρm ∧
         ∀ cl ∈ cls, ppShapeOK cl.1 p = true → ClauseTy SD SP SF Γm τt cl)
    (hinstF : ∀ {f : String} {sig : PatFunSig} {qs : List Pattern}
       {Γ' : TyCtx} {Φ : PatParamCtx} {Δ₀ Δ' : BindCtx} {τp τt : Ty},
       List.find? (fun pr => pr.1 == f) SF = some (f, sig) →
       PatTy SD SP SF Γ' Φ Δ₀ (.papp f qs) τp τt Δ' →
       ∃ duals Δfin,
         PatTys SD SP SF Γ' Φ Δ₀ qs duals Δ' ∧
         (∀ pr ∈ duals, StructReaches pr.1 pr.2) ∧
         PatTy SD SP SF Γ' (sig.params.zip duals) [] sig.body τp τt Δfin) :
    (∀ {ρ : Env} {e : Expr} {v : Value} {Γ' : TyCtx} {τ : Ty},
       Eval SF ρ e v → EnvTyped SD SP SF Γ' ρ → HasTy SD SP SF Γ' e τ →
       ValueTy SD SP SF v τ) ∧
    (∀ {s : MState} {ss : List MState} {Δgoal : BindCtx},
       Step SF s ss → stackNoOr s.S = true → WTState SD SP SF Γ s Δgoal →
       ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal) := by
  have hSF' : ∀ pr ∈ SF, pr.2.body.embedVars = pr.2.params ∧
      pr.2.body.noEmbedInOr = true ∧ pr.2.params.Nodup := fun pr hpr =>
    ⟨(hSigF pr hpr).linearity, (hSigF pr hpr).noOr, (hSigF pr hpr).paramsNodup⟩
  constructor
  · intro ρ e v Γ' τ hev hρ hty
    refine type_safety_a hwfD hL ?_ hgen ?_ hev hρ hty
    · intro Γ'' Δ s ss hstep hno hwt s' hs'
      exact ⟨(step_occs hSF' hstep hno s' hs').2,
        type_safety_b_at hwfD hwfP hL hevG hclorc hinstF hSF' hstep
          Γ'' [] Δ hno hwt s' hs'⟩
    · intro Γ'' p v_m v_t τ_p τ_t Δ hp hm hv
      exact initial_atom_wt hwfD hp (hsiteReach hp) hm hv
  · intro s ss Δgoal hstep hno hwt
    exact type_safety_b_at hwfD hwfP hL hevG hclorc hinstF hSF' hstep
      Γ [] Δgoal hno hwt

end TypePM