import TypePM.WellTyped

/-!
# 正準形補題 (Lem 5.5 Progress の前提層) — 全て証明済み

* `vshape_of_valueTy` — 値型付けから形状型付けへ
  (Def 4.2(1c) arm exhaustiveness の量化域 `VShape` が実際の整型値を覆う)
* `canonical_prod` — 積型の値はタプル(Σ_D 整形性の下で)
* 形状保存:`applyTSList_length`・`renamesTo_*`・`oneWay_*`
  (双対検査の構造条件が something/積マッチャーを構成子パターンで
  却下する論証の機械化;付録 C.2 の「構造前提が裸変数マッチャーを排除」)
-/

namespace TypePM

/-! ## VShape は ValueTy を覆う -/

theorem vshape_of_valueTy {SD : SigD} {SP : SigP} {SF : SigF} :
    ∀ {v : Value} {τ : Ty}, ValueTy SD SP SF v τ → VShape SD v τ := by
  intro v τ h
  induction h with
  | lit => exact VShape.lit
  | ctor hfind hlen hall ih =>
      exact VShape.ctor hfind (by simpa using hlen) fun pr hpr => ih pr hpr
  | tuple hlen hall ih =>
      exact VShape.tuple hlen fun pr hpr => ih pr hpr
  | closure Γ _ _ _ _ => exact VShape.closure
  | matcherV Γm _ _ _ => exact VShape.matcherV
  | something => exact VShape.something
  | prodMatcher _ _ _ => exact VShape.matcherTuple
  | slotV _ _ _ _ _ => exact VShape.slotAny
  | prodSlot _ _ _ => exact VShape.slotAny

/-! ## 正準形 -/

/-- 積型の値はタプルで、成分ごとに型付く(Σ_D 整形性の下で)。 -/
theorem canonical_prod {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) {v : Value} {τs : List Ty}
    (h : ValueTy SD SP SF v (.prod τs)) :
    ∃ vs, v = Value.tuple vs ∧ vs.length = τs.length ∧
      ∀ pr ∈ vs.zip τs, ValueTy SD SP SF pr.1 pr.2 := by
  generalize hτ : (Ty.prod τs : Ty) = τx at h
  cases h with
  | lit => cases hτ
  | ctor hfind hlen hall =>
      exfalso
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at hτ
      simp [Ty.instSig, Ty.applyTS] at hτ
  | tuple hlen hall =>
      injection hτ with h1
      subst h1
      exact ⟨_, rfl, hlen, hall⟩
  | closure Γ' _ _ _ _ => cases hτ
  | matcherV _ _ _ _ => cases hτ
  | something => cases hτ
  | prodMatcher _ _ => cases hτ
  | slotV _ _ _ _ => cases hτ
  | prodSlot _ _ => cases hτ

/-! ## 形状保存(代入・改名・one-way) -/

theorem applyTSList_length (θ : TySubst) : ∀ (l : List Ty),
    (applyTSList θ l).length = l.length
  | [] => rfl
  | t :: l => by simp [applyTSList, applyTSList_length θ l]

/-- 改名は変数を変数に写す -/
theorem renamesTo_var {a : TyVar} {τ' : Ty} (h : RenamesTo (.var a) τ') :
    ∃ b, τ' = .var b := by
  obtain ⟨r, -, hr⟩ := h
  exact ⟨r a, hr.symm⟩

/-- 改名は積を(同数の)積に写す -/
theorem renamesTo_prod {τs : List Ty} {τ' : Ty} (h : RenamesTo (.prod τs) τ') :
    ∃ τs', τ' = .prod τs' ∧ τs'.length = τs.length := by
  obtain ⟨r, -, hr⟩ := h
  have hlen : ∀ (l : List Ty), (applyRenList r l).length = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih => simp [applyRenList, ih]
  exact ⟨applyRenList r τs, hr.symm ▸ by simp [Ty.applyRen], hlen τs⟩

/-- one-way instance は data 頭を保つ(構造条件が裸変数マッチャーを却下する核) -/
theorem oneWay_data {n : String} {l : List Ty} {τm : Ty}
    (h : OneWay (.data n l) τm) :
    ∃ l', τm = .data n l' ∧ l'.length = l.length := by
  obtain ⟨θ, -, hθ⟩ := h
  refine ⟨applyTSList θ l, ?_, applyTSList_length θ l⟩
  rw [← hθ]
  simp [Ty.applyTS]

/-- one-way instance は積頭を保つ -/
theorem oneWay_prod {l : List Ty} {τm : Ty}
    (h : OneWay (.prod l) τm) :
    ∃ l', τm = .prod l' ∧ l'.length = l.length := by
  obtain ⟨θ, -, hθ⟩ := h
  refine ⟨applyTSList θ l, ?_, applyTSList_length θ l⟩
  rw [← hθ]
  simp [Ty.applyTS]

/-- 構成子頭の構造添字は something(裸変数マッチャー)を却下する
    (付録 C.2:「構造前提 τm' ⊑ τp が裸変数マッチャーを排除」の機械化)。 -/
theorem something_rejected_at_data {n : String} {l : List Ty} {τm : Ty}
    {a : TyVar} (hren : RenamesTo (.var a) τm) (how : OneWay (.data n l) τm) :
    False := by
  obtain ⟨b, rfl⟩ := renamesTo_var hren
  obtain ⟨l', hl', -⟩ := oneWay_data how
  cases hl'

/-- 構成子頭の構造添字は積マッチャーも却下する -/
theorem prod_rejected_at_data {n : String} {l : List Ty} {τs : List Ty} {τm : Ty}
    (hren : RenamesTo (.prod τs) τm) (how : OneWay (.data n l) τm) :
    False := by
  obtain ⟨τs', hτs', -⟩ := renamesTo_prod hren
  obtain ⟨l', hl', -⟩ := oneWay_data how
  subst hτs'
  cases hl'

/-- 積頭の構造添字は something を却下する(MS-TUPLE の場合分けの核) -/
theorem something_rejected_at_prod {l : List Ty} {τm : Ty}
    {a : TyVar} (hren : RenamesTo (.var a) τm) (how : OneWay (.prod l) τm) :
    False := by
  obtain ⟨b, rfl⟩ := renamesTo_var hren
  obtain ⟨l', hl', -⟩ := oneWay_prod how
  cases hl'

/-! ## 単一化可能性の形状補題(MS-TUPLE の長さ整合に使用) -/

/-- 積型と単一化可能な「値の型」(ValueTy が結論しうる型)は同数の積型
    (Σ_D 整形性の下で)。 -/
theorem valueTy_unifiable_prod {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) {v : Value} {τ : Ty} {τts : List Ty}
    (hv : ValueTy SD SP SF v τ) (huni : Unifiable (.prod τts) τ) :
    ∃ τs', τ = .prod τs' ∧ τs'.length = τts.length := by
  obtain ⟨θ, hθ⟩ := huni
  -- θ(prod τts) は積;τ の applyTS が積になるのは τ 自身が積のときのみ
  -- (ValueTy の結論しうる型は var でない)
  cases hv with
  | lit => simp [Ty.applyTS] at hθ
  | ctor hfind hlen hall =>
      exfalso
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at hθ
      simp [Ty.instSig, Ty.applyTS] at hθ
  | tuple hlen hall =>
      rename_i vs τs
      refine ⟨τs, rfl, ?_⟩
      simp only [Ty.applyTS, Ty.prod.injEq] at hθ
      have := congrArg List.length hθ
      simp only [applyTSList_length] at this
      exact this.symm
  | closure Γ' _ _ _ _ => simp [Ty.applyTS] at hθ
  | matcherV _ _ _ _ => simp [Ty.applyTS] at hθ
  | something => simp [Ty.applyTS] at hθ
  | prodMatcher _ _ => simp [Ty.applyTS] at hθ
  | slotV _ _ _ _ => simp [Ty.applyTS] at hθ
  | prodSlot _ _ => simp [Ty.applyTS] at hθ

end TypePM
