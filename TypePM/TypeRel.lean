import TypePM.Syntax

/-!
# 型上の関係 (論文 §4 冒頭「Notation」・§5.2)

* 型代入と自由型変数
* 単一化可能性 τ ~ τ' (存在する共通インスタンス;伝播なしの検査)
* one-way instance τ_m' ⊑ τ_p (双対検査の構造条件;
  定義は τ ⊑_θ τ' ⟺ dom θ ⊆ ftv τ' ∧ θ(τ') = τ、
  すなわち **マッチャー側がパターンの構造添字のインスタンス**)
* 変数改名(fresh_rename の宣言的対応物)
* シグネチャのインスタンス化

Lemma 5.2 (one-way matching uniqueness) の一意性部分はここで証明済み。
-/

namespace TypePM

/-! ## 型代入 -/

abbrev TySubst := List (TyVar × Ty)

/-- 代入の変数への適用(束縛が無ければ変数のまま) -/
def TySubst.appVar (θ : TySubst) (a : TyVar) : Ty :=
  match List.find? (fun p => p.1 == a) θ with
  | some (_, t) => t
  | none        => .var a

def TySubst.dom (θ : TySubst) : List TyVar := θ.map (·.1)

mutual
/-- 型への代入適用 -/
def Ty.applyTS (θ : TySubst) : Ty → Ty
  | .var a      => θ.appVar a
  | .int        => .int
  | .bool       => .bool
  | .data n ts  => .data n (applyTSList θ ts)
  | .prod ts    => .prod (applyTSList θ ts)
  | .fn t₁ t₂   => .fn (t₁.applyTS θ) (t₂.applyTS θ)
  | .matcher t  => .matcher (t.applyTS θ)
  | .slot t₁ t₂ => .slot (t₁.applyTS θ) (t₂.applyTS θ)

def applyTSList (θ : TySubst) : List Ty → List Ty
  | []      => []
  | t :: ts => t.applyTS θ :: applyTSList θ ts
end

mutual
/-- 自由型変数 -/
def Ty.ftv : Ty → List TyVar
  | .var a      => [a]
  | .int        => []
  | .bool       => []
  | .data _ ts  => ftvList ts
  | .prod ts    => ftvList ts
  | .fn t₁ t₂   => t₁.ftv ++ t₂.ftv
  | .matcher t  => t.ftv
  | .slot t₁ t₂ => t₁.ftv ++ t₂.ftv

def ftvList : List Ty → List TyVar
  | []      => []
  | t :: ts => t.ftv ++ ftvList ts
end

/-! ## 型関係 -/

/-- 単一化可能性 τ ~ τ' (∃θ. θτ = θτ'、「共通インスタンスを持つ」;§4 Notation)。
    Matcher rigidity (§4.6) は推論アルゴリズム側の制限であり、
    宣言的関係としては通常の単一化可能性を用いる(README 設計判断)。 -/
def Unifiable (τ τ' : Ty) : Prop :=
  ∃ θ : TySubst, τ.applyTS θ = τ'.applyTS θ

/-- one-way instance:`OneWayAt θ τp τm` は τm ⊑_θ τp、
    すなわち dom θ ⊆ ftv τp かつ θ(τp) = τm(マッチャー型はパターン構造添字のインスタンス)。 -/
def OneWayAt (θ : TySubst) (τp τm : Ty) : Prop :=
  (∀ a ∈ θ.dom, a ∈ τp.ftv) ∧ τp.applyTS θ = τm

/-- τm ⊑ τp (∃θ. τm ⊑_θ τp) -/
def OneWay (τp τm : Ty) : Prop := ∃ θ, OneWayAt θ τp τm

mutual
/-- 変数改名の適用 -/
def Ty.applyRen (r : TyVar → TyVar) : Ty → Ty
  | .var a      => .var (r a)
  | .int        => .int
  | .bool       => .bool
  | .data n ts  => .data n (applyRenList r ts)
  | .prod ts    => .prod (applyRenList r ts)
  | .fn t₁ t₂   => .fn (t₁.applyRen r) (t₂.applyRen r)
  | .matcher t  => .matcher (t.applyRen r)
  | .slot t₁ t₂ => .slot (t₁.applyRen r) (t₂.applyRen r)

def applyRenList (r : TyVar → TyVar) : List Ty → List Ty
  | []      => []
  | t :: ts => t.applyRen r :: applyRenList r ts
end

/-- τ' が τ の(単射)変数改名である:fresh_rename(τ) の宣言的対応物。 -/
def RenamesTo (τ τ' : Ty) : Prop :=
  ∃ r : TyVar → TyVar, (∀ a b, r a = r b → a = b) ∧ τ.applyRen r = τ'

/-- 「同じ頭・新しい葉」(PP-Con の premise、fresh instantiation):
    構造を保ち変数葉のみ改名した型。改名として定式化する。 -/
def FreshLike (τ τ' : Ty) : Prop := RenamesTo τ τ'

/-! ## シグネチャのインスタンス化 -/

/-- 束縛変数 0..n-1 を ts で置換(シグネチャ/スキームのインスタンス化) -/
def Ty.instSig (ts : List Ty) (τ : Ty) : Ty :=
  τ.applyTS ((List.range ts.length).zip ts)

/-- スキームのインスタンス関係:σ ≥ τ -/
def Scheme.Inst (σ : Scheme) (τ : Ty) : Prop :=
  ∃ θ : TySubst, (∀ a ∈ θ.dom, a ∈ σ.binders) ∧ σ.body.applyTS θ = τ

/-! ## Lemma 5.2:one-way matching の一意性

witness θ は(τp の自由変数上で)一意。証明は τp の構造帰納法。 -/

mutual
theorem applyTS_eq_on_ftv (θ₁ θ₂ : TySubst) (τ : Ty)
    (h : τ.applyTS θ₁ = τ.applyTS θ₂) :
    ∀ a ∈ τ.ftv, θ₁.appVar a = θ₂.appVar a := by
  cases τ with
  | var a =>
      intro b hb
      simp [Ty.ftv] at hb
      subst hb
      simpa [Ty.applyTS] using h
  | int => intro a ha; simp [Ty.ftv] at ha
  | bool => intro a ha; simp [Ty.ftv] at ha
  | data n ts =>
      intro a ha
      simp only [Ty.applyTS, Ty.data.injEq] at h
      exact applyTSList_eq_on_ftv θ₁ θ₂ ts h.2 a (by simpa [Ty.ftv] using ha)
  | prod ts =>
      intro a ha
      simp only [Ty.applyTS, Ty.prod.injEq] at h
      exact applyTSList_eq_on_ftv θ₁ θ₂ ts h a (by simpa [Ty.ftv] using ha)
  | fn t₁ t₂ =>
      intro a ha
      simp only [Ty.applyTS, Ty.fn.injEq] at h
      simp only [Ty.ftv, List.mem_append] at ha
      rcases ha with ha | ha
      · exact applyTS_eq_on_ftv θ₁ θ₂ t₁ h.1 a ha
      · exact applyTS_eq_on_ftv θ₁ θ₂ t₂ h.2 a ha
  | matcher t =>
      intro a ha
      simp only [Ty.applyTS, Ty.matcher.injEq] at h
      exact applyTS_eq_on_ftv θ₁ θ₂ t h a (by simpa [Ty.ftv] using ha)
  | slot t₁ t₂ =>
      intro a ha
      simp only [Ty.applyTS, Ty.slot.injEq] at h
      simp only [Ty.ftv, List.mem_append] at ha
      rcases ha with ha | ha
      · exact applyTS_eq_on_ftv θ₁ θ₂ t₁ h.1 a ha
      · exact applyTS_eq_on_ftv θ₁ θ₂ t₂ h.2 a ha

theorem applyTSList_eq_on_ftv (θ₁ θ₂ : TySubst) (ts : List Ty)
    (h : applyTSList θ₁ ts = applyTSList θ₂ ts) :
    ∀ a ∈ ftvList ts, θ₁.appVar a = θ₂.appVar a := by
  cases ts with
  | nil => intro a ha; simp [ftvList] at ha
  | cons t ts =>
      intro a ha
      simp only [applyTSList, List.cons.injEq] at h
      simp only [ftvList, List.mem_append] at ha
      rcases ha with ha | ha
      · exact applyTS_eq_on_ftv θ₁ θ₂ t h.1 a ha
      · exact applyTSList_eq_on_ftv θ₁ θ₂ ts h.2 a ha
end

/-- **Lemma 5.2 (One-way matching uniqueness、一意性部分)**:
    τm ⊑_θ₁ τp かつ τm ⊑_θ₂ τp ならば θ₁ と θ₂ は τp の全自由変数上で一致する。
    (計算可能性 O(|τp|+|τm|) は `Exec.lean` の `matchOneWay` が対応。) -/
theorem oneWay_unique {θ₁ θ₂ : TySubst} {τp τm : Ty}
    (h₁ : OneWayAt θ₁ τp τm) (h₂ : OneWayAt θ₂ τp τm) :
    ∀ a ∈ τp.ftv, θ₁.appVar a = θ₂.appVar a :=
  applyTS_eq_on_ftv θ₁ θ₂ τp (h₁.2.trans h₂.2.symm)

/-! ## 代入適用の合同性(逆向き:自由変数上の一致 → 適用結果の一致) -/

mutual
theorem applyTS_congr : ∀ (τ : Ty) {θ θ' : TySubst},
    (∀ a ∈ τ.ftv, θ.appVar a = θ'.appVar a) → τ.applyTS θ = τ.applyTS θ'
  | .var a, θ, θ', h => h a (by simp [Ty.ftv])
  | .int, _, _, _ => rfl
  | .bool, _, _, _ => rfl
  | .data n ts, θ, θ', h => by
      simp only [Ty.applyTS]
      exact congrArg (Ty.data n)
        (applyTSList_congr ts fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .prod ts, θ, θ', h => by
      simp only [Ty.applyTS]
      exact congrArg Ty.prod
        (applyTSList_congr ts fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .fn t₁ t₂, θ, θ', h => by
      simp only [Ty.applyTS]
      rw [applyTS_congr t₁ fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_congr t₂ fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]
  | .matcher t, θ, θ', h => by
      simp only [Ty.applyTS]
      rw [applyTS_congr t fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .slot t₁ t₂, θ, θ', h => by
      simp only [Ty.applyTS]
      rw [applyTS_congr t₁ fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_congr t₂ fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]

theorem applyTSList_congr : ∀ (ts : List Ty) {θ θ' : TySubst},
    (∀ a ∈ ftvList ts, θ.appVar a = θ'.appVar a) → applyTSList θ ts = applyTSList θ' ts
  | [], _, _, _ => rfl
  | t :: ts, θ, θ', h => by
      simp only [applyTSList]
      rw [applyTS_congr t fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inl ha),
          applyTSList_congr ts fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inr ha)]
end

end TypePM

