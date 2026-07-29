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

/-- リスト中の型の自由変数はリスト全体の自由変数(要素帰納) -/
theorem mem_ftvList_of_mem : ∀ {ts : List Ty} {τ : Ty}, τ ∈ ts →
    ∀ {a}, a ∈ τ.ftv → a ∈ ftvList ts
  | t :: ts, τ, hmem, a, ha => by
      simp only [ftvList, List.mem_append]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact .inl ha
      · exact .inr (mem_ftvList_of_mem hmem ha)

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

/-! ## 到達不変量 StructReaches とその支持層(§4.2 fresh-leaf 構成の宣言的帰結)

`StructReaches τp τt`:構造添字 τp は標的 τt の**任意の**改名コピーへ ⊑ できる。
論文 §4.2 の「構造添字は同じコンストラクタ頭・fresh な変数葉で作る」構成なら
自動的に成り立つ性質を宣言的不変量として切り出したもの(WT-ATOM の premise)。
MS-MATCHER の後続原子再建で、抽出パターンの構造添字を節スロットの構造注釈
(= 標的位置の改名コピー、PP-Con refresh)へ ⊑ で繋ぐのに使う。 -/

def StructReaches (τp τt : Ty) : Prop :=
  ∀ τr, RenamesTo τt τr → OneWay τp τr

/-- find? はリスト連結の左を優先する(左が some) -/
theorem list_find?_append_some {α} {f : α → Bool} : ∀ {l₁ l₂ : List α} {a : α},
    List.find? f l₁ = some a → List.find? f (l₁ ++ l₂) = some a
  | [], _, _, h => nomatch h
  | b :: l₁, l₂, a, h => by
      rw [List.cons_append]
      simp only [List.find?] at h ⊢
      cases hb : f b
      · rw [hb] at h
        exact list_find?_append_some h
      · rw [hb] at h
        exact h

/-- find? はリスト連結の左を優先する(左が none なら右へ) -/
theorem list_find?_append_none {α} {f : α → Bool} : ∀ {l₁ l₂ : List α},
    List.find? f l₁ = none → List.find? f (l₁ ++ l₂) = List.find? f l₂
  | [], _, _ => rfl
  | b :: l₁, l₂, h => by
      rw [List.cons_append]
      simp only [List.find?] at h ⊢
      cases hb : f b
      · rw [hb] at h
        exact list_find?_append_none h
      · rw [hb] at h
        exact nomatch h

/-- 鍵 a のエントリを全て通すフィルタは、鍵 a の find? を変えない -/
theorem find?_key_filter {l : List (TyVar × Ty)} {q : TyVar × Ty → Bool} {a : TyVar}
    (hq : ∀ pr ∈ l, pr.1 = a → q pr = true) :
    List.find? (fun pr => pr.1 == a) (l.filter q)
      = List.find? (fun pr => pr.1 == a) l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      have ih' := ih (fun pr hpr => hq pr (List.mem_cons_of_mem _ hpr))
      cases hkey : ((hd.1 : TyVar) == a) with
      | true =>
          have hpass := hq hd (List.mem_cons_self ..) (by simpa using hkey)
          simp [List.filter_cons, hpass, List.find?, hkey]
      | false =>
          cases hqh : q hd with
          | true => simp [List.filter_cons, hqh, List.find?, hkey, ih']
          | false => simp [List.filter_cons, hqh, List.find?, hkey, ih']

/-- ftv 制限フィルタは ftv 上で appVar を変えない -/
theorem appVar_filter_ftv {θ : TySubst} {fv : List TyVar} {a : TyVar}
    (ha : a ∈ fv) :
    TySubst.appVar (θ.filter (fun pr => decide (pr.1 ∈ fv))) a = θ.appVar a := by
  unfold TySubst.appVar
  rw [find?_key_filter]
  intro pr _ hkey
  subst hkey
  simpa using ha

/-- **⊑ の witness パッケージ**:任意の代入の適用等式から、witness を
    構造添字の自由変数に制限して dom 条件(Notation の ⊑ 定義)を満たす。
    dom 制限の受け渡しはこの補題に一元化する(利用側は等式だけ示せばよい)。 -/
theorem oneWay_of_applyTS {τp τm : Ty} {θ : TySubst}
    (h : τp.applyTS θ = τm) : OneWay τp τm := by
  refine ⟨θ.filter (fun pr => decide (pr.1 ∈ τp.ftv)), ?_, ?_⟩
  · intro a ha
    simp only [TySubst.dom, List.mem_map] at ha
    obtain ⟨pr, hpr, rfl⟩ := ha
    have := (List.mem_filter.mp hpr).2
    simpa using this
  · rw [applyTS_congr _ (fun a ha => appVar_filter_ftv ha)]
    exact h

/-- 鍵を保ち値を写す map と find? の可換性 -/
theorem find?_map_val {θ : TySubst} {f : Ty → Ty} {a : TyVar} :
    List.find? (fun pr => pr.1 == a) (θ.map (fun pr => (pr.1, f pr.2)))
      = (List.find? (fun pr => pr.1 == a) θ).map (fun pr => (pr.1, f pr.2)) := by
  induction θ with
  | nil => rfl
  | cons hd tl ih =>
      cases hkey : ((hd.1 : TyVar) == a) with
      | true => simp [List.find?, hkey]
      | false => simp [List.find?, hkey, ih]

/-- 合成代入:全変数上で θ₂ ∘ θ₁ と一致する有限代入(左が θ₁ の写像で右を遮蔽)。
    dom 制限は持たない(⊑ の witness 化は `oneWay_of_applyTS` が担う)。 -/
def TySubst.compOn (θ₁ θ₂ : TySubst) : TySubst :=
  θ₁.map (fun pr => (pr.1, pr.2.applyTS θ₂)) ++ θ₂

theorem appVar_compOn {θ₁ θ₂ : TySubst} {a : TyVar} :
    (TySubst.compOn θ₁ θ₂).appVar a = (θ₁.appVar a).applyTS θ₂ := by
  unfold TySubst.compOn TySubst.appVar
  cases hfind : List.find? (fun pr => pr.1 == a) θ₁ with
  | some pr =>
      have hmap : List.find? (fun pr => pr.1 == a)
          (θ₁.map (fun pr => (pr.1, pr.2.applyTS θ₂))) = some (pr.1, pr.2.applyTS θ₂) := by
        rw [find?_map_val, hfind]; rfl
      rw [list_find?_append_some hmap]
  | none =>
      have hmap : List.find? (fun pr => pr.1 == a)
          (θ₁.map (fun pr => (pr.1, pr.2.applyTS θ₂))) = none := by
        rw [find?_map_val, hfind]; rfl
      rw [list_find?_append_none hmap]
      simp only [Ty.applyTS, TySubst.appVar]

/-! ### 二重適用の pointwise 転送 -/

mutual
/-- (τ[θ₁])[θ₂] は、τ の自由変数上の合成挙動だけで決まる -/
theorem applyTS_applyTS_pointwise : ∀ (τ : Ty) {θ₁ θ₂ θ₃ : TySubst},
    (∀ a ∈ τ.ftv, (θ₁.appVar a).applyTS θ₂ = θ₃.appVar a) →
    (τ.applyTS θ₁).applyTS θ₂ = τ.applyTS θ₃
  | .var a, θ₁, θ₂, θ₃, h => h a (by simp [Ty.ftv])
  | .int, _, _, _, _ => rfl
  | .bool, _, _, _, _ => rfl
  | .data n ts, θ₁, θ₂, θ₃, h => by
      simp only [Ty.applyTS]
      exact congrArg (Ty.data n) (applyTSList_applyTS_pointwise ts
        fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .prod ts, θ₁, θ₂, θ₃, h => by
      simp only [Ty.applyTS]
      exact congrArg Ty.prod (applyTSList_applyTS_pointwise ts
        fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .fn t₁ t₂, θ₁, θ₂, θ₃, h => by
      simp only [Ty.applyTS]
      rw [applyTS_applyTS_pointwise t₁
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_applyTS_pointwise t₂
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]
  | .matcher t, θ₁, θ₂, θ₃, h => by
      simp only [Ty.applyTS]
      rw [applyTS_applyTS_pointwise t fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .slot t₁ t₂, θ₁, θ₂, θ₃, h => by
      simp only [Ty.applyTS]
      rw [applyTS_applyTS_pointwise t₁
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_applyTS_pointwise t₂
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]

theorem applyTSList_applyTS_pointwise : ∀ (ts : List Ty) {θ₁ θ₂ θ₃ : TySubst},
    (∀ a ∈ ftvList ts, (θ₁.appVar a).applyTS θ₂ = θ₃.appVar a) →
    applyTSList θ₂ (applyTSList θ₁ ts) = applyTSList θ₃ ts
  | [], _, _, _, _ => rfl
  | t :: ts, θ₁, θ₂, θ₃, h => by
      simp only [applyTSList]
      rw [applyTS_applyTS_pointwise t
            fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inl ha),
          applyTSList_applyTS_pointwise ts
            fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inr ha)]
end

mutual
/-- (τ[θ₁])[θ₂] = (τ[θ₃])⟨r⟩ も pointwise 挙動から従う(改名との混合版) -/
theorem applyTS_applyRen_pointwise : ∀ (τ : Ty) {θ₁ θ₂ θ₃ : TySubst} {r : TyVar → TyVar},
    (∀ a ∈ τ.ftv, (θ₁.appVar a).applyTS θ₂ = (θ₃.appVar a).applyRen r) →
    (τ.applyTS θ₁).applyTS θ₂ = (τ.applyTS θ₃).applyRen r
  | .var a, θ₁, θ₂, θ₃, r, h => h a (by simp [Ty.ftv])
  | .int, _, _, _, _, _ => rfl
  | .bool, _, _, _, _, _ => rfl
  | .data n ts, θ₁, θ₂, θ₃, r, h => by
      simp only [Ty.applyTS, Ty.applyRen]
      exact congrArg (Ty.data n) (applyTSList_applyRen_pointwise ts
        fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .prod ts, θ₁, θ₂, θ₃, r, h => by
      simp only [Ty.applyTS, Ty.applyRen]
      exact congrArg Ty.prod (applyTSList_applyRen_pointwise ts
        fun a ha => h a (by simpa [Ty.ftv] using ha))
  | .fn t₁ t₂, θ₁, θ₂, θ₃, r, h => by
      simp only [Ty.applyTS, Ty.applyRen]
      rw [applyTS_applyRen_pointwise t₁
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_applyRen_pointwise t₂
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]
  | .matcher t, θ₁, θ₂, θ₃, r, h => by
      simp only [Ty.applyTS, Ty.applyRen]
      rw [applyTS_applyRen_pointwise t fun a ha => h a (by simpa [Ty.ftv] using ha)]
  | .slot t₁ t₂, θ₁, θ₂, θ₃, r, h => by
      simp only [Ty.applyTS, Ty.applyRen]
      rw [applyTS_applyRen_pointwise t₁
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inl ha),
          applyTS_applyRen_pointwise t₂
            fun a ha => h a (by simp [Ty.ftv, List.mem_append]; exact .inr ha)]

theorem applyTSList_applyRen_pointwise : ∀ (ts : List Ty) {θ₁ θ₂ θ₃ : TySubst} {r : TyVar → TyVar},
    (∀ a ∈ ftvList ts, (θ₁.appVar a).applyTS θ₂ = (θ₃.appVar a).applyRen r) →
    applyTSList θ₂ (applyTSList θ₁ ts) = applyRenList r (applyTSList θ₃ ts)
  | [], _, _, _, _, _ => rfl
  | t :: ts, θ₁, θ₂, θ₃, r, h => by
      simp only [applyTSList, applyRenList]
      rw [applyTS_applyRen_pointwise t
            fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inl ha),
          applyTSList_applyRen_pointwise ts
            fun a ha => h a (by simp [ftvList, List.mem_append]; exact .inr ha)]
end

/-- **⊑ の推移律**(合成代入 compOn による;Lem 5.4 強化と後続原子再建で使用) -/
theorem oneWay_trans {A B C : Ty} (h₁ : OneWay A B) (h₂ : OneWay B C) :
    OneWay A C := by
  obtain ⟨θ₁, -, he₁⟩ := h₁
  obtain ⟨θ₂, -, he₂⟩ := h₂
  refine oneWay_of_applyTS (θ := TySubst.compOn θ₁ θ₂) ?_
  calc A.applyTS (TySubst.compOn θ₁ θ₂)
      = (A.applyTS θ₁).applyTS θ₂ :=
        (applyTS_applyTS_pointwise A fun _ _ => appVar_compOn.symm).symm
    _ = C := by rw [he₁, he₂]

/-! ### 到達不変量の位置分解 -/

/-- map の等式から要素ごとの等式へ -/
theorem map_eq_map_forall {α β} {f g : α → β} : ∀ {l : List α},
    l.map f = l.map g → ∀ x ∈ l, f x = g x
  | [], _, x, hx => nomatch hx
  | a :: l, h, x, hx => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact map_eq_map_forall h.2 x hx

theorem applyTSList_eq_map {θ : TySubst} : ∀ {ts : List Ty},
    applyTSList θ ts = ts.map (Ty.applyTS θ)
  | [] => rfl
  | t :: ts => by simp [applyTSList, applyTSList_eq_map]

theorem applyRenList_eq_map {r : TyVar → TyVar} : ∀ {ts : List Ty},
    applyRenList r ts = ts.map (Ty.applyRen r)
  | [] => rfl
  | t :: ts => by simp [applyRenList, applyRenList_eq_map]

/-- **到達不変量の instSig 分解**(PAT-CON の位置分解)。
    Def 4.1 の整形性(res = data n (var 0 … var (np−1))、引数の型変数 < np)
    のもとで、結果型での到達から各引数位置での到達を得る。 -/
theorem structReaches_instSig {ss ts : List Ty} {np : Nat} {n : String}
    {res : Ty} (hres : res = .data n ((List.range np).map .var))
    (h : StructReaches (Ty.instSig ss res) (Ty.instSig ts res)) :
    ∀ {τa : Ty}, (∀ a ∈ τa.ftv, a < np) →
    StructReaches (Ty.instSig ss τa) (Ty.instSig ts τa) := by
  intro τa hargs τr ⟨r, hinj, hren⟩
  obtain ⟨θ, hdom, happ⟩ := h ((Ty.instSig ts res).applyRen r) ⟨r, hinj, rfl⟩
  subst hres
  simp only [Ty.instSig, Ty.applyTS, Ty.applyRen] at happ
  injection happ with _ hlist
  rw [applyTSList_eq_map, applyTSList_eq_map, applyTSList_eq_map,
    applyRenList_eq_map] at hlist
  have h2 : List.map (fun i => Ty.applyTS θ
        (Ty.applyTS ((List.range ss.length).zip ss) (Ty.var i))) (List.range np)
      = List.map (fun i => Ty.applyRen r
        (Ty.applyTS ((List.range ts.length).zip ts) (Ty.var i))) (List.range np) := by
    simpa [List.map_map, Function.comp] using hlist
  have hstar : ∀ i, i < np →
      (Ty.applyTS θ (Ty.applyTS ((List.range ss.length).zip ss) (.var i)))
        = (Ty.applyRen r (Ty.applyTS ((List.range ts.length).zip ts) (.var i))) := by
    intro i hi
    exact map_eq_map_forall h2 i (List.mem_range.mpr hi)
  rw [← hren]
  apply oneWay_of_applyTS (θ := θ)
  show (τa.applyTS ((List.range ss.length).zip ss)).applyTS θ
    = (τa.applyTS ((List.range ts.length).zip ts)).applyRen r
  exact applyTS_applyRen_pointwise τa fun a ha => hstar a (hargs a ha)

/-- 変数構造添字は任意の型へ到達する(fresh-leaf 構成の葉ケース) -/
theorem structReaches_var {a : TyVar} {τ : Ty} : StructReaches (.var a) τ := by
  intro τr _
  refine ⟨[(a, τr)], ?_, ?_⟩
  · intro b hb
    simp only [TySubst.dom, List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    simp [Ty.ftv]
  · simp [Ty.applyTS, TySubst.appVar, List.find?]

/-- **到達不変量の積分解**(PAT-TUPLE の位置分解) -/
theorem structReaches_prod {as bs : List Ty}
    (h : StructReaches (.prod as) (.prod bs)) :
    ∀ {i : Nat} (hia : i < as.length) (hib : i < bs.length),
    StructReaches as[i] bs[i] := by
  intro i hia hib τr ⟨r, hinj, hren⟩
  obtain ⟨θ, hdom, happ⟩ := h ((Ty.prod bs).applyRen r) ⟨r, hinj, rfl⟩
  simp only [Ty.applyTS, Ty.applyRen] at happ
  injection happ with hlist
  rw [applyTSList_eq_map, applyRenList_eq_map] at hlist
  have hi' : i < (as.map (Ty.applyTS θ)).length := by simpa using hia
  have h1 := List.getElem_of_eq hlist hi'
  rw [← hren]
  apply oneWay_of_applyTS (θ := θ)
  simpa [List.getElem_map] using h1

/-! ### 適用の基本補題(空代入・長さ)と fresh 変数供給

Notation の 3 関係(=・~・⊑)と改名の一般補題をここに集約する
(使用側ファイルに散在していたものの移設;定義の直下に置く)。 -/

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

theorem applyTSList_length (θ : TySubst) : ∀ (l : List Ty),
    (applyTSList θ l).length = l.length
  | [] => rfl
  | t :: l => by simp [applyTSList, applyTSList_length θ l]

theorem applyRenList_length (r : TyVar → TyVar) : ∀ (l : List Ty),
    (applyRenList r l).length = l.length
  | [] => rfl
  | t :: l => by simp [applyRenList, applyRenList_length r l]

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

/-- fresh 変数と任意の型は単一化可能(~ の基本供給) -/
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

/-! ### 3 関係の積成分分割(zip 形;WT-ATOM 再建で使用) -/

theorem zip_applyRenList {r : TyVar → TyVar} : ∀ {τs τs' : List Ty},
    applyRenList r τs = τs' → ∀ pr ∈ τs.zip τs', pr.1.applyRen r = pr.2
  | [], _, h, pr, hpr => by subst h; cases hpr
  | τ :: τs, _, h, pr, hpr => by
      subst h
      simp only [applyRenList, List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · rfl
      · exact zip_applyRenList rfl pr hpr

theorem zip_applyTSList {θ : TySubst} : ∀ {τs τs' : List Ty},
    applyTSList θ τs = τs' → ∀ pr ∈ τs.zip τs', pr.1.applyTS θ = pr.2
  | [], _, h, pr, hpr => by subst h; cases hpr
  | τ :: τs, _, h, pr, hpr => by
      subst h
      simp only [applyTSList, List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · rfl
      · exact zip_applyTSList rfl pr hpr

theorem zip_applyTSList_eq {U : TySubst} : ∀ {τs τts : List Ty},
    applyTSList U τs = applyTSList U τts → τs.length = τts.length →
    ∀ pr ∈ τs.zip τts, pr.1.applyTS U = pr.2.applyTS U
  | [], _, _, _, pr, hpr => by
      cases hpr
  | τ :: τs, [], _, hlen, _, _ => by simp at hlen
  | τ :: τs, τt :: τts, h, hlen, pr, hpr => by
      simp only [applyTSList, List.cons.injEq] at h
      simp only [List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact h.1
      · exact zip_applyTSList_eq h.2 (by simpa using hlen) pr hpr

/-- 積の改名は成分ごとの改名(同じ改名関数) -/
theorem renamesTo_prod_comp {τs τs' : List Ty}
    (h : RenamesTo (.prod τs) (.prod τs')) :
    τs.length = τs'.length ∧ ∀ pr ∈ τs.zip τs', RenamesTo pr.1 pr.2 := by
  obtain ⟨r, hinj, hr⟩ := h
  simp only [Ty.applyRen, Ty.prod.injEq] at hr
  constructor
  · rw [← hr]
    exact (applyRenList_length r τs).symm
  · intro pr hpr
    exact ⟨r, hinj, zip_applyRenList hr pr hpr⟩

/-- 積の one-way instance は成分ごとの one-way instance
    (成分等式を `oneWay_of_applyTS` でパッケージ;dom 制限は同補題が担う) -/
theorem oneWay_prod_comp {τps τms : List Ty}
    (h : OneWay (.prod τps) (.prod τms)) :
    τps.length = τms.length ∧ ∀ pr ∈ τps.zip τms, OneWay pr.1 pr.2 := by
  obtain ⟨θ, _, happ⟩ := h
  simp only [Ty.applyTS, Ty.prod.injEq] at happ
  constructor
  · rw [← happ]
    exact (applyTSList_length θ τps).symm
  · intro pr hpr
    exact oneWay_of_applyTS (zip_applyTSList happ pr hpr)

/-- 積の単一化可能性は成分ごとの単一化可能性(同じ U) -/
theorem unifiable_prod_comp {τs τts : List Ty}
    (h : Unifiable (.prod τs) (.prod τts)) (hlen : τs.length = τts.length) :
    ∀ pr ∈ τs.zip τts, Unifiable pr.1 pr.2 := by
  obtain ⟨U, hU⟩ := h
  simp only [Ty.applyTS, Ty.prod.injEq] at hU
  intro pr hpr
  exact ⟨U, zip_applyTSList_eq hU hlen pr hpr⟩

end TypePM

