import TypePM.Exec
import TypePM.Typing

/-!
# 主型性 (論文 §5.2・付録 B/D) — Lemma 5.2 の計算可能性部分は証明済み

Theorem 5.3 (Principal Type Property) の機械化には Algorithm W
(付録 B:6 ステップの matchAll 推論・双対検査の実装・Matcher rigidity)の
形式化が必要で、それは Stage 2(README ロードマップ)。

本ファイルで**証明済み**:
* `matchOneWay_sound` / `matchOneWay_complete` —
  one-way matching の線形時間アルゴリズム(`Exec.lean`)の健全性と完全性。
  一意性 `oneWay_unique`(TypeRel.lean)と併せて **Lemma 5.2 の機械化が完結**。

Stage 2 の残り(論文対応):
* Algorithm W の実装(付録 B の Step 1–6、rigidity 付き Robinson 単一化)
* Lemma D.1 (Δ-threading preserves principality)
* Lemma D.2 (Tuple-of-matchers coercion uniqueness)
* Lemma D.3 (Slot-tuple coercion uniqueness)
* Theorem 5.3 (Principal Type Property)
-/

namespace TypePM

/-! ## Ty.beq の基本補題 -/

mutual
theorem Ty.beq_eq : ∀ (t t' : Ty), Ty.beq t t' = true → t = t'
  | .var a, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next b => simp only [beq_iff_eq] at h; exact h ▸ rfl
  | .int, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      rfl
  | .bool, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      rfl
  | .data n ts, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next n' ts' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h₁, h₂⟩ := h
        simp only [beq_iff_eq] at h₁
        rw [h₁, Ty.beqList_eq ts ts' h₂]
  | .prod ts, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next ts' => rw [Ty.beqList_eq ts ts' h]
  | .fn t₁ t₂, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next t₁' t₂' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h₁, h₂⟩ := h
        rw [Ty.beq_eq t₁ t₁' h₁, Ty.beq_eq t₂ t₂' h₂]
  | .matcher t, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next t'' => rw [Ty.beq_eq t t'' h]
  | .slot t₁ t₂, t', h => by
      cases t' <;> simp only [Ty.beq] at h <;> try exact Bool.noConfusion h
      next t₁' t₂' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h₁, h₂⟩ := h
        rw [Ty.beq_eq t₁ t₁' h₁, Ty.beq_eq t₂ t₂' h₂]

theorem Ty.beqList_eq : ∀ (ts ts' : List Ty), Ty.beqList ts ts' = true → ts = ts'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [Ty.beqList] at h; exact Bool.noConfusion h
  | _ :: _, [], h => by simp only [Ty.beqList] at h; exact Bool.noConfusion h
  | t :: ts, t' :: ts', h => by
      simp only [Ty.beqList, Bool.and_eq_true] at h
      obtain ⟨h₁, h₂⟩ := h
      rw [Ty.beq_eq t t' h₁, Ty.beqList_eq ts ts' h₂]
end

mutual
theorem Ty.beq_refl : ∀ (t : Ty), Ty.beq t t = true
  | .var a => by simp [Ty.beq]
  | .int => rfl
  | .bool => rfl
  | .data n ts => by simp [Ty.beq, Ty.beqList_refl ts]
  | .prod ts => Ty.beqList_refl ts
  | .fn t₁ t₂ => by simp [Ty.beq, Ty.beq_refl t₁, Ty.beq_refl t₂]
  | .matcher t => Ty.beq_refl t
  | .slot t₁ t₂ => by simp [Ty.beq, Ty.beq_refl t₁, Ty.beq_refl t₂]

theorem Ty.beqList_refl : ∀ (ts : List Ty), Ty.beqList ts ts = true
  | [] => rfl
  | t :: ts => by simp [Ty.beqList, Ty.beq_refl t, Ty.beqList_refl ts]
end

/-! ## appVar・dom の補題 -/

theorem TySubst.appVar_eq_of_find? {θ : TySubst} {a : TyVar} {pr : TyVar × Ty}
    (hf : List.find? (fun q => q.1 == a) θ = some pr) : θ.appVar a = pr.2 := by
  simp [TySubst.appVar, hf]

theorem TySubst.appVar_eq_var_of_find?_none {θ : TySubst} {a : TyVar}
    (hf : List.find? (fun q => q.1 == a) θ = none) : θ.appVar a = .var a := by
  simp [TySubst.appVar, hf]

theorem TySubst.mem_dom_of_find? {θ : TySubst} {a : TyVar} {pr : TyVar × Ty}
    (hf : List.find? (fun q => q.1 == a) θ = some pr) : a ∈ θ.dom := by
  have hmem := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  simp only [beq_iff_eq] at hp
  subst hp
  exact List.mem_map_of_mem hmem

theorem TySubst.not_mem_dom_of_find?_none {θ : TySubst} {a : TyVar}
    (hf : List.find? (fun q => q.1 == a) θ = none) : a ∉ θ.dom := by
  intro hmem
  simp only [TySubst.dom] at hmem
  obtain ⟨pr, hpr, hfst⟩ := List.mem_map.mp hmem
  have := List.find?_eq_none.mp hf pr hpr
  simp [hfst] at this

theorem TySubst.appVar_cons_ne {a b : TyVar} {t : Ty} {θ : TySubst} (h : a ≠ b) :
    TySubst.appVar ((a, t) :: θ) b = θ.appVar b := by
  simp [TySubst.appVar, h]

theorem TySubst.appVar_cons_self {a : TyVar} {t : Ty} {θ : TySubst} :
    TySubst.appVar ((a, t) :: θ) a = t := by
  simp [TySubst.appVar]

/-! ## matchOneWay の不変量 -/

/-- acc から θ への拡張不変量(自由変数集合 fv に対して)。 -/
structure MOWInv (acc θ : TySubst) (fv : List TyVar) : Prop where
  domMono : ∀ a ∈ acc.dom, a ∈ θ.dom
  ext     : ∀ a ∈ acc.dom, θ.appVar a = acc.appVar a
  cover   : ∀ a ∈ fv, a ∈ θ.dom
  bound   : ∀ a ∈ θ.dom, a ∈ acc.dom ∨ a ∈ fv

theorem MOWInv.refl (acc : TySubst) : MOWInv acc acc [] where
  domMono _ h := h
  ext _ _ := rfl
  cover _ h := by cases h
  bound _ h := .inl h

theorem MOWInv.trans {acc θ₁ θ : TySubst} {fv₁ fv₂ : List TyVar}
    (h₁ : MOWInv acc θ₁ fv₁) (h₂ : MOWInv θ₁ θ fv₂) : MOWInv acc θ (fv₁ ++ fv₂) where
  domMono a ha := h₂.domMono a (h₁.domMono a ha)
  ext a ha := (h₂.ext a (h₁.domMono a ha)).trans (h₁.ext a ha)
  cover a ha := by
    rcases List.mem_append.mp ha with h | h
    · exact h₂.domMono a (h₁.cover a h)
    · exact h₂.cover a h
  bound a ha := by
    rcases h₂.bound a ha with h | h
    · rcases h₁.bound a h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_append.mpr (.inl h'))
    · exact .inr (List.mem_append.mpr (.inr h))

/-- 後段の拡張は前段で被覆済みの型の適用結果を変えない。 -/
theorem MOWInv.applyTS_stable {θ₁ θ : TySubst} {fv₂ : List TyVar} {τ : Ty}
    (h₂ : MOWInv θ₁ θ fv₂) (hcov : ∀ a ∈ τ.ftv, a ∈ θ₁.dom) :
    τ.applyTS θ = τ.applyTS θ₁ :=
  applyTS_congr τ fun a ha => h₂.ext a (hcov a ha)

theorem MOWInv.applyTSList_stable {θ₁ θ : TySubst} {fv₂ : List TyVar} {ts : List Ty}
    (h₂ : MOWInv θ₁ θ fv₂) (hcov : ∀ a ∈ ftvList ts, a ∈ θ₁.dom) :
    applyTSList θ ts = applyTSList θ₁ ts :=
  applyTSList_congr ts fun a ha => h₂.ext a (hcov a ha)

/-! ## matchOneWay の健全性 -/

mutual
theorem matchOneWay_spec : ∀ (τp : Ty) {τm : Ty} {acc θ : TySubst},
    matchOneWay τp τm acc = some θ →
    MOWInv acc θ τp.ftv ∧ τp.applyTS θ = τm
  | .var a, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next pr hf =>
        split at h
        next hbeq =>
          obtain rfl : acc = θ := Option.some.inj h
          have ha : a ∈ acc.dom := TySubst.mem_dom_of_find? hf
          refine ⟨⟨fun _ h => h, fun _ _ => rfl, ?_, fun _ h => .inl h⟩, ?_⟩
          · intro b hb
            simp only [Ty.ftv, List.mem_singleton] at hb
            exact hb ▸ ha
          · show Ty.applyTS acc (.var a) = τm
            simp only [Ty.applyTS]
            rw [TySubst.appVar_eq_of_find? hf, Ty.beq_eq _ _ hbeq]
        next => simp at h
      next hf =>
        obtain rfl : (a, τm) :: acc = θ := Option.some.inj h
        have hna : a ∉ acc.dom := TySubst.not_mem_dom_of_find?_none hf
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · intro b hb
          simp only [TySubst.dom, List.map_cons, List.mem_cons]
          exact .inr hb
        · intro b hb
          have hab : a ≠ b := fun he => hna (he ▸ hb)
          exact TySubst.appVar_cons_ne hab
        · intro b hb
          simp only [Ty.ftv, List.mem_singleton] at hb
          subst hb
          simp [TySubst.dom]
        · intro b hb
          simp only [TySubst.dom, List.map_cons, List.mem_cons] at hb
          rcases hb with hb | hb
          · exact .inr (by simp [Ty.ftv, hb])
          · exact .inl hb
        · show Ty.applyTS ((a, τm) :: acc) (.var a) = τm
          simp only [Ty.applyTS]
          exact TySubst.appVar_cons_self
  | .int, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      · obtain rfl : acc = θ := Option.some.inj h
        exact ⟨MOWInv.refl acc, rfl⟩
      · simp at h
  | .bool, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      · obtain rfl : acc = θ := Option.some.inj h
        exact ⟨MOWInv.refl acc, rfl⟩
      · simp at h
  | .data n ts, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next n' ts' =>
        split at h
        next hn =>
          obtain ⟨inv, heq⟩ := matchOneWayList_spec ts h
          refine ⟨inv, ?_⟩
          simp only [beq_iff_eq] at hn
          simp only [Ty.applyTS, heq, hn]
        next => simp at h
      next => simp at h
  | .prod ts, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next ts' =>
        obtain ⟨inv, heq⟩ := matchOneWayList_spec ts h
        exact ⟨inv, by simp only [Ty.applyTS, heq]⟩
      next => simp at h
  | .fn t₁ t₂, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next t₁' t₂' =>
        split at h
        next θ₁ h₁ =>
          obtain ⟨inv₁, heq₁⟩ := matchOneWay_spec t₁ h₁
          obtain ⟨inv₂, heq₂⟩ := matchOneWay_spec t₂ h
          refine ⟨inv₁.trans inv₂, ?_⟩
          simp only [Ty.applyTS]
          rw [inv₂.applyTS_stable inv₁.cover, heq₁, heq₂]
        next => simp at h
      next => simp at h
  | .matcher t, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next t' =>
        obtain ⟨inv, heq⟩ := matchOneWay_spec t h
        exact ⟨inv, by simp only [Ty.applyTS, heq]⟩
      next => simp at h
  | .slot t₁ t₂, τm, acc, θ, h => by
      unfold matchOneWay at h
      split at h
      next t₁' t₂' =>
        split at h
        next θ₁ h₁ =>
          obtain ⟨inv₁, heq₁⟩ := matchOneWay_spec t₁ h₁
          obtain ⟨inv₂, heq₂⟩ := matchOneWay_spec t₂ h
          refine ⟨inv₁.trans inv₂, ?_⟩
          simp only [Ty.applyTS]
          rw [inv₂.applyTS_stable inv₁.cover, heq₁, heq₂]
        next => simp at h
      next => simp at h

theorem matchOneWayList_spec : ∀ (ts : List Ty) {ts' : List Ty} {acc θ : TySubst},
    matchOneWayList ts ts' acc = some θ →
    MOWInv acc θ (ftvList ts) ∧ applyTSList θ ts = ts'
  | [], ts', acc, θ, h => by
      unfold matchOneWayList at h
      split at h
      · obtain rfl : acc = θ := Option.some.inj h
        exact ⟨MOWInv.refl acc, rfl⟩
      · simp at h
  | t :: ts, tts', acc, θ, h => by
      unfold matchOneWayList at h
      split at h
      next t' ts' =>
        split at h
        next θ₁ h₁ =>
          obtain ⟨inv₁, heq₁⟩ := matchOneWay_spec t h₁
          obtain ⟨inv₂, heq₂⟩ := matchOneWayList_spec ts h
          refine ⟨inv₁.trans inv₂, ?_⟩
          simp only [applyTSList]
          rw [inv₂.applyTS_stable inv₁.cover, heq₁, heq₂]
        next => simp at h
      next => simp at h
end

/-- **`matchOneWay` の健全性**(Lemma 5.2 の計算可能性部分、**証明済み**):
    witness を返せば one-way instance が成り立つ。 -/
theorem matchOneWay_sound {τp τm : Ty} {θ : TySubst}
    (h : matchOneWay τp τm [] = some θ) :
    OneWayAt θ τp τm := by
  obtain ⟨inv, heq⟩ := matchOneWay_spec τp h
  refine ⟨fun a ha => ?_, heq⟩
  rcases inv.bound a ha with h' | h'
  · simp [TySubst.dom] at h'
  · exact h'

/-! ## matchOneWay の完全性 -/

mutual
theorem matchOneWay_completeAux : ∀ (τp : Ty) {θw acc : TySubst},
    (∀ a ∈ acc.dom, acc.appVar a = θw.appVar a) →
    ∃ θ, matchOneWay τp (τp.applyTS θw) acc = some θ ∧
      (∀ a ∈ θ.dom, θ.appVar a = θw.appVar a)
  | .var a, θw, acc, hacc => by
      simp only [Ty.applyTS]
      unfold matchOneWay
      cases hf : List.find? (fun pr => pr.1 == a) acc with
      | some pr =>
        obtain ⟨a', t'⟩ := pr
        have hp : acc.appVar a = t' := TySubst.appVar_eq_of_find? hf
        have hmem : a ∈ acc.dom := TySubst.mem_dom_of_find? hf
        have h2 : t' = θw.appVar a := hp ▸ hacc a hmem
        refine ⟨acc, ?_, hacc⟩
        rw [← h2]
        show (if t'.beq t' = true then some acc else none) = some acc
        rw [Ty.beq_refl]
        simp
      | none =>
        refine ⟨(a, θw.appVar a) :: acc, rfl, ?_⟩
        intro b hb
        simp only [TySubst.dom, List.map_cons, List.mem_cons] at hb
        by_cases hab : a = b
        · subst hab; exact TySubst.appVar_cons_self
        · rcases hb with hb | hb
          · exact absurd hb.symm hab
          · rw [TySubst.appVar_cons_ne hab]; exact hacc b hb
  | .int, θw, acc, hacc => ⟨acc, rfl, hacc⟩
  | .bool, θw, acc, hacc => ⟨acc, rfl, hacc⟩
  | .data n ts, θw, acc, hacc => by
      simp only [Ty.applyTS]
      obtain ⟨θ, hrun, hθ⟩ := matchOneWayList_completeAux ts hacc
      exact ⟨θ, by unfold matchOneWay; simp [hrun], hθ⟩
  | .prod ts, θw, acc, hacc => by
      simp only [Ty.applyTS]
      obtain ⟨θ, hrun, hθ⟩ := matchOneWayList_completeAux ts hacc
      exact ⟨θ, by unfold matchOneWay; simp [hrun], hθ⟩
  | .fn t₁ t₂, θw, acc, hacc => by
      simp only [Ty.applyTS]
      obtain ⟨θ₁, hrun₁, hθ₁⟩ := matchOneWay_completeAux t₁ (θw := θw) hacc
      obtain ⟨θ, hrun, hθ⟩ := matchOneWay_completeAux t₂ (θw := θw) hθ₁
      exact ⟨θ, by unfold matchOneWay; simp [hrun₁, hrun], hθ⟩
  | .matcher t, θw, acc, hacc => by
      simp only [Ty.applyTS]
      obtain ⟨θ, hrun, hθ⟩ := matchOneWay_completeAux t (θw := θw) hacc
      exact ⟨θ, by unfold matchOneWay; simp [hrun], hθ⟩
  | .slot t₁ t₂, θw, acc, hacc => by
      simp only [Ty.applyTS]
      obtain ⟨θ₁, hrun₁, hθ₁⟩ := matchOneWay_completeAux t₁ (θw := θw) hacc
      obtain ⟨θ, hrun, hθ⟩ := matchOneWay_completeAux t₂ (θw := θw) hθ₁
      exact ⟨θ, by unfold matchOneWay; simp [hrun₁, hrun], hθ⟩

theorem matchOneWayList_completeAux : ∀ (ts : List Ty) {θw acc : TySubst},
    (∀ a ∈ acc.dom, acc.appVar a = θw.appVar a) →
    ∃ θ, matchOneWayList ts (applyTSList θw ts) acc = some θ ∧
      (∀ a ∈ θ.dom, θ.appVar a = θw.appVar a)
  | [], θw, acc, hacc => ⟨acc, rfl, hacc⟩
  | t :: ts, θw, acc, hacc => by
      simp only [applyTSList]
      obtain ⟨θ₁, hrun₁, hθ₁⟩ := matchOneWay_completeAux t (θw := θw) hacc
      obtain ⟨θ, hrun, hθ⟩ := matchOneWayList_completeAux ts (θw := θw) hθ₁
      exact ⟨θ, by unfold matchOneWayList; simp [hrun₁, hrun], hθ⟩
end

/-- **`matchOneWay` の完全性**(**証明済み**):
    one-way instance が存在すればアルゴリズムは witness を返す。 -/
theorem matchOneWay_complete {τp τm : Ty}
    (h : OneWay τp τm) :
    ∃ θ, matchOneWay τp τm [] = some θ := by
  obtain ⟨θw, -, heq⟩ := h
  obtain ⟨θ, hrun, -⟩ :=
    matchOneWay_completeAux τp (θw := θw) (acc := [])
      (by intro a ha; simp [TySubst.dom] at ha)
  exact ⟨θ, heq ▸ hrun⟩

end TypePM
