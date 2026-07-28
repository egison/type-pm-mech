import TypePM.WellTyped

/-!
# Theorem 5.1:マッチャー多相性 (Matcher Polymorphism) — 証明済み

パターンの型はそれを評価するマッチャーに依存しない:
双対判定 Γ;ε ⊢ p : Pattern (τp ▷ τt) ; Δ が与えられれば、
双対検査(構造 τm' ⊑ τp・標的 τm ~ τt)を満たす**任意の**マッチャー式 e_m について、
matchAll e_t as e_m with p → e は同じパターン導出のまま T-MATCHALL で整型する。

論文の証明は「パターン型付け規則のどの premise もマッチャーに言及しない」;
機械化では `hp : PatTy …` がマッチャーと独立な仮定として現れ、
COERCE-MATCHER-TO-SLOT と T-MATCHALL の構成子合成そのものが証明になる。
-/

namespace TypePM

/-- **Theorem 5.1 (Matcher Polymorphism)**。
    パターン導出 `hp` は結論の構成にそのまま渡される(マッチャーごとの再導出は不要)。 -/
theorem matcher_polymorphism
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {e_t e_m : Expr} {p : Pattern} {body : Expr}
    {τp τt τm τm' τr : Ty} {Δ : BindCtx}
    (hp : PatTy SD SP SF Γ [] [] p τp τt Δ)          -- 双対判定(マッチャー非依存)
    (het : HasTy SD SP SF Γ e_t τt)                   -- Γ ⊢ e_t : τt
    (hem : HasTy SD SP SF Γ e_m (.matcher τm))        -- m : Matcher τm(内在型)
    (hren : RenamesTo τm τm')                         -- τm' = fresh_rename(τm)
    (hstr : OneWay τp τm')                            -- 構造:τm' ⊑ τp
    (htgt : Unifiable τm τt)                          -- 標的:τm ~ τt
    (hbody : HasTy SD SP SF (BindCtx.toCtx Δ ++ Γ) body τr) :
    HasTy SD SP SF Γ (.matchAll e_t e_m p body) (Ty.listT τr) :=
  HasTy.matchAll het hp
    (HasTy.coerceMatcherToSlot hem hren hstr htgt) hbody

/-- 系:同じパターン導出が異なる 2 つのマッチャーで共有される
    (論文の例:$x :: $xs は list/multiset/set で同一導出)。 -/
theorem matcher_polymorphism_two
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {e_t e_m₁ e_m₂ : Expr} {p : Pattern} {body : Expr}
    {τp τt τm₁ τm₁' τm₂ τm₂' τr : Ty} {Δ : BindCtx}
    (hp : PatTy SD SP SF Γ [] [] p τp τt Δ)
    (het : HasTy SD SP SF Γ e_t τt)
    (hbody : HasTy SD SP SF (BindCtx.toCtx Δ ++ Γ) body τr)
    (hem₁ : HasTy SD SP SF Γ e_m₁ (.matcher τm₁))
    (h₁ : RenamesTo τm₁ τm₁') (h₁' : OneWay τp τm₁') (h₁'' : Unifiable τm₁ τt)
    (hem₂ : HasTy SD SP SF Γ e_m₂ (.matcher τm₂))
    (h₂ : RenamesTo τm₂ τm₂') (h₂' : OneWay τp τm₂') (h₂'' : Unifiable τm₂ τt) :
    HasTy SD SP SF Γ (.matchAll e_t e_m₁ p body) (Ty.listT τr) ∧
    HasTy SD SP SF Γ (.matchAll e_t e_m₂ p body) (Ty.listT τr) :=
  ⟨matcher_polymorphism hp het hem₁ h₁ h₁' h₁'' hbody,
   matcher_polymorphism hp het hem₂ h₂ h₂' h₂'' hbody⟩

end TypePM
