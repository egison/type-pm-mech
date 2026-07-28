import TypePM.WellTyped

/-!
# 保存系の補題と型安全性 (論文 §5.3–5.4・付録 C)

* Lemma 5.4 (PPP Type Preservation) — `ppp_preservation`
* Lemma C.2 (Matcher-Value Slot Invariant) — `matcher_slot_invariant`
* Theorem 5.6 (Type Safety) —
  (a) 式評価の型付け `type_safety_a`、(b) マッチング状態保存 `type_safety_b`

いずれも論文に証明があり(付録 C)、未機械化(`sorry`)。
論文の証明は結合導出木の高さに関する強帰納法で (a)(b) を同時に示す;
機械化では `Eval`/`Step` が単一の相互帰納族なので相互構造帰納に対応する
(Lean の相互帰納原理の整備が Stage 1 の主作業;README ロードマップ)。
-/

namespace TypePM

/-- **Lemma 5.4 (PPP Type Preservation)**。
    pp 判定の穴対列 pairs と p の双対判定が与えられ pp ≈ p が成功したとき、
    取り出された次パターン列 ps' は pairs の標的成分で型付けられ
    (Δ は p の入力文脈から左→右に継がれ、出力は p のそれと一致)、
    ρp は pp の値パターン束縛 Δpp をその型の値で束縛する。

    値束縛の型付けには Theorem 5.6(a) を要する(論文は結合帰納法;
    ここでは評価型付けを仮定 `heval` として渡す)。 -/
theorem ppp_preservation
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx} {Φ : PatParamCtx}
    {ρ : Env} {pp : PPat} {p : Pattern} {ps' : List Pattern} {ρp : Env}
    {τ τp₀ : Ty} {pairs : List (Ty × Ty)} {Δpp : BindCtx} {Δ₀ Δn : BindCtx}
    (heval : ∀ ρ' e v τ', Eval SF ρ' e v →
      HasTy SD SP SF Γ e τ' → ValueTy SD SP SF v τ')
    (hpp : PPTy SP pp τ pairs Δpp)
    (hp : PatTy SD SP SF Γ Φ Δ₀ p τp₀ τ Δn)
    (hm : PPM SF ρ pp p (some (ps', ρp))) :
    ps'.length = pairs.length ∧
    (∃ duals, PatTys SD SP SF Γ Φ Δ₀ ps' duals Δn ∧
      duals.map (·.2) = pairs.map (·.2)) ∧
    (∀ pr ∈ Δpp, ∃ v, Env.find? ρp pr.1 = some v ∧ ValueTy SD SP SF v pr.2) := by
  sorry

/-- **Lemma C.2 (Matcher-Value Slot Invariant)**。
    スロット型 MatcherSlot τp τt で消費される式 e_m の評価値 m は、
    自らの内在型 Matcher τm について双対検査の両条件を満たし、
    WT-ATOM のマッチャー選言(something / Σ_P 整合 / それらの積)に入る。 -/
theorem matcher_slot_invariant
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {ρ : Env} {e_m : Expr} {m : Value} {τp τt : Ty}
    (hρ : EnvTyped SD SP SF Γ ρ)
    (hty : HasTy SD SP SF Γ e_m (.slot τp τt))
    (hev : Eval SF ρ e_m m) :
    ∃ τm τm', ValueTy SD SP SF m (.matcher τm) ∧
      RenamesTo τm τm' ∧ OneWay τp τm' ∧ Unifiable τm τt ∧
      MatcherOK SD SP m := by
  sorry

/-- **Theorem 5.6(a) (式評価の型付け)**。
    Γ ⊢ e : τ で ρ が Γ で型付けられ、ρ, e ⇓ v ならば v : τ。
    (Σ_F は PATFUN-DEF 検査済みと仮定。) -/
theorem type_safety_a
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {ρ : Env} {e : Expr} {v : Value} {τ : Ty}
    (hSigF : SigFWF SD SP SF Γ)
    (hev : Eval SF ρ e v)
    (hρ : EnvTyped SD SP SF Γ ρ)
    (hty : HasTy SD SP SF Γ e τ) :
    ValueTy SD SP SF v τ := by
  sorry

/-- **Theorem 5.6(b) (マッチング状態保存)**。
    s → [s₁, …, s_l] かつ ⊢ s : Δ_goal ok ならば各 sᵢ について ⊢ sᵢ : Δ_goal ok。 -/
theorem type_safety_b
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {ss : List MState} {Δgoal : BindCtx}
    (hSigF : SigFWF SD SP SF Γ)
    (hstep : Step SF s ss)
    (hwt : WTState SD SP SF Γ s Δgoal) :
    ∀ s' ∈ ss, WTState SD SP SF Γ s' Δgoal := by
  sorry

end TypePM
