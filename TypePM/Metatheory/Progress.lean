import TypePM.WellTyped

/-!
# Lemma 5.5:マッチング状態の進行 (Matching State Progress)

整型な非終端状態は必ず簡約できる(l = 0 は正当なマッチ失敗であり、行き詰まりではない)。

機械化上の注意(README 設計判断):
MS-MATCHER の premise は分解関数 N・次マッチャー式 M の評価 ⇓ を含むため、
「簡約列 s → [sᵢ] が導出可能」という主張は埋め込まれた式評価の**停止**を要する。
論文は「分解関数は停止すると仮定する」(§5)と明言しており、
ここではそれを大域的停止仮定 `htotal` として渡す
(循環 catch-all 委譲は発散であって stuck ではない、という論文の注記の機械化対応)。
-/

namespace TypePM

/-- **Lemma 5.5 (Matching State Progress)**。
    証明は先頭マッチング木の場合分け(論文付録 C.2 の全ケース):
    変数/ワイルドカード/値パターンは MS-SOME-* / MS-PROD-SOME / catch-all、
    構成子パターンは構造前提が裸変数マッチャーを排除し
    Coverage (Def 4.2(3)) と arm exhaustiveness (1c) で MS-MATCHER が発火、
    タプルは MS-TUPLE または積型 Coverage、
    and/or/パターン関数/MNode は構文主導。未機械化(`sorry`)。 -/
theorem ms_progress
    {SD : SigD} {SP : SigP} {SF : SigF} {Γ : TyCtx}
    {s : MState} {Δgoal : BindCtx}
    (htotal : ∀ ρ e, ∃ v, Eval SF ρ e v)     -- 分解関数の停止仮定(§5)
    (hSigF : SigFWF SD SP SF Γ)
    (hwt : WTState SD SP SF Γ s Δgoal)
    (hne : s.S ≠ []) :
    ∃ ss, Step SF s ss := by
  sorry

end TypePM
