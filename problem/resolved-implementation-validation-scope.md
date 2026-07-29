# R11：Egison 実装と検証結果の主張範囲

## 状態

- 状態：実装事実と論文主張の境界は解決済み
- 論文での表示：青字（`\new`）
- 解決の種類：過大主張の撤回と検証範囲の明示

## 問題

prototype checker の存在から，次を一括して結論するのは強すぎる．

- Egison standard library が追加注釈なしで完全に推論された
- formal Matcher Consistency の全条件を全 matcher で hard error として強制する
- value-pattern scope condition を不透明・高階 flow まで完全検査する
- tensor の領域規約など，例に現れる意味的性質を型だけで保証する
- 実装 corpus の成功が full soundness/principality proof になる

実装は論文設計の重要部分を具体化するが，形式モデルとの間には意図的な近似と，
既存ライブラリ互換のための警告・fallback がある．

## 固定した解決

論文の implementation claim を次へ限定する．

1. 現行 Egison standard-library sources を，**既存の注釈を含む形で** checker が受理する．
2. match site の dual check，matcher rigidity，pattern-function structure など，
   指定した中核検査を実装している．
3. representative な domain error を検出する経験的 validation corpus がある．
4. Matcher Consistency の各条件について，hard check，保守近似，warning，
   未検査を区別して報告する．
5. P1/P2 と full principality は実装済み機能から自動的に解決したとはしない．

## 実装対応表

| 項目 | Egison の現状 | 形式条件との差 |
|---|---|---|
| `MatcherSlot` dual check | `checkMatcherAdmissibility` と one-way/target check | dual-type probe の任意の推論失敗で fresh fallback |
| 単相 matcher rigidity | 異なる `TMatcher` 添字の通常単一化を拒否 | scheme instantiation は通常 HM のまま |
| matcher literal checking | 定義注釈との専用 checking mode | P2 の一般 instance relation ではない |
| matcher-dispatchable | core の複合形を先に構文分解 | Egison 固有 `IIndexedPat` は core 分類外，専用の負回帰テストはない |
| catch-all ordering | bare-hole 後の節を hard error | catch-all の正式な arm 形全体は未強制 |
| arm body の型 | hole target tuple のリスト型へ単一化 | 中核条件 (1b) に対応 |
| arm exhaustiveness | 外側 literal で保守的 hard check | 別 matcher body 内の literal と一般 ADT 列挙は不完全 |
| Coverage | opt-in warning | hard consistency guarantee ではない |
| next matcher 構造 | 通常は component check | 単一式で複数穴の場合，完全な deferred check は skip（eager guard と target check は残る） |
| value-pattern scope | 既知 matcher shape で局所検査 | opaque/higher-order flow は P1 |
| pattern-function structure | 直接名の signature と線形性を検査 | 高階関数式では fresh fallback |
| type-class constraints | scheme と辞書展開に統合済み | qualified principality proof ではない |

## 主な実装箇所

- runtime dispatch と捕捉：
  [`Core.hs`](../../egison/hs-src/Language/Egison/Core.hs)
- 推論，matcher consistency の近似，pattern-function check：
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs)
- rigidity，one-way coercion，tuple slot：
  [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs)
- instantiation：
  [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs)
- type-class dictionary expansion：
  [`Type/TypeClassExpand.hs`](../../egison/hs-src/Language/Egison/Type/TypeClassExpand.hs)

## 検証 corpus

代表的な正の回帰：

- matcher slots：
  `mini-test/60-matcher-slot-parse.egi`，
  `61-matcher-slot-coerce.egi`，
  `80-matcher-slot-tuple.egi`
- pattern-function structure：
  `mini-test/120-patfun-struct-index.egi`
- matcher arm と type classes：
  `mini-test/121-matcher-arm-typeclass.egi`，
  `122-signature-constraints.egi`
- matcher parameter の複数利用点：
  `mini-test/123-multisite-matcher-param.egi`
- arm exhaustiveness：
  `mini-test/124-matcher-dp-arm-exhaustiveness.egi`
- value-pattern capture：
  `minitest/008-ppval-atom-env.egi`，
  `mini-test/125-ppval-early-eval.egi`
- clause order：
  `minitest/009-matcher-clause-order.egi`

代表的な型エラー回帰：

- matcher structural mismatch：
  `test/type-error/01-something-cons.egi`，
  `02-something-cons-param.egi`，
  `04-something-tuple-pattern.egi`，
  `05-matcher-target-mismatch.egi`
- pattern-function target/structure：
  `test/type-error/10-patfun-body-structural.egi` から
  `14-patfun-arg-target.egi`
- pattern-function linearity：
  `test/type-error/20-patfun-linearity-unused.egi` から
  `23-patfun-linearity-under-or.egi`
- next matcher structure：`test/type-error/40-matcher-next-structural.egi`
- matcher rigidity/cast：
  `50-matcher-collection-hetero.egi`，
  `51-matcher-cast-structured.egi`，
  `53-matcher-alias-specialize.egi`，
  `54-something-structured-hole.egi`

ファイル番号の集合は実装の変更で動き得るため，論文の claim は個数だけでなく，
どの性質を各回帰が覆うかで管理する．

## 論文との対応

- abstract と contributions の implementation claim
- validation section と case study
- Appendix “Implementation”
- arm exhaustiveness，Coverage，clause ordering，value-pattern capture の各段落
- conclusion の実装評価

mahjong case study などの domain error 検出は，checker の有用性を示す経験的結果で
ある．すべての domain invariant が型に内在するという主張ではない．

## Lean 機械化との対応

Lean は calculus と proof interface を機械化するものであり，Egison Haskell
checker の refinement ではない．そのため次を区別する．

- Lean の `ConsistentClauses.armExh`：全値・全 instance を量化する意味的条件
- Egison の `pdArmsExhaustive`：限定された構文形を認識する保守近似
- Lean の `holeAfterGenerals`：証明に十分な順序条件
- 論文：唯一の最終 bare-hole catch-all
- Egison：bare-hole 後の節を拒否するが formal catch-all 形全体は未検査

同じ名称を使っても，三者の保証強度は同一ではない．

## 保証範囲

R11 で解決したのは，実装済み事実を再現可能な範囲で述べ，未実装・部分近似を
隠さないことである．次は依然として主張しない．

- Egison checker が論文の全 well-typed program に対して sound/complete であること
- P1/P2 の全面解決
- full/qualified Principal Type Property
- standard library から既存注釈を除いても同じ結果になること
- warning-only Coverage を含む formal consistency の全面強制

## 回帰確認

- implementation claim を変更するときは，対応する正負テストと実装箇所を示す．
- “accepts the standard library” には既存注釈を含むことを書く．
- warning，保守近似，fallback，skip を hard guarantee と呼ばない．
- Haskell 実装，論文形式条件，Lean proposition を三段階で比較する．
