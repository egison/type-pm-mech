# R5：値パターンパターン捕捉の実行時意味論

## 状態

- 状態：実行時意味論は解決済み
- 論文での表示：青字（`\new`）
- 静的保証：P1 として未解決

## 問題

matcher の primitive-pattern pattern `#$x` は，利用者パターン中の値パターン
`#M` を捕捉する．節に穴が先行する場合，`M` がどの束縛を参照できるかを
明示しないと，操作的意味論と型付けの文脈がずれる．

典型例は `sortedList` の pivot 節である．

```text
$ ++ #$px :: $
```

ここで `px` が捕捉する式は，原子より前に作られた束縛を参照できる必要がある．
一方，左側の `$` が同じ原子の分解後に作る束縛は，節選択時にはまだ存在しない．
この区別がないと，同一原子内の未来の束縛を捕捉式が読む導出を誤って許し，
`PPP-VAL` の保存性に必要な評価環境を構成できない．

## 固定した解決

`PPP-VAL` は，`MS-REDUCE` が現在の原子に渡す入力環境 `ρ ∪ θ` を使って
捕捉式 `M` を評価する．したがって可視性は次になる．

- 原子より前に確立した lexical binding と pattern binding：利用可能
- 同じ原子の穴が将来作る binding：利用不可
- 後続の原子が作る binding：利用不可

この固定された要件を **value-pattern scope condition** と呼ぶ．R5 が解決するのは
環境と順序の意味論であり，任意の matcher flow に対する静的判定法ではない．

## 論文との対応

- Definition “Matcher Consistency” 後の “Value-pattern-pattern capture”
- `PPP-VAL`
- Conditional PPP Type Preservation
- Appendix の `PPP-VAL` 保存ケース
- `MS-MATCHER` の value-pattern refinement ケース
- 実装節の “Value-pattern-pattern capture in the implementation”

matcher definition だけを見ても，実際に `#$x` がどの利用者パターンを捕捉するかは
決まらない．このため完全な静的条件は definition-time consistency ではなく
per-use-site obligation になる．

## Egison 実装との対応

[`Core.hs`](../../egison/hs-src/Language/Egison/Core.hs) の `processMState'` は原子の
環境を組み立てて `inductiveMatch`／`primitivePatPatternMatch` へ渡す．
`PPValuePat` はその環境を閉じ込めた thunk を作る．

したがって正確な対応は次である．

> 節選択時の atom environment を捕捉し，捕捉式はその環境で評価される．

Egison は call-by-need なので，値までの強制時刻は後へ延び得る．純粋式の
変数可視性と結果は論文の早期評価と一致するが，発散や効果まで含む厳密な
評価時刻の一致は主張しない．

回帰先：

- [`minitest/008-ppval-atom-env.egi`](../../egison/minitest/008-ppval-atom-env.egi)
- [`mini-test/125-ppval-early-eval.egi`](../../egison/mini-test/125-ppval-early-eval.egi)

静的局所検査は `Type/Infer.hs` の `resolveVpShape`，`vpAlign`，`checkVpScope` が担う．
直接形状を追える matcher literal，tuple，直接参照される top-level matcher などを
扱うが，不透明な slot 引数，next matcher 伝播，pattern-function application，
alias，高階 flow は完全には追わない．

## Lean 機械化との対応

[`TypePM/Semantics.lean`](../TypePM/Semantics.lean) の `PPM.pval` は
`Eval SF ρ M v` を直接前提にし，同じ `ρ` で捕捉値を作る．

[`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) には
`capturedExprs` を使う `VPScoped`／`VPScopedList` があり，捕捉式を
`BindCtx.toCtx Δ₀ ++ Γ` で型付ける候補条件を表す．しかし現在，
`VPScoped` は `WTTree.atom` の premise でも最終 `type_safety` の premise でもない．

[`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean) の
`ppp_core`，`ppp_list`，`ppp_preservation` は構造部分を証明済みだが，
`PPP-VAL` の結果型は `heval` oracle から受け取る．`VPScoped` からこの oracle を
導く橋はまだない．

## P1 へ残るもの

[P1](value-pattern-scope.md) は次を決める必要がある．

- 不透明・高階な matcher flow でも捕捉候補を追跡する表現
- pattern-function，tuple，next matcher をまたぐ条件の合成
- `VPScoped` または同等条件を source typing と safety invariant へ配線する方法
- 健全性を保ちつつ既存ライブラリ idiom を許す保守性

R5 の完了を P1 の完了とみなしてはならない．

## 回帰確認

- 捕捉式を同一原子の穴の出力文脈で型付けしない．
- Egison について「値を節選択時に必ず強制する」と書かず，環境捕捉と書く．
- `VPScoped` の存在だけで最終型安全性に配線済みと主張しない．
- built-in `something` の値パターン比較と，matcher 固有の `#$x` refinement を
  同一視しない．
