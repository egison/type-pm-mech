# `type-pm` の未解決設計問題

このディレクトリは，`type-pm-paper` が条件付き結果の前提として残している
設計問題を，1問題1ファイルで検討するための索引である．

ここにある文書は設計の決定記録ではない．現在固定できている事実，必要な性質，
候補となる設計空間，決定前に答えるべき質問を分離し，問題を1つずつ議論できる
ようにすることを目的とする．

## 問題一覧

| ID | 問題 | 現在の論文への影響 | 状態 |
|---|---|---|---|
| P1 | [不透明・高階なマッチャーフローに対する値パターンスコープ条件](value-pattern-scope.md) | 捕捉許容性，条件付き保存性・型安全性 | 設計判断待ち |
| P2 | [`Matcher` 添字の能力を保存するスキームインスタンス化](matcher-capability-instantiation.md) | 能力許容性，`mPoly`，主要型，無条件の進行性・型安全性 | 設計判断待ち |

## 2問題の境界

- P1 は「選ばれた matcher 節の `#$x` が，利用者パターン中のどの値パターン式を
  捕捉し，その式が原子入力環境だけで型付くか」を扱う．
- P2 は「一般化された matcher 値を利用箇所でインスタンス化しても，定義時に
  確立した分解能力が強化されないか」を扱う．
- どちらも実行時の matcher 値の流れに関係するが，P1 は名前・環境・捕捉順序，
  P2 は型スキーム・固有能力・インスタンス関係の問題である．一方の解決を
  そのまま他方の解決とみなしてはならない．

## 共通して固定されていること

- `PPP-VAL` は捕捉した値パターン式を，穴による同一原子内の束縛を追加する前の
  原子環境で評価する．
- matcher 値の固有型は，`T-MATCHER`／`T-SOME` が確立した構造的能力を表す．
  matcher の実行時タプルには，`COERCE-TUPLE-MATCHER` の値レベル版により
  正準な積の固有型が与えられる．利用箇所の `MatcherSlot` は，これらの
  固有能力を検査する消費位置である．
- 現在の型安全性・マッチング状態進行性・マッチャー整合性は，捕捉許容性と
  能力許容性を仮定する条件付き結果として読む．
- `StepTotal` という停止性前提は別問題であり，この2ファイルでは設計対象にしない．

## このディレクトリでの進め方

1. 対象の問題ファイルにある「決定すべき質問」に回答する．
2. 採用案だけでなく，却下案と却下理由を残す．
3. 決定後，論文の英語版・日本語版，Egison 実装，Lean の判断・定理境界を
   同時に更新する作業単位を定める．
4. 各ファイルの「受入条件」を満たすテストと機械化を行う．
5. 完了した設計は `type-pm-mech/README.md` の設計判断へ移し，本索引では
   決定記録への参照を残す．

## 主な参照先

- 論文：
  [`type-pm-paper/main.tex`](../../type-pm-paper/main.tex)，
  [`type-pm-paper/ja/main.tex`](../../type-pm-paper/ja/main.tex)
- Lean の型・スキーム：
  [`TypePM/Syntax.lean`](../TypePM/Syntax.lean)，
  [`TypePM/TypeRel.lean`](../TypePM/TypeRel.lean)，
  [`TypePM/Typing.lean`](../TypePM/Typing.lean)
- Lean の実行時不変量と型安全性：
  [`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean)，
  [`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean)
- Egison の型推論：
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs)，
  [`Type/Unify.hs`](../../egison/hs-src/Language/Egison/Type/Unify.hs)，
  [`Type/Env.hs`](../../egison/hs-src/Language/Egison/Type/Env.hs)
