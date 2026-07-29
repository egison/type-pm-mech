# R2：matcher 節へ送るパターン形の限定

## 状態

- 状態：解決済み
- 論文での表示：青字（`\new`）
- 解決の種類：操作的意味論の規則重複の除去
- P1/P2 との関係：独立

## 問題

`MS-MATCHER` 系の規則を任意のパターンへ適用できると，連言，選言，
パターン関数適用には二つの処理経路が生じる．

1. `MS-AND`，`MS-OR`，`MS-PATFUN-ENTER` で構文的に分解する経路
2. user-defined matcher の節列へ送り，bare-hole catch-all で受ける経路

例えば `($x :: $xs) & $y` が catch-all に先取りされると，内部の構成子パターンが
通常 `something` に委譲される．`something` は cons を分解する能力を持たないため，
本来の構文主導経路があるにもかかわらず行き詰まり得る．

## 固定した解決

user-defined matcher の3規則に `clause-form(p)` を要求する．節へ送るのは次だけである．

- パターン変数
- ワイルドカード
- 値パターン
- パターン構成子
- タプルパターン

連言，選言，パターン関数適用，埋込みパターン変数は，それぞれの専用規則で先に
処理する．これにより意味論は構文主導になり，catch-all と専用規則の重複が消える．

## 論文との対応

- 操作的意味論の `clause-form` 定義
- `MS-MATCHER-PP-FAIL`
- `MS-MATCHER-DP-FAIL`
- `MS-MATCHER`
- §3.3 の user-defined matcher dispatch の説明
- 実装節の “Clause ordering in the implementation”

R2 は catch-all の**位置**を決める R3 と補完関係にある．R2 は節列へ送る前の
パターン形を制限し，R3 は節列へ送った後の到達可能性を保証する．

## Egison 実装との対応

[`Core.hs`](../../egison/hs-src/Language/Egison/Core.hs) の `processMState'` は，
pattern-function application，連言，選言などを構文的に処理した後でのみ
`UserMatcher` の `inductiveMatch` へ進む．したがって，**論文 core に含まれる
pattern forms について**実装の dispatch 順序は `clause-form` と一致する．
Egison 固有の indexed pattern `IIndexedPat` はこの core 分類の外側にあり，
`UserMatcher` へ到達するため，実装の全 pattern forms が同じ五分類に収まるとは
主張しない．

関連する既存例：

- [`mini-test/120-patfun-struct-index.egi`](../../egison/mini-test/120-patfun-struct-index.egi)
- [`mini-test/121-matcher-arm-typeclass.egi`](../../egison/mini-test/121-matcher-arm-typeclass.egi)

これらは該当経路を通るが，`clause-form` だけを狙った負の回帰テストは現在ない．

## Lean 機械化との対応

[`TypePM/Semantics.lean`](../TypePM/Semantics.lean) の
`Pattern.isClauseForm` が対象形を定義し，次の3構成子が
`p.isClauseForm = true` を要求する．

- `MAtom.matcherPPFail`
- `MAtom.matcherDPFail`
- `MAtom.matcher`

実行関数側は [`TypePM/Exec.lean`](../TypePM/Exec.lean) の `matomF` が同じ guard を
使う．関係意味論と実行関数の対応は
[`TypePM/Metatheory/Adequacy.lean`](../TypePM/Metatheory/Adequacy.lean) の
`clausesF_sound'`，`armsF_sound'`，`matomF_sound'` で扱われる．

## 保証範囲

R2 は実行時 dispatch の曖昧性を解く．次は別問題である．

- matcher 節そのものの Coverage と arm 網羅性（R3）
- 値パターンパターンの捕捉環境（R5/P1）
- matcher 値の能力保存インスタンス化（P2）
- Egison に専用の clause-form 負テストを追加すること

## 回帰確認

- `MS-MATCHER` 系の新規規則には同じ `clause-form` 前提を付ける．
- 実装で新しい複合パターン形を追加したときは，matcher 節より前に専用 dispatch
  するか，明示的に clause form に含めるかを決める．
- `($x :: $xs) & $y` のような連言を catch-all に直接渡さない．
