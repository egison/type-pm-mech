# P1：不透明・高階なマッチャーフローに対する値パターンスコープ条件

## 状態

中核設計解決済み（2026-08-02）．論文・Lean・Egison への反映待ち．

primitive-pattern pattern（以下 pp）の各 `#$x` より前に pattern hole `$` を
置かないという，matcher 定義時の局所的な整形式条件を採用する．この条件により，
pp・利用者パターン・matcher 値の整形式性から，`PPP-VAL` が捕捉する値パターン式を
原子入力文脈で型付けられる設計になる．不透明な matcher 引数，次 matcher，
高階受け渡し，パターン関数を通る節形状のフローを追跡する必要はない．この橋渡し
補題のLean証明は未完了である．

この文書では設計判断を固定した．Lean でソース型付けから捕捉許容性を導く補題を
証明し，論文の条件付き保存性・型安全性から capture-admissibility の仮定を除く
作業は未完了である．したがって現時点の定理を無条件と読み替えてはならない．

## 問題の要点

matcher 節の pp にある `#$z` は，利用者パターンの値パターン `#e` を捕捉する．
`e` は，その原子を処理し始めた時点の環境で評価できなければならない．現行の
操作的意味論は次を固定している．

1. `PPP-VAL` が捕捉した値パターン式は，節選択時に先に評価される．
2. 評価環境は，`MS-REDUCE` が当該原子へ渡した原子入力環境である．
3. それ以前の原子が作った束縛は参照できる．
4. 同じ原子の hole がこれから作る束縛は，まだ参照できない．

捕捉式 `e` の期待型を `τ` とすると，論文の捕捉許容性は概ね次を要求する．

```text
原子入力文脈 Γatom ⊢ e : τ
実行時の原子入力環境 ρatom が Γatom を実現する
```

従来は，どの `#e` がどの `#$z` に捕捉されるかが実行時 matcher の節形状に
依存するため，この性質を matcher 型の効果，別のインターフェース，制約，または
全プログラムの matcher フロー解析で運ぶ案を検討していた．採用案は，危険な順序を
pp 自体から除くことで，このフロー問題を発生させない．

## 採用する整形式条件

### 左から右の leaf 順序

pp の leaf を，constructor と tuple の引数順に，深さ優先・左から右へ並べる．

```text
leaves($)                  = [hole]
leaves(_)                  = [wild]
leaves(#$x)                = [pval]
leaves(c pp₁ ... ppₙ)      = leaves(pp₁) ++ ... ++ leaves(ppₙ)
leaves((pp₁, ..., ppₙ))    = leaves(pp₁) ++ ... ++ leaves(ppₙ)
```

整形式条件を次で定める．Lean での述語名は `NoHoleBeforePVal` を予定する．

```text
NoHoleBeforePVal(pp)
  iff  there are no i < j such that
       leaves(pp)[i] = hole and leaves(pp)[j] = pval
```

すなわち，どの `#$x` より前にも `$` が現れてはならない．`_` と先行する別の
`#$y` は利用者パターンの束縛を作らないため，`#$x` より前にあってよい．

例：

```text
許可    #$x
許可    #$x ++ $
許可    (#$x, $) :: $
許可    _ ++ #$x :: $
拒否    $ ++ #$x :: $
拒否    ($, #$n) :: $
拒否    ($, (#$x, $))
```

各 matcher 節の pp に `NoHoleBeforePVal` を要求する．組み込み matcher と trusted
primitive が導入する matcher 値にも同じ条件を要求する．積 matcher は成分ごとに
別の原子を作るので，各成分 matcher を個別に検査する．

この条件で，従来の反例は利用箇所ではなく matcher 定義時に排除される．

```egison
def weird {a} (m : MatcherSlot p a) : Matcher [p] [a] :=
  matcher
    | $ ++ #$z as ... with ...   -- NoHoleBeforePVal 違反

def viaParam {a}
  (m : MatcherSlot [p] [a])
  (xs : [a]) : [[a]] :=
  matchAll xs as m with $ys ++ #ys -> ys
```

従来は `m` が不透明なので `viaParam` の局所検査をすり抜けた．採用後の formal
core では `weird` 自体が整形式でなく，この値を `m` へ渡す導出が存在しない．
Egison が warning-only で `weird` を受理する場合，その実行は formal core の
型安全性定理の対象外である．

### 条件を構文だけに課す理由

この条件は利用者側の特定の `#e` が閉じているかどうかにかかわらず，pp の順序だけで
判定する．したがって，たまたま安全な利用箇所も含め，hole-before-`#$` の節を
formal core から一律に除く保守的な設計である．その代わり，

- matcher 型へ capture effect を追加しない，
- `MatcherSlot` を通る高階コードに節要約を運ばない，
- 別コンパイルや再帰 matcher の到達元解析を行わない，
- 利用箇所で実行時 matcher の内部を反射しない，

という単純な局所型付けを保てる．

## この条件でP1を閉じられる理由

利用者パターンの型付けは左から右へ束縛文脈 `Δ` を拡張する．pp と利用者
パターンを `PPM` で対応付けたとき，同じ原子内で利用者パターンの新しい束縛を
後続位置へ持ち込み得る pp leaf は hole `$` だけである．

`#$x` より前に hole がなければ，対応する利用者値パターン `#e` の型付け位置まで
`Δ` は原子入力文脈 `Δatom` から増えていない．pp の `_` は利用者側の wildcard
だけに一致し，pp の `#$y` は利用者側の値パターンに一致するが，どちらも利用者の
pattern variable を束縛しない．したがって，次を導ける．

```text
pp と p が整型で PPM により対応する
NoHoleBeforePVal(pp)
pp の #$x が p の #e を捕捉する
------------------------------------------------
Γatom ⊢ e : τ
```

実行時には `PPP-VAL` が同じ原子入力環境 `ρatom` で `e` を評価する．
`ρatom ⊨ Γatom` と式評価の型保存から，捕捉結果が `PP-Val` の宣言型 `τ` を持つ．
後続の hole はその後に successor atom を作るので，この導出を壊さない．

この議論は実際に選ばれる matcher の由来に依存しない．すべての matcher literal，
組み込み matcher，実行時 matcher 値が整形式条件を保存することを値型付け不変量に
含めれば，不透明な `MatcherSlot` 引数，高階返却，次 matcher，再帰，積，MNode を
通っても，利用箇所で節形状を復元せずに捕捉許容性を得られる．

別の原子で既に作られた束縛は `Γatom`／`ρatom` に含まれるため，引き続き参照できる．
formal core では，同じ tuple の前成分や連言によって先に完了した原子の束縛を
禁止する条件ではない．full Egison の sequential pattern でも，先に完了した段の
束縛は後段の原子入力環境に入るという同じ区別を使うが，これは core 外の拡張である．
右側の hole が将来作る変数への前方参照は，通常の左から右のパターン型付けが拒否する．

## 表現力の扱い

### `assoc`／`rvAssoc` pattern view

従来，次のような pp は，値パターンより左の要素パターンを取り出しながら，個数を
値パターンで指定する `assocMultiset` のために必要と考えていた．

```egison
| ($, #$n) :: $ as ... with ...
```

formal core ではこの一つの pattern constructor に両方の観測順序を担わせない．
full language の表現力回復案として，同じ target representation に対し，引数順の
異なる二つの pattern constructor／pattern view を用意する．次の等式は一般の
definitional equality ではなく，`assocMultiset` に対して意図する view law を表す
メタ記法である．

```text
<assoc   p1 p2 p3> = (p1, p2) :: p3
<rvAssoc p1 p2 p3> = (p2, p1) :: p3
```

例えば，従来の利用者パターン

```text
($x, #n) :: $rs
```

は，提案する表層メタ記法では，値パターンを先に置いて次のように表せる．これは
現行Egisonに既に存在する構文を主張するものではない．

```text
<rvAssoc #n $x $rs>
```

`rvAssoc` の matcher 節は，例えば `rvAssoc #$n $ $` のように capture-before-hole
の順序を持てる．`assoc`／`rvAssoc` は検査前に tuple-cons パターンへ展開する単なる
構文マクロではなく，この引数順を matcher dispatch まで保持する独立した pattern
constructor／pattern view とする．検査前に `(p2, p1) :: p3` へ展開すると，再び
hole-before-`#$` が現れ，採用条件を満たさない．

上の等式は target に対する意味上の view を表す表層設計である．`assoc`／
`rvAssoc` の view signature，型付け，ShapeCap，Coverage を `type-pm-mech` の
formal core に追加して証明することはP1の完了条件に含めない．P1に必要なのは，
hole-before-`#$` を除いても full language で別の安全な表現を選べるという設計判断
だけである．この表現力回復案を実際に導入する場合の source typing，matcher
dispatch，signature，ShapeCap，Coverage への接続は，P1 safety core とは別の
full-language 設計・実装課題として残る．

### join／cons の refinement

`$ ++ #$px :: $` のように，join の分解結果を取り出す前に pivot を捕捉したい場合も，
formal core がこの pp 形を直接備える必要はない．full language では pivot，prefix，
suffix を capture-before-hole の引数順で公開する専用の pattern constructor／
pattern view として表せる．`_ ++ #$px :: $` のように値パターンより前が wildcard
だけなら，元の pp のまま整形式である．この join view 自体の形式化もP1の完了条件
には含めない．

この設計判断により，`sortedList` や `assocMultiset` の現在の表層構文をそのまま
formal core の必須機能として証明することはP1の完了条件に含めない．必要な探索や
分解の意味は，安全な引数順を持つ別の pattern view で表現する．

### sequential pattern の位置付け

full Egison では，hole 位置を later pattern variable で受け，値パターンを先に
処理してから抽出結果を後続段で照合する sequential pattern を使って，類似の
評価順を表現できる．ただし sequential pattern は表層拡張であり，今回の formal
core の捕捉安全性は自動書換えや sequential pattern の意味論に依存させない．
必要なら Egison 側の elaboration またはライブラリ実装の選択肢として扱う．

## 以前の案からの変更

以前も「`#$x` より前の hole を禁止する」という接頭条件を検討したが，
`sortedList` の `$ ++ #$px :: $` と `assocMultiset` の `($, #$n) :: $` を
そのまま受理できないため撤回していた．当時は，これらの既存構文を formal core の
必須表現力とみなしていた．

今回，観測順序の異なる `assoc`／`rvAssoc` や join 用 pattern view によって同じ
target representation を扱えるため，hole-before-`#$` 自体を core に残す必要は
ないと判断した．表現力は pattern view の選択で回復し，core のP1証明は局所的な
整形式条件へ単純化する．

以下の案は採用しない．

- `Matcher`／`MatcherSlot` 型への capture effect の追加
- 節形状要約を持つ別インターフェース
- capture-safe 制約を運ぶ限定型
- 全プログラムの matcher フロー解析または特殊化
- 不透明 matcher の利用箇所だけを保守的に拒否する方式
- 捕捉直前の実行時自由変数検査を formal core の安全性根拠にする方式

既知 matcher に対する利用箇所の精密な診断や実行時ガードは，full Egison の補助的な
診断として残してよいが，formal core の証明はそれらに依存しない．

## 論文への反映

英語版・日本語版とも，少なくとも次を同期して更新する．

- 「Matcher definitions and consistency」で `NoHoleBeforePVal` を matcher 節の
  整形式条件として本文に定義する．
- pp 型付けと利用者パターン型付けから，捕捉式が原子入力文脈で型付く補題を
  追加する．
- PPP 型保存の `PPP-VAL` ケースで，この補題と式評価の型保存を使う．
- matching-state preservation，初期状態，型安全性へ matcher 整形式不変量を通す．
- `capture-admissible` を外部 oracle とする記述を，ソース整形式性から導く記述へ
  置き換える．
- 実装付録では，formal core の拒否と Egison の warning-only 境界を区別する．
- 現行 `sortedList`／`assocMultiset` の hole-before-`#$` 形を formal core の
  必須例として使わず，pattern view による安全な代替または full-language extension
  であることを明記する．

本文が形式仕様の正本であるため，整形式条件と健全性補題を付録だけに置かない．

## Egison 実装との対応

### 定義時 warning

Egison では後方の実用コードを直ちに拒否せず，matcher literal の各 pp に対して
`NoHoleBeforePVal` を左から右へ検査し，違反を warning として報告する方針を採る．
AST は `PPPatVar` と `PPValuePat` を区別しているので，状態 `seenHole : Bool` を
thread する一回の構文走査で判定できる．

warning-only の matcher は実行可能なため，Egison が受理する全プログラムへ formal
core の無条件型安全性を主張してはならない．定理の対象は，診断の表示有無ではなく，
`NoHoleBeforePVal` を構文的に検証済みで，かつP2の `CoverageOK` など covered
calculus の条件を満たす certified subset とする．違反 matcher は full-language
legacy extension として扱う．将来の certified mode では同じ診断をエラーへ
昇格できる．

### 既存の利用箇所検査

現行実装には，静的に形状が見える matcher に対する局所検査がある．

- `inferMatcherShapes`：トップレベル matcher 定義の節 pp を記録する．
- `resolveVpShape`：matcher リテラル，積，トップレベル定義の適用を解決する．
- `vpAlign`／`vpAlignList`：pp と利用者パターンを対応付け，同じ原子内で左にある
  hole の束縛を集める．
- `checkVpScope`：捕捉式がその禁止変数を参照すれば型エラーにする．
- `VpUnknown`：不透明な matcher は現在検査しない．

この検査は，warning-only で残した legacy matcher の危険な利用を具体的な変数名と
ともに診断できるため，補助的な精密検査として残してよい．formal core の
安全性は `resolveVpShape` の成功や `VpUnknown` の解析には依存しない．

既知の移行対象には，標準ライブラリの `sortedList` と `assocMultiset`，意図的な
反例を持つ `minitest/008-ppval-atom-env.egi`，一部 database sample がある．
標準ライブラリは安全な pattern view へ移行するか，warning 付き extension として
境界を明記する．

## Lean 機械化への反映

現在の Lean には次の候補部品がある．

- `Syntax.lean` の `capturedExprs`／`capturedExprsList` は，pp とパターンを対応付けて
  `#$y` に捕捉される式を集める．
- `WellTyped.lean` の `VPScoped`／`VPScopedList` は，実行時 matcher 値の全節に
  ついて捕捉式が原子入力文脈で型付くことを要求する．

必要な機械化は次である．

1. `PPat` に `NoHoleBeforePVal` の実行可能な判定と命題的仕様を定義する．
2. `ConsistentClauses` または matcher literal の source well-formedness に，全節の
   `NoHoleBeforePVal` を追加する．
3. pp 型付け，利用者パターン型付け，pp/pattern 対応から，捕捉位置の入力文脈が
   `Γatom` のままであることを示す．
4. 3から `VPScoped` 相当を導く健全性補題を証明する．
5. matcher value，環境，slot，積 matcher，matching state，MNode を通して
   整形式性を保存する．
6. PPP 保存の `PPP-VAL` ケースで捕捉結果の型を無条件に供給する．
7. matching-state preservation と型安全性から capture-admissibility oracle を除く．

`VPScoped` と `capturedExprs` は，実行時の到達事象を記述する述語／抽出関数として
再利用できる．高階 matcher flow を解析するソースアルゴリズムとして使う必要はない．

P2 の capability／target 分離とは独立であり，P2 の二 sort 型や producer-flow
summary に capture effect を追加しない．P2 の covered safety へ接続するときだけ，
source matcher well-formedness の一成分として本条件を要求する．

## 完了条件

### 固定済みの設計判断

- [x] 決定可能な局所判断 `NoHoleBeforePVal` を定義した．
- [x] 不透明・高階な matcher flow を追跡せず，すべての matcher 定義の
      整形式性で安全性を運ぶ方針を固定した．
- [x] hole-before-`#$` を formal core の必須表現力から外した．
- [x] `assoc`／`rvAssoc` など，引数順の異なる full-language pattern view で
      表現力を回復する案を採用し，その view 機構と formal core との接続自体は
      P1の証明対象に含めない方針を固定した．
- [x] formal core の拒否と Egison の warning-only extension の境界を固定した．
- [x] P2 の capability 基盤とは独立にする方針を固定した．

### 残る反映・証明作業

- [ ] Lean に `NoHoleBeforePVal` と matcher well-formedness を実装する．
- [ ] ソース整形式性から全到達捕捉の `VPScoped` 相当を導く．
- [ ] PPP 保存と matching-state preservation から捕捉許容性 oracle を除く．
- [ ] 次 matcher，積 matcher，パターン関数，連言・選言，MNode，再帰 matcher の
      保存補題と回帰例を追加する．
- [ ] Egison に定義時 warning と回帰テストを追加する．
- [ ] 英語論文と日本語論文で定義，補題，定理境界，実装範囲を同期する．

## 参照ポインタ

- 論文：
  [`main.tex`](../../type-pm-paper/main.tex) の `sec:matchers`,
  `sec:metatheory`, `lem:ppp-preservation`, `app:proof-cases`,
  `sec:implementation`
- 日本語版：
  [`ja/main.tex`](../../type-pm-paper/ja/main.tex) の同じラベル
- 操作的意味論：
  [`TypePM/Semantics.lean`](../TypePM/Semantics.lean) の `PPM`／`MAtom`
- pp とパターンの構文：
  [`TypePM/Syntax.lean`](../TypePM/Syntax.lean) の `PPat`／`capturedExprs`
- pp／パターン型付け：
  [`TypePM/Typing.lean`](../TypePM/Typing.lean) の `PPTy`／`PatTy`／
  `ConsistentClauses`
- 候補不変量：
  [`TypePM/WellTyped.lean`](../TypePM/WellTyped.lean) の `VPScoped`
- PPP 保存：
  [`TypePM/Metatheory/Preservation.lean`](../TypePM/Metatheory/Preservation.lean)
- 型安全性：
  [`TypePM/Metatheory/TypeSafety.lean`](../TypePM/Metatheory/TypeSafety.lean)
- Egison の局所検査：
  [`Type/Infer.hs`](../../egison/hs-src/Language/Egison/Type/Infer.hs) の
  `resolveVpShape`, `vpAlign`, `checkVpScope`
- 実測例：
  [`minitest/008-ppval-atom-env.egi`](../../egison/minitest/008-ppval-atom-env.egi)
