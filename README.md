# type-pm-mech — Egison core の機械化

## 最上位目標

本リポジトリの完成目標は，次を正確に主張できる機械化を与えることである．

> The soundness of executable type inference for the Egison core is mechanized in Lean 4.

具体的には，整形式な frozen signature と入力 context の下で executable `infer` が
成功したならば，その結果に対応する宣言的な `HasTy` 導出が必ず得られることを証明する．
利用者が成功 trace に対する `WBridgeWF` を別途仮定する conditional reconstruction は
中間定理とし，`WBridgeWF` 自体を `infer` の各再帰ケースが保存する不変量から導出する．
completeness と full principality，および Egison コンパイラ全体の検証はこの目標に
含めない．

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．形式仕様は
[`tex/main.tex`](tex/main.tex)，Lean の public import surface は
[`TypePM.lean`](TypePM.lean) である．

現行 calculus は matcher producer と利用位置の要求を分ける．

```text
Matcher     κ τ   -- 値が生成時から持つ intrinsic capability
MatcherSlot κ τ   -- pattern site が要求する consumer capability
```

capability と target type は別 sort，別変数，別 substitution，別 quantifier を持つ．
producer から slot への接続は対称単一化ではなく producer-stable な one-way check で
行う．動的定理は concrete source/runtime judgments だけを使う．

## 証明している範囲

### Source typing

- lambda，application，`let`，tuple，data constructor，primitive，`something`
- matcher literal，`matchAll`，pattern function
- singleton direct-self の単相 `fix f x.e`
- user pattern，primitive-pattern pattern，primitive data pattern，clause／arm
- actual clause からの決定的 evidence，`PPatCapsAt`，`ShapeCap`，`CoverageOK`

matcher literal の型付けは，actual clause list に対する `CatchAllLast`，data-arm
exhaustiveness，binder 線形性，`CoverageOK` を必須とする．coverage を欠く literal を
追加 mode で受理する経路はない．
Frozen signature の lookup table は有限 map として扱い，pattern-function 名の
非重複性を `FrozenSigWF` が明示的に保持する．
Pattern-function 定義の本体は freeze 済みの完全な signature で型付けする一方，
自身の scheme は generalization の ambient free-variable 集合から除外する．
自己 `papp` は `pval` 内の `matchAll` や matcher clause の next／arm body を含む
全構文を走査して拒否するため，別定義への参照を許しながら直接自己再帰を受理しない．

各 clause は最終 matcher capability でも添字付けされる．nested primitive-pattern
hole はその構造位置の capability と一致し，bare root hole だけが catch-all として
独立した slot capability を消費できる．Pattern constructor の capability projection は
partial evidence を返してよく，`CapCompatible` がそれを最終 capability の canonical
evidence と exact merge できることを要求する．このため，element capability を直接は
観測しない nullary `nil` も周囲の list capability と整合できる．

Scheme の宣言的な利用は二段階である．最初に量化 capability を binder-local な
capability variable へだけ写し，その結果に量化 target binder だけを support とする
構造的な target substitution を順に適用する．宣言的 relation 自体は binder の像の
相異性や ambient freshness を要求しない．Algorithm W はこの relation を強化した witness として，
両 sort の binder へ互いに異なる fresh variable を signature と context の自由変数に
対して割り当てる．
別 scheme の局所 binder 名はこの ambient scope に含めない．利用側の consumer
demand に合わせて value producer の capability を構造化する instance は作れない．
二段階は一つの global paired substitution へ潰さず，capability binder-local な
variable mapping の後へ target specialization を順に適用する．従って，後段が挿入した
自由 capability と同じ
番号の量化 binder があっても捕捉しない．型付け導出の後続輸送も，producer の
capability に対する variable-only mapping と target-only specialization に制限する．
この宣言的 post は単射性，像の相異性，ambient freshness を要求せず，W の強い
finite-support chain から忘却して得る．
`let` の輸送では，内側の generalization binder を target ambient の外へ局所的に
freshen してから導出を再構成する．これにより，外側の instance が導入した自由変数と
数値 identifier が一致しても捕捉されない．この freshening は導出される補題であり，
source typing や scheme 等式を追加前提にしない．

### Inference

二種 substitution を持つ executable Algorithm W が expression，pattern，slot，
matcher literal を検査する．各 fresh value instance の producer variable を
`protectedCaps` に記録し，全 solver step がそれらを固定することを実行時にも証明上も
監査する．matcher inference は coverage／exhaustiveness checker を必ず実行する．
Pattern constructor の未観測位置は fresh capability で埋め，literal 全体の prevailing
substitution が確定してから raw hole dual を一度だけ解決する．その後，全 clause の
evidence と `PPatCapsAt` check を最終 capability に対して再計算する．
再構成では生成時の raw provenance と，substitution 適用後の実際の index で構造を追う
terminal derivation を分ける．nested child の raw index と親の raw field index が
構文的に同一であることは仮定しない．

W について主張するのは停止する checker と conditional reconstruction soundness で
あり，completeness や full principal-type theorem ではない．成功 trace の supply，
binder，solver replay，cross-sort-aware な逐次 post 合成，terminal context までの
instance 合成，generalization，coverage checker に関する名前付きの algorithmic 条件から，
concrete declarative `HasTy` を再構成する．後段 post の target component は前段 target
range に後段 capability action も適用するため，二 sort の componentwise 合成や誤った
可換性は仮定しない．
これらの条件に `HasTy` 自体や同型の導出を oracle として含めない．

### Runtime safety

runtime matcher value は，生成元の actual clause list と現在の clause cursor を別々に
保持する．suffix cursor は一つの atom dispatch の内部だけで使い，公開 state では
値・captured environment・tree・stack 全体に `Pristine` を要求する．`ValueTy` は
intrinsic capability，target，captured environment，source matcher derivation，coverage
を保持する．matching state の型付けは atom ごとの
prevailing substitution，pattern-function node の隔離された parameter context，
残余 actual argument，内部 stack を追跡する．

Ordered dispatch は失敗済み clause prefix を `DispatchTrace` で追跡する．Frozen
signature の pattern-constructor capability 一意性と coverage-index coherence により，
structured pattern が先行する対応 clause をすべて飛ばして bare-hole catch-all へ到達する
不正な branch を排除する．

`CoreSafety` は次を個別に取り出せる形でまとめ，`core_safety` が concrete
judgment 上の証明を与える．

1. pristine な typed environment からの expression evaluation の preservation
2. matching state 一段の preservation
3. matching state の local progress
4. 到達可能な全 state の型付け
5. 成功した terminal match substitution の型付け
6. 上の終端性質としての matcher consistency

正当な match failure（後続 state が空）は stuck ではない．値パターン式が原子入力の
context で型付くことは局所 `CaptureAdm`，一段の dispatch が必要とする局所評価・decode
結果は `StepReady` として明示する．前者は該当する preservation にだけ，後者は
progress にだけ必要であり，一般の program termination は仮定しない．

### Recursive matcher regressions

[`TypePM/P2/RecursiveExamples.lean`](TypePM/P2/RecursiveExamples.lean) は，外部の
型付け済み matcher 定数ではなく，実際の `fix self m. matcher ...` 本体を検査する．

- list: direct-self source typing と W の成功
- paper-complete multiset interface: list とは別の self binder／clause list に対する
  source typing と W の成功
- simplified multiset: `join` 一般節不足により source coverage と W が失敗
- structured consumer が polymorphic producer を強化しようとする入力は W が失敗
- 量化 binder と target specialization 内の自由 capability が同じ番号でも，ordered
  binder-local instance と let generalization が成功

## 明示的な境界

次はこの formal core の主張に含めない．

- Algorithm W の completeness／full principality
- alias，mutual recursion，transform，高階 origin を含む一般 producer-flow 解析
- raw declaration から frozen signature を構築する validator
- full Egison の warning mode，module/import persistence，標準ライブラリ移行
- CAS の target-indexed pattern view
- capture admissibilityそのものの証明，一般の評価停止性

## モジュール

| 層 | 主なファイル | 内容 |
|---|---|---|
| 型代数 | `Syntax`, `Substitution`, `Relation`, `CapMatch`, `Unification` | 二 sort，代入，自然性，one-way match，solver |
| capability | `Observability`, `Shape`, `Projection`, `Canonical`, `CapTarget`, `Recursion` | 観測可能性，evidence，projection，direct-self shape fold |
| source | `Term`, `ClauseEvidence`, `Source`, `SourceSubstitution`, `SourceGeneralization`, `SourceMetatheory`, `PatternFunction` | concrete syntax と宣言的型付け，coverage，安全な一般化と輸送 |
| runtime | `Semantics`, `Dynamic`, `Preservation`, `DynamicMetatheory`, `Reachability`, `Safety` | 評価・matching semantics，state invariant，preservation/progress/safety |
| W | `InferenceBase`, `Inference`, `InferenceRegression`, `InferenceHistory`, `Reconstruction`, `BridgeChecks`, `Soundness` | executable inference，state-threading 回帰，append-only history，producer audit，bridge audit，declarative reconstruction，concrete safety composition |
| 回帰 | `ClauseEvidenceExamples`, `GeneralizationRegression`, `RecursiveExamples` | evidence，binder collision，recursive list/multiset の正負例 |

各ファイルは `TypePM/P2/` 以下にある．

## 検証

Lean 4 toolchain は [`lean-toolchain`](lean-toolchain) で固定し，外部依存や Mathlib は
使わない．

```sh
lake build
```

形式仕様 PDF は必ず `tex/` の Makefile を使う．

```sh
cd tex
make
```

出力は `tex/type-pm-mech.pdf` である．`sorry`，`admit`，`axiom` は使用しない．
