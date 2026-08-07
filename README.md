# type-pm-mech — Egison core の機械化

非 CAS の Egison core（`Matcher κ τ`／`MatcherSlot κ τ` の二 sort capability calculus）を
Lean 4 で機械化するリポジトリである．文書は次のように分ける．

- この README — 最上位目標・設計原理・達成済みの主柱・ロードマップ（大局）
- [`docs/details.md`](docs/details.md) — モジュール単位の詳細仕様・証明状況・回帰一覧（詳細）
- [`tex/main.tex`](tex/main.tex) — 形式仕様
- [`CLAUDE.md`](CLAUDE.md) — 作業規律

Lean の public import surface は [`TypePM.lean`](TypePM.lean) にある．

## 最上位目標

完成目標は，Egison core の **demand-directed な注釈不要性**（annotation-freeness）の
機械化である．その前提となる仕様を，推論器から独立した構文主導の状態付き judgment
`DDTyping` として定義する方針に固定する．完成定理は `DDTyping` に対する公開推論器の
受理完全性である：

```text
∀ signature e τ,
  DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`DDTyping` は式層（pattern-free 断片）に対して
[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean) で定義済みである（pattern 層の
規則と受理完全性定理は未）．内部には fresh supply `q` と prevailing
substitution `S` を入出力で thread する synthesis／checking の二判断を置く：

```text
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       -- DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  -- DDCheck
```

closed wrapper `DDTyping` は `initialSupply signature context` と identity substitution
から開始し，終端 substitution を raw result に適用した型を公開する．実行関数の成功や
`CoreTyping` の存在を前提にした定義ではなく，fresh allocation，通常 solve，coercion
selection，左から右の構文走査を帰納規則として独立に記述する．core の構文
（[`TypePM/Term.lean`](TypePM/Term.lean)）自体には型注釈の形がないので，上の完成定理が
「`DDTyping` を持つ closed program は注釈なしで受理される」の正確な主張である．

これと区別して，広い `HasTy` を前提とする命題

```text
∀ signature e τ,  HasTy signature [] e τ → (infer signature [] e).isSome
```

を `Coherent.WideAnnotationFree` と呼ぶ．これは完成目標でも open goal でもなく，境界を
固定するために残した**恒久的に反証済みの命題**である（`wideAnnotationFree_refuted`）．
宣言的 `HasTy` の無条件 coercion 規則は動的安全性の包絡としては維持するが，受理完全性の
前提としては広すぎる．

## 設計原理: slot-demand coercion

coercion 挿入の根本原則は **demand-directed** であり，その demand の唯一の形は
**expected type の head が `MatcherSlot` であること**（slot-demand）である．

`DDCheck` は必ず先に期待型なしで式を synthesize し，その出力 state `q₁; S₁` を exact
coercion cut とする：

```text
q₀; S₀; Γ ⊢ e ⇒ τraw ⊣ q₁; S₁
head (S₁ τexpected) = MatcherSlot のときだけ coercion branch を検討
q₁; S₁ から source と expected を整合
```

non-identity coercion を選べるのは，この cut で `S₁ τexpected` の slot head が既に露出
している場合だけである．checking 開始前の `S₀` でも全走査後の substitution でもなく，
synthesis 後かつ当該 coercion 前の `S₁` を見る．coercion branch は raw source の形に
よる三形に閉じ，**非恒等 coercion の終点は常に slot** である：

| raw source | 選ばれる plan |
|---|---|
| `Matcher κ τ` | `matcherToSlot`（producer-stable one-way） |
| product-of-matchers | `productMatcher; matcherToSlot`（whole-product-first の二段） |
| product-of-slots | `slotTuple`（一段） |

空 product は両 recognizer に一致するため matcher-first の二段経路を選ぶ．

この一本化の根拠は実行時意味論である：タプルが product matcher として振る舞うのは
**matcher として消費される瞬間**であり，言語組み込みの消費位置（`matchAll` の matcher
位置・matcher clause の next-matcher 位置）が要求する型はすべて slot である．expected
head が `Matcher` に確定している位置（matcher 引数を宣言した署名 constructor 等）は
producer の転送であり，raw `Matcher` の通常単一化だけを許す — そこへの product 渡しは
coercion の対象ではなく，意図された拒否である．

付随する規律：

- λ domain は任意の型として選ばず fresh metavariable とする．application は function
  synthesis，fresh domain／codomain，通常 alignment，argument synthesis，domain check
  の順で state を thread し，list 構文も左から右へ進める．
- 要求が未確定なら source は raw synthesized type のままである．通常 alignment が期待
  meta をその raw 型へ固定できるが，coercion を成立させるために slot head を発明しない．
  各 solve delta はその時点で解く constraint に対する MGU または one-way solution に
  限定し，無関係な meta を同時に構造化しない（no-guess）．
- coercion 可否を semantic entailment で定義せず，通常の unification が失敗してから
  coercion branch を試す方式（負前提）も採らない．branch は unification 前に visible な
  slot head から決定し，その branch の solve が失敗すればその check は失敗する．
  この構文走査の順序自体が正当な demand の由来を与えるため，別の demand-origin token や
  ordered existential context は導入しない．
- selector の決定性と head 構成子の排他性は補題として示す．expected 側の場合分けが
  slot 一種であることが，この排他性証明と `DDCheck` の規則数を最小にする．

関連研究からの採否は絞ってある：Dunfield–Krishnaswami からは algorithmic judgment の
input/output state threading だけを採り，ordered existential context は採らない．
Kießling–Luo 流の「unification 失敗後に coercion を探索する」負前提は採らない．
OutsideIn(X) は guess-free solver と algorithmic completeness 条件の先例として参照する
が，constraint-generation／solving 分離は採らず，`DDTyping` 自身が構文走査中に state と
solve を逐次 thread する．出典と詳細は [`tex/main.tex`](tex/main.tex)．

**現行実装との差分**: executable selector `expectedCoercionSource` は slot-demand に
一本化済みである（matcher-expected で product lift 単独を選んでいた旧分岐は段階 3-0 で
撤去し，対応回帰を負例へ反転した）．残る差分は一つ：現行 selector は product の
source view を `S₁ τraw` ではなく raw `τraw` から認識する．定義済みの `DDAlign` は
仕様として cut-resolved view `S₁ τraw` 上の `demandClass` で分岐する．この
**raw-source visibility** は demand の権威ではなく実装上の死角であり，最初の受理定理
では条件 `RawSourceVisible` として隔離し，後に cut-indexed coercion event で外す
（段階 4-1）．

## 達成済みの主柱

> The soundness of executable type inference for the Egison core is mechanized in Lean 4.

- **公開 inference の soundness** — `infer = some r` の成功等式だけから宣言的 `HasTy` を
  返す（`infer_success_sound`）．`infer` は停止する raw W 走査 `inferRaw` と有限な
  fail-closed terminal validator の合成で，呼び出し側の整形性仮定や bridge 証明書を
  要求しない．
- **動的安全性** — `core_safety` は唯一の global 条件 `FrozenSigWF`（実行可能 checker
  `frozenSigWFCheck` で確立）から preservation／local progress／reachability／matcher
  consistency の 6 項を与える．
- **対称 MGU の完全なメタ理論** — 最汎性（`universal` certificate）・fuel 単調性・
  ∃fuel solvability completeness・公開 wrapper の可解性 iff．
- **origin-aware paired unifier** — ledger（`rigid`／`renameOnly`／`structuralFlexible`）
  方向付きの二 sort kernel，soundness＋admissibility＋origin-relative factorization，
  W の全 solve への接続と export freeze event．
- **DM 断片の宣言側** — 一 sort Damas–Milner 体系の二 sort 体系への埋め込み
  （`DM.HasTy.emb`）と全 coherence（`dm_coherent`）．
- **principality の反例** — `(something, something)` の二重型付けにより無制限
  principality は偽（`no_principal_type`）．受理完全性とは両立する（反例が否定するのは
  推論結果からの代入による全型付けの回収であって，受理そのものではない）．

`sorry`／`admit`／`axiom`／oracle premise はゼロである．いずれの詳細も
[`docs/details.md`](docs/details.md)．

## 意図された境界

- `WideAnnotationFree` — 恒久的に反証済み（上述）．
- `nestedCapProgram`（と swapped 版）— demand の無い位置の coercion に依存する例．
  拒否が意図された挙動であり，`DDTyping` に導出を持たない（将来 inversion で固定）．
  `let` 多相化した `nestedCapLetProgram` は受理される正例．
- matcher-expected 位置への product-of-matchers 渡し — 意図された拒否
  （段階 3-0 で負の回帰として固定済み）．
- 非主張: 広い `HasTy` 前提の completeness，無制限 principality，一般 producer-flow
  解析（alias／mutual recursion／高階 origin），raw declaration からの signature
  validator，一般の評価停止性，full Egison の warning mode／module persistence／標準
  ライブラリ，CAS の target-indexed pattern view，Egison コンパイラ全体の検証．

## ロードマップ

各段は独立に主張として成立する形で積む．済／未は 2026-08 時点．

### 段階 1: coherent surface typing 基盤 — 済

reconstruction certificate `ExprDeriv` への定義的 abbreviation として 10 family の
coherent surface typing（`Coherent.CoherentExpr` ほか）を公開し，surface への忘却・
推論成功からの `infer_success_coherent`・product lift の raw-source provenance 添字・
旗艦例の coherent instance・pval-free 吸収補題まで完了．

### 段階 2: Damas–Milner 断片の全受理

宣言側（DM 埋め込み・match-free 全 coherence・`dm_coherent`）は完了．算法側の現状：

1. **済** 対称 MGU の最汎性・単調性・∃fuel solvability・公開 wrapper の可解性 iff．
2. **済** 受理ギャップ三系統の機械化 — or pattern（修正して受理側へ），nested matcher
   capability（意図された拒否として固定），capability freeze（`packProgram` を受理側へ
   反転）．
3. **済** or-pattern binder の整合（`alignBindings`: 名前の位置照合＋型の単一化）．
4. **大半済** origin-aware paired unifier — kernel・W 接続・export freeze・単制約の
   局所因子化まで済．残: safe-rename 条件の全 traversal 保存と legacy terminal guard の
   接続．
5. **大半済** fuel 単調性と solvability — 対称 kernel は完了．残: origin-aware kernel の
   solvability completeness と固定 bound 十分性．
6. **一部済** `inferRaw` の trace-level factorization — StateExtension／AdmissibleTrace／
   FactorizingTrace を `inferRaw_runInvariants` に統合済み．残: trace 合成の明示前提
   （residual admissibility／solvability・export safe-rename）を全 traversal で保存する
   証明．
7. **一部済** terminal validator の受理 — 多相 `let` 証人の end-to-end 受理は固定済み．
   残: 任意の DM raw 成功に対する trace invariant の一般証明．
8. 到達点: `DM.HasTy → infer 受理`（古典的 ML の注釈不要性保証）．

### 段階 3: `DDTyping` と条件付き受理完全性

0. **済** selector の slot-demand 一本化 — `expectedCoercionSource` から
   matcher-expected 分岐を撤去し，受理回帰を反転した
   （`CertifiedInferenceRegression` の selector 検査は identity へ・application guard は
   拒否へ；`ApplicationCoercionRegression` の宣言導出は wide 包絡の意図された受理ギャップ
   として維持）．`HasTy`・Safety・reconstruction certificate は不変
   （`coerceProductMatcher` は slot-demand 二段の中間段として残る）．
   `nestedCapProgram` の拒否機構は「lift 後の rigid 比較」から「demand 不在による
   head 不一致」へ変わったが，拒否自体は不変である．原則そのものも selector の定理
   （`expectedCoercionSource_slotDemand`／`expectedCoercionSource_matcherExpected`）
   として機械化した．
1. **式層済** `DDTyping` の定義 — 推論器から独立な帰納的 `DDSynth`／`DDCheck`
   （[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean)）を式層（pattern-free
   断片）に対して定義した．設計原理節のとおり synthesis-first・slot-demand（分岐は
   cut-resolved view 上の決定的 `demandClass`）・no-guess（各 solve delta は当該
   constraint の関係的 MGU か exact one-way 解）で，実行関数や
   `ElaborableHasTy := ∃ CoreTyping` を定義に含めない．closed wrapper `DDTyping`，
   prevailing replay（`ReplayExtends`）と supply 単調性，判断レベルの slot-demand
   定理（`DDAlign.slotDemand`／`DDAlign.matcherExpected`），coercion 正例と
   matcher-expected 拒否の対（`DemandTypingRegression`）まで機械化済み．
   残: pattern 層 family（`matchAll`・matcher literal・matcher-bodied `fix`）の規則．
2. 未: `DDTyping` の基本メタ理論 — state extension・prevailing replay・freshness・solve
   delta の relevance・`HasTy` への忘却・`CoherentExpr` への変換．境界例は
   `nestedCapProgram` の不在 inversion と `nestedCapLetProgram` の構成で固定する．
3. 未: 現行実装に対する最初の受理定理 —
   `DDTyping + RawSourceVisible + FreezeCompatible → infer 受理`．二条件は demand の
   由来を定義する条件ではなく，現行実装との対応条件である．
4. 未: principal-core factorization の**存在定理**（∀ typing ∃θ plan）を先に立て，
   canonical boundary（substitution が coercible head を導入しない等）を定義してから
   条件付き一意性を扱う．定理は acceptance・存在・（canonicalization 後の）一意性の
   三本に分ける．slot-demand 一本化により demand 側の synthesis は Matcher 終点 plan を
   生成しないため，反例の coercion 重なりの一方は構造的に消える．

### 段階 4: `DDTyping` 受理完全性の最終形

1. 未: solve-cut event（cut-indexed coercion event）を導入し，prevailing substitution 後
   に初めて product head が現れる正当な case も selector が扱えるようにして
   `RawSourceVisible` を外す．
2. **大半済** W の origin-aware paired solver 化と export freeze（`packProgram` ギャップ
   解消済み）．残: safe rename の terminal bridge と trace factorization による
   `FreezeCompatible` の除去．
3. 未: canonical core judgment の critical pair 解消と，canonical boundary 下の full
   plan uniqueness・置換への naturality．
4. 到達点: `DDTyping signature [] e τ → (infer signature [] e).isSome`．前提は
   `DDTyping` だけとし，`WideAnnotationFree` は復活させない．

## モジュール

| 層 | 主なファイル | 内容 |
|---|---|---|
| 型代数 | `Syntax`, `Substitution`, `Relation`, `CapMatch`, `Unification` | 二 sort，代入，自然性，one-way match，solver |
| capability | `Observability`, `Shape`, `Projection`, `Canonical`, `CapTarget`, `Recursion` | 観測可能性，evidence，projection，direct-self shape fold |
| source | `Term`, `ClauseEvidence`, `Source`, `SourceSubstitution`, `SourceGeneralization`, `SourceMetatheory`, `PatternFunction` | concrete syntax と宣言的型付け，coverage，安全な一般化と輸送 |
| elaboration | `Elaboration`, `CoreTyping`, `CanonicalCoercion`, `CapabilityOrigin`, `PairedUnification`, `CoherentSurface`, `CoherentTyping`, `DemandTyping` | surface root factorization，raw-threaded recursive core head factorization，outer-plan normalization，origin-sensitive phased post，origin-aware paired solver kernel，pattern-local coherent surface 境界，mutual coherent surface typing，反証済み wide 注釈不要性境界，式層の demand-directed judgment（`DDSynth`／`DDCheck`／`DDTyping`） |
| runtime | `Semantics`, `Dynamic`, `Preservation`, `DynamicMetatheory`, `Reachability`, `Safety`, `RuntimeAgreementBridge` | 評価・matching semantics，state invariant，preservation/progress/safety，global agreement からの derivation-local mirror 構成 |
| W | `InferenceBase`, `Inference`, `InferenceLedgerAdmissibility`, `InferenceLocalFactorization`, `InferenceTraversalLocalFactorization`, `InferenceTraceFactorization`, `InferenceFreezeTransport`, `InferenceAdmissibleTrace`, `InferenceTraversalAdmissibleTrace`, `InferenceInput`, `InferenceHistory`, `InferenceStateExtension`, `InferenceTraversalStateExtension`, `InferenceRunInvariants`, `Reconstruction`, `BridgeChecks`, `CertifiedInference`, `InferenceRegression`, `Soundness` | raw W 走査，origin-admissible local solve／全 traversal の局所因子化証明書／scoped trace 合成／selective freeze 輸送／全 traversal 不変量の統合，入力整形性，append-only history，全 traversal の supply／producer state extension，terminal validation，declarative reconstruction，公開 inference soundness，concrete safety composition |
| 回帰 | `ClauseEvidenceExamples`, `GeneralizationRegression`, `CertifiedInferenceRegression`, `AcceptanceGapRegression`, `DMTerminalAcceptance`, `ApplicationCoercionRegression`, `DemandTypingRegression`, `RecursiveExamples`, `ProducerStrengtheningRegression`, `PatternCtorCapabilityRegression`, `DynamicSafetyRegression`, `DynamicCaptureRegression`, `DynamicDispatchRegression`, `PatternFunctionSafetyRegression` | evidence，source-level binder collision，domain-directed coercion，公開 inference soundness，DM 多相 let の terminal 受理，demand-directed judgment の具体導出と slot-demand 境界対，recursive matcher の旗艦例と正負例，producer non-strengthening と PAT-CON の public control twin，空／非空 runtime signature，capture，型付き ordered dispatch を含む動的安全性の具体適用 |

各ファイルは `TypePM/` 以下にある．各モジュールの詳細仕様と回帰の正負境界は
[`docs/details.md`](docs/details.md)．

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

出力は `tex/type-pm-mech.pdf` である．`sorry`，`admit`，project-defined `axiom` は
使用しない．主定理，一般補題，および `#guard`／kernel reduction で評価する小さな回帰は
kernel が検査する．一部の大きな具体的実行回帰で用いる `native_decide` だけは Lean の
native compiler を追加で信頼するため，この二層を区別する．
