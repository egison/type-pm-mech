# type-pm-mech — Egison core の機械化

非 CAS の Egison core（`Matcher κ τ`／`MatcherSlot κ τ` の二 sort capability calculus）を
Lean 4 で機械化するリポジトリである．文書は次のように分ける．

- この README — 最上位目標・設計原理・達成済みの主柱・ロードマップ（大局）
- [`docs/details.md`](docs/details.md) — モジュール単位の詳細仕様・証明状況・回帰一覧（詳細）
- [`tex/main.tex`](tex/main.tex) — 形式仕様
- [`CLAUDE.md`](CLAUDE.md) — 作業規律

Lean の public import surface は [`TypePM.lean`](TypePM.lean) にある．

## 最上位目標

Egison core の唯一の source typing discipline は，demand-directed・構文主導・状態付きの
judgment `DDTyping` である．完成目標は，この source typing に対する注釈不要性
（annotation-freeness），すなわち公開推論器との受理対応である：

```text
∀ signature e τ,
  DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`DDTyping` は推論器の成功を定義に含めない独立仕様であり，pattern 層 family を含む全構文層に対して
[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean) で定義済みである（受理完全性
定理は未）．内部には fresh supply `q` と prevailing
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

歴史的な帰納型名 `HasTy` は，Lean 内では `SemanticTyping` という役割名を与えた
state-free な semantic/safety certificate として残す．これは closure／matcher value typing，
preservation，公開推論成功の再構成が消費する内部判断であって，source program の受理可能性を
定義する第二の typing discipline ではない．次の命題

```text
∀ signature e τ,  HasTy signature [] e τ → (infer signature [] e).isSome
```

は内部 semantic envelope 全体を推論器が受理するという誤った強化であり，
`Coherent.WideAnnotationFree` という**恒久的に反証済みの回帰命題**としてだけ残す
（`wideAnnotationFree_refuted`）．source typing や完成目標として扱わない．

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
  各 solve delta はその時点で解く constraint に対する **exact MGU**（最汎・制約変数の
  外では恒等・像も制約変数の内・solved form＝冪等）または one-way solution に限定し，
  無関係な meta には触れない（no-guess）．このうち「構造化も衝突もしない」は MGU 仕様の
  普遍性だけから定理として従い，exactness 条項が除くのは残余のリネーム自由度である．
  制約外のリネームを許すと scheme binder を capture して value-flow instance の輸送が
  壊れ，制約内でも自明に成立する制約上の involutive swap は support／range を満たした
  まま prevailing 吸収（文脈型の terminal 輸送）を壊す．どちらも境界定理として固定
  してあり，前者は support／range 条項が，後者は solved-form 条項が除く．
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

- **公開 inference の semantic soundness** — `infer = some r` の成功等式だけから内部
  `SemanticTyping`（実装名 `HasTy`）を返す（`infer_success_sound`）．`infer` は停止する raw W 走査 `inferRaw` と有限な
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
- **semantic envelope の principality 反例** — `(something, something)` の二重型付けにより
  `SemanticTyping` 全体の無制限 principality は偽（`no_principal_type`）．これは public
  source typing `DDTyping` の型決定性を否定しない．

`sorry`／`admit`／`axiom`／oracle premise はゼロである．いずれの詳細も
[`docs/details.md`](docs/details.md)．

## 意図された境界

- `WideAnnotationFree` — 内部 semantic envelope を source acceptance と取り違えた命題として
  恒久的に反証済み（上述）．
- `nestedCapProgram`（と swapped 版）— demand の無い位置の coercion に依存する例．
  拒否が意図された挙動であり，`nestedCapProgram` が `DDTyping` に導出を持たないことは
  inversion で固定済み（`nestedCapProgram_no_ddTyping`／swapped 版
  `nestedCapSwappedProgram_no_ddTyping`）．`let` 多相化
  した `nestedCapLetProgram` は受理される正例で，`DDTyping` 導出も持つ．
- matcher-expected 位置への product-of-matchers 渡し — 意図された拒否
  （段階 3-0 で負の回帰として固定済み）．
- capability freeze の忘却側境界 — 量化 matcher producer の instance capability を
  demand 判断は構造化できるが宣言的 value flow は variable-only であり，
  `DDTyping` と内部 `SemanticTyping` が分離する（`capFreeze_forgetting_gap`）．同じ分離は
  量化 seed なしでも `let` 一般化が capability meta を束縛する形で生じる
  （`letCapFreeze_forgetting_gap`）ため，忘却定理の freeze 側対応条件は文脈側の
  述語だけでは表せず，`let` 一般化 scheme も制約する形で述べる．
- 非主張: 広い `SemanticTyping` 前提の completeness，無制限 principality，一般 producer-flow
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
   として維持）．`SemanticTyping`・Safety・reconstruction certificate は不変
   （`coerceProductMatcher` は slot-demand 二段の中間段として残る）．
   `nestedCapProgram` の拒否機構は「lift 後の rigid 比較」から「demand 不在による
   head 不一致」へ変わったが，拒否自体は不変である．原則そのものも selector の定理
   （`expectedCoercionSource_slotDemand`／`expectedCoercionSource_matcherExpected`）
   として機械化した．
1. **済** `DDTyping` の定義 — 推論器から独立な帰納的 `DDSynth`／`DDCheck`
   （[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean)）を，pattern 層 family
   （user pattern・primitive pattern・data pattern・arm・clause）と `matchAll`・
   matcher literal・matcher-bodied `fix` の規則を含む全構文層に対して定義した．
   設計原理節のとおり synthesis-first・slot-demand（分岐は cut-resolved view 上の
   決定的 `demandClass`）・no-guess（各 solve delta は当該 constraint の関係的 MGU か
   exact one-way 解）で，実行関数や `ElaborableHasTy := ∃ CoreTyping` を定義に
   含めない．pattern 層の fresh 割当は実行走査の supply-indexed 純関数 twin として
   写し，matcher literal の finalization は宣言規則と同一の executable coverage
   検査群を消費する．closed wrapper `DDTyping`，prevailing replay（`ReplayExtends`）
   と supply 単調性（全 judgment），判断レベルの slot-demand 定理
   （`DDAlign.slotDemand`／`DDAlign.matcherExpected`），coercion 正例と
   matcher-expected 拒否の対，or-pattern `matchAll` program と delegating matcher
   literal の旗艦導出（`DemandTypingRegression`）まで機械化済み．
2. **一部済** `DDTyping` の基本メタ理論 — state extension・prevailing replay は定義と
   同時に済．solve delta の no-guess 定理も済: MGU 仕様の普遍性だけから，ある unifier が
   固定する変数は最汎解で必ず変数像を持ち（fixing-unifier 形），制約外の変数は高々
   リネームされ（構造化されず），相異なる制約外変数は衝突しない（`CapMGU`／
   `TargetMGU`／`PairedMGU` の各 sort）．その残余のリネーム自由度が有害であることは
   **value-flow transport 境界**として固定した: `?1 ≐ Int` の最汎解が無関係な
   `?3`／`?9` を交換でき，部分一般化 scheme `∀9. 9 → 3` を capture して instance の
   輸送を壊す（`valueFlow_transport_needs_exactness`）．これを受け，判断の全 solve
   premise は **exact MGU**（`ExactCapMGU`／`ExactTargetMGU`／`ExactPairedMGU` =
   最汎 ∧ 制約変数外は恒等）へ強化済み（具体 witness は全部 exact）．境界例も固定済み:
   `nestedCapLetProgram` の `DDTyping` 導出は実行 raw result shape と同じ型で閉じ，
   `nestedCapProgram` には任意の published type・任意の最汎 delta 選択に対して導出が
   存在しない（`nestedCapProgram_no_ddTyping`；swapped 版
   `nestedCapSwappedProgram_no_ddTyping` は鏡像の強制連鎖 — 先行する product 引数が
   domain を product 頭へ固定し，後続の bare matcher raw が衝突する — で同じく不在）．
   **freeze 軸が忘却にも
   要ることは判定済み**: 量化 matcher producer `m : ∀κ α. Matcher κ α` を束縛した文脈上で
   `(λh. (h something, h m)) (λz. z)` は，`m` の fresh instance capability を ordinary
   matcher-pair solve が `Any` へ構造化して `DDTyping` で閉じるが，宣言側は value-flow
   instance の variable-only 条件が同じ型を拒否する（`capFreeze_forgetting_gap`）．
   よって任意文脈の無条件忘却は偽であり，忘却定理は freeze 側対応条件
   （段階 3-3 の `FreezeCompatible` に対応）を持つ形が最終形である．さらに同じ分離は
   量化 seed なしでも生じる：単相 seed `m2 : Matcher (con "c" []) Int` の下の
   `let f = λx. Pack x in (f something, f m2)` は mid-derivation の generalize が
   capability meta を自ら束縛し，二利用が instance capability を発散して構造化して
   `DDTyping` で閉じるが，どの λ domain 選択も内部 semantic typing で両利用を満たせない
   （`letCapFreeze_forgetting_gap`）．よって freeze 側条件は文脈側の述語だけでは
   表せず，`let` 一般化 scheme も制約する．**忘却の transport 前提として exactness に
   solved-form（冪等）条項を追加済み**：support／range を満たす制約内 involutive swap が
   prevailing 吸収を壊すことは境界例で固定し（`inConstraintSwap_forces_solvedForm`），
   吸収（`Subst.seq_absorbs_of_idempotent`）と solved-form 合成
   （`Subst.seq_idempotent`）を忘却の主帰納の道具として用意した．
   **freshness 不変量は完成**: 供給有界性述語（`Cap`／`Ty`／`Dual`／`Subst`／scheme
   三種／context 三種の `BoundedBy`）・supply extension に沿う単調性・恒等／apply／seq の
   閉包・**exact delta の有界性**（像有界性は exactness の条項に採用:
   `RangeWithin`／`CapRangeWithin`）・one-way 解の有界性・checking cut と全整列関係の
   有界性・**pattern 層 supply-twin の有界性**（fresh target・skeleton freshening・
   shared assignment・matcher-bodied placeholder；署名スキームは閉性条件
   `FrozenSig.SchemesClosed` で消費し，evidence 射影パイプラインの自由変数保存
   （merge／finalize／shape 推論・certified projection・clause evidence）に載せる）・
   **9-family judgment の有界性 sweep**（有界な入力 state から出力 substitution・
   公開型・dual・binding・hole ledger のすべてが出力 supply で有界；matcher 規則は
   terminal hole capability の有界性を evidence 連鎖で通す）・closed wrapper の系
   （`DDTyping.published_boundedBy` = 公開型は initialSupply を拡張する終端 supply で
   有界）．残: `SemanticTyping` への semantic erasure（freeze 側条件つき）・
   `CoherentExpr` への変換．
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
| elaboration | `Elaboration`, `CoreTyping`, `CanonicalCoercion`, `CapabilityOrigin`, `PairedUnification`, `CoherentSurface`, `CoherentTyping`, `DemandTyping` | surface root factorization，raw-threaded recursive core head factorization，outer-plan normalization，origin-sensitive phased post，origin-aware paired solver kernel，pattern-local coherent surface 境界，mutual coherent surface typing，反証済み wide 注釈不要性境界，全構文層の demand-directed judgment（`DDSynth`／`DDCheck`／`DDTyping`・pattern 層 family） |
| runtime | `Semantics`, `Dynamic`, `Preservation`, `DynamicMetatheory`, `Reachability`, `Safety`, `RuntimeAgreementBridge` | 評価・matching semantics，state invariant，preservation/progress/safety，global agreement からの derivation-local mirror 構成 |
| W | `InferenceBase`, `Inference`, `InferenceLedgerAdmissibility`, `InferenceLocalFactorization`, `InferenceTraversalLocalFactorization`, `InferenceTraceFactorization`, `InferenceFreezeTransport`, `InferenceAdmissibleTrace`, `InferenceTraversalAdmissibleTrace`, `InferenceInput`, `InferenceHistory`, `InferenceStateExtension`, `InferenceTraversalStateExtension`, `InferenceRunInvariants`, `Reconstruction`, `BridgeChecks`, `CertifiedInference`, `InferenceRegression`, `Soundness` | raw W 走査，origin-admissible local solve／全 traversal の局所因子化証明書／scoped trace 合成／selective freeze 輸送／全 traversal 不変量の統合，入力整形性，append-only history，全 traversal の supply／producer state extension，terminal validation，declarative reconstruction，公開 inference soundness，concrete safety composition |
| 回帰 | `ClauseEvidenceExamples`, `GeneralizationRegression`, `CertifiedInferenceRegression`, `AcceptanceGapRegression`, `DMTerminalAcceptance`, `ApplicationCoercionRegression`, `DemandTypingRegression`, `RecursiveExamples`, `ProducerStrengtheningRegression`, `PatternCtorCapabilityRegression`, `DynamicSafetyRegression`, `DynamicCaptureRegression`, `DynamicDispatchRegression`, `PatternFunctionSafetyRegression` | evidence，source-level binder collision，domain-directed coercion，公開 inference soundness，DM 多相 let の terminal 受理，demand-directed judgment の具体導出と slot-demand 境界対（or-pattern `matchAll`・delegating matcher の旗艦込み），recursive matcher の旗艦例と正負例，producer non-strengthening と PAT-CON の public control twin，空／非空 runtime signature，capture，型付き ordered dispatch を含む動的安全性の具体適用 |

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
