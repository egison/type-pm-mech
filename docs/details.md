# type-pm-mech 詳細仕様

この文書は Lean module と現在の証明境界を説明する．設計の要約は
[`README.md`](../README.md)，規則を先頭から読むための形式仕様は
[`tex/main.tex`](../tex/main.tex) を参照する．

## 1. 型と source form

[`TypePM/Syntax.lean`](../TypePM/Syntax.lean) は capability と target type を別 sort として
定義する．

```text
κ ::= χ | Any | Skolem s | K(κ̄) | (κ̄)
τ ::= α | Int | D(τ̄) | (τ̄) | τ → τ | Matcher κ τ | MatcherSlot κ τ
```

`Matcher κ τ` は matcher producer の型，`MatcherSlot κ τ` は matcher を消費する expected
type である．`Subst` は capability substitution と target substitution の組であり，target
substitution の像にも capability が現れるため，合成 `Subst.seq` は二 sort をまたいで定義する．

[`TypePM/Term.lean`](../TypePM/Term.lean) は lambda，application，`let`，direct-self `fix`，
tuple，data constructor，primitive，`something`，`matchAll`，matcher literal と pattern
syntax を定義する．source term 自体に型注釈 form はない．

matcher literal の各 clause は primitive pattern，next-matcher expression，arm list を持つ．
[`TypePM/ClauseEvidence.lean`](../TypePM/ClauseEvidence.lean) と
[`TypePM/Shape.lean`](../TypePM/Shape.lean) は hole の順序，shape capability，catch-all，coverage
に必要な有限 evidence を定義する．

## 2. 唯一の source typing: DDTyping

[`TypePM/DemandTyping.lean`](../TypePM/DemandTyping.lean) が raw な DD family を，
[`TypePM/DemandTypingOrigin.lean`](../TypePM/DemandTypingOrigin.lean) が各 raw derivation と同じ形の
intrinsic Origin certificateを定義する．式層は次の二判断とalignmentからなる．

```text
q; S; Ω; Γ ⊢ e ⇒ τraw      ⊣ q'; S'; Ω'    synthesis
q; S; Ω; Γ ⊢ e ⇐ τexpected ⊣ q'; S'; Ω'    checking
S; Ω ⊢ τraw ≼ τexpected    ⊣ S'             alignment
```

`DDTyping Σ Γ e τ` は `initialSupply Σ Γ`，`Subst.id`，空ledgerから上のsynthesisを開始し，
終端substitutionをraw resultへ適用した型だけを公開するwrapperである．Lean上ではraw derivation
とOrigin certificateを別のinductive familyにすることで，既存のtyping構造を複製せずにledgerの
履歴をintrinsicに対応付けている．source acceptance はこの二つを常に組にするため，Origin情報を
忘れた公開wrapperは持たない．

### 2.1 三つの状態：fresh supply，substitution，origin ledger

`q = (nextCap, nextTy)` は二 sort の fresh counter である．capability metavariable を一つ
生成すれば `nextCap` だけ，target metavariableを一つ生成すれば `nextTy` だけ進む．`S` は
その構文位置までに確定した paired substitution である．`Ω` はcapability variableの由来と，
そのcutで許されるsolveを記録するledgerである．子judgmentの出力 `q'; S'; Ω'` は左から右に
次の子へ渡される．未登録のkeyはrigidとして扱う．

| origin | 意味 | 許される像 |
|---|---|---|
| `rigid` | signature／入力context由来 | 恒等のみ |
| `renameOnly` | 外部へ流れるproducer instance | 非structural variableへのrename |
| `structuralFlexible` | constructor内部またはconsumer demandの局所変数 | cut内のstructural solve |

expression schemeとpattern-function dual schemeのbinder imageはinstance生成時から
`renameOnly` になる．constructor／primitive instance，fresh pattern hole，`fixMatcher`
placeholderなどDD内部の局所変数は `structuralFlexible` として生成される．constructor exportは
公開payloadに残る像のstructural leafだけを選択的にfreezeする．matcher finalizationは最終
capabilityに現れる全DD-owned explicit ledger keyのstructural leafをfreezeするため，matcher開始前に
生成された `fixMatcher` placeholderのowned leafも対象になる．

lambda は fresh domain を生成する．application は fresh domain／codomain pair を用意し，function
synthesis，function typeとのordinary alignment，argument checkingの順でstateを渡す．`let` はvalueの
終端型を prevailing context に対して一般化し，body lookup ごとに fresh instance を作る．さらに
Origin certificateは，bodyの終端substitutionを適用しても同じschemeが得られること，すなわち
`S' σ = Gen(Σ, S' Γ, S' τ1)` を要求する．これにより一般化後のproducer binderを後続solveで
遡及的に構造化できない．

### 2.2 synthesis-first checking

`DDCheck` の規則は一つだけである．

1. expected type を使わず `DDSynth` する．
2. synthesis の出力 cut でalignmentを一回行う．

このため matcher producer と slot demand の対応は，特定の source constructor ではなく
expected type が現れる任意の checking cut で起こる．関数引数，`matchAll` の matcher 引数，
matcher clause の next matcher はすべて同じ規則を使う．

### 2.3 alignment

`demandClass` は cut-resolved source と expected type を分類する．非恒等 branch を選べるのは
resolved expected head が `MatcherSlot` の場合だけである．

- matcher → slot: producer-stable one-way capability match と target unification
- product of matchers → slot: whole-product matcher lift の後に matcher → slot
- product of slots → slot: slot-tuple lift
- slot → slot: ordinary paired equality
- その他: ordinary paired equality

expected head が matcher または未解決変数なら coercion branch はない．通常 equality の失敗を
負 premise として別 branch を選ぶこともない．branch は head から先に一意に決まり，選択した
solve が失敗すれば judgment は成立しない．

`ExactCapMGU`，`ExactTargetMGU`，`ExactPairedMGU` は次を要求する．

- constraint を解くこと
- 任意の解がその解を経由して因子化すること
- constraint 外で恒等であること
- constraint variable の像が constraint 内に収まること
- solved form，すなわち冪等であること

`OneWayDelta` は producer capability を保持し，consumer slot 側だけを producer に合わせる
exact solution である．ordinary equalityとone-way solveはいずれも，そのcutの `Ω` に対して
admissibleでなければならない．特に `renameOnly` keyはvariableへのrenameしか許さず，
`structuralFlexible` keyだけがconstructor，product，`Any` などへ構造化できる．

### 2.4 pattern，arm，clause

式以外の DD family は executable traversal と同じ割当順を関係として記述する．主な family は
`DDPattern`／`DDPatterns`，`DDPPat`／`DDPPats`，`DDDPat`／`DDDPatList`，`DDArm`／
`DDArms`，`DDClause`／`DDClauses` である．

pattern constructor は target instance と capability projection を同じ signature entry から
得る．or-pattern は両 alternative の binder 名を位置対応させ，型を align する．matcher
literal は全 clause の共有 target を生成し，shape，catch-all order，data-arm exhaustiveness，
primitive-pattern binder 線形性，arm binder 線形性，`CoverageOK` を finalization で要求する．

### 2.5 DDTyping と ledger の証明済み性質

- alignmentの非 ordinary branchならexpected typeはslot-headedである．
- matcher-headed expected type の derivation は ordinary equality に限られる．
- 各 family の出力 supply は入力 supply を拡張する．
- 出力 substitution は入力 substitution と solve delta の chronological replay に分解できる．
- 公開型，dual，bindings，hole ledger の flexible variable は終端 supply で有界である．
- exact MGU は constraint 外の fresh variable を slot や matcher に構造化しない．
- 全expression／pattern／arm／clause familyにraw derivationと同型のOrigin certificateがある．
- ledger transitionは入力ledgerを保ち，fresh supplyの範囲内だけを追加・freezeする．
- scheme／dual instance，constructor／fresh allocation，selective export，matcher finalizationの
  origin policyがcertificateのconstructorに固定されている．
- `capFreezeProgram` と `letCapFreezeProgram` はpublic `DDTyping`では導出不能である．

## 3. executable inference

[`TypePM/Inference.lean`](../TypePM/Inference.lean) の `inferRaw` は停止する W-style traversal で
ある．`InferState` は supply，prevailing substitution，constraint trace，source trace，
capability-origin ledger を持つ．`infer` は `inferRaw` の結果を有限の `wBridgeCheck` で検査し，
失敗時は `none` を返す．

executable traversalのorigin ledgerとDD側のintrinsic Origin certificateは，同じ三originと
freeze policyを別々の役割で記録する．前者はsolverを実行時にfail closedにする状態，後者は
関係的なDD derivationで各solveが許可されたことを証明する履歴である．consumer demandのために
生成したvariableはstructural solveを許せるが，value-flow instanceやexport後のproducer imageは
variable-onlyにfreezeされる．

推論 proof modules の役割は次の通りである．

| module | 内容 |
|---|---|
| `InferenceLedgerAdmissibility` | 各 solve の origin policy 適合性 |
| `InferenceLocalFactorization` | local solver result の因子化 |
| `InferenceTraversalLocalFactorization` | traversal 全体への局所因子化の持上げ |
| `InferenceTraceFactorization` | trace の chronological factorization |
| `InferenceFreezeTransport` | freeze event を越える substitution 輸送 |
| `InferenceHistory` | append-only history |
| `InferenceStateExtension` | 単一操作の supply／state extension |
| `InferenceTraversalStateExtension` | traversal 全体の extension |
| `InferenceAdmissibleTrace` | 単一操作の trace admissibility |
| `InferenceTraversalAdmissibleTrace` | traversal 全体の admissibility |
| `InferenceRunInvariants` | 成功 run の不変量の統合 |
| `BridgeChecks` | fail-closed terminal validator の soundness |

`InferenceInputWF` は入力境界を記述するが，公開成功定理の caller premise ではない．validator
が必要な `WBridgeWF` を成功 result から構成する．

`DemandTypingInferenceSoundness` は，successful traversalのsupply，prevailing substitution，origin
ledgerをDD derivationの入出力indexへ直接一致させるexact-state runを構成する．expression synthesis／
checkingに加えてuser pattern／pattern listのrunもあり，pattern listのnil／cons，pattern variable，
wildcard，value pattern，parameter embed，tuple patternまで実行分岐から`DDPatternOrigin`へ再構成済みで
ある．残るuser-pattern分岐はpattern constructor，and／or，pattern-function applicationであり，
primitive／data pattern，arm，clauseとともに後続の相互帰納へ統合する．

## 4. RuntimeTyping は内部 certificate である

[`TypePM/Source.lean`](../TypePM/Source.lean) の `RuntimeTyping` は fresh supply，prevailing solver
state，origin ledger を消去した expression certificate である．`ExprsTy`，pattern resolution，
arm／clause certificate と相互に構成される．source acceptance は定義しない．

coercion certificate も同じ消去原則に従う．`RuntimeTyping` と `ValueTy` の matcher-to-slot
constructor は終端 producer／consumer capability 間の `CapabilityDemand` だけを持ち，raw
matching，MGU，後続 substitution を持たない．slot-to-slot solve は終端 slot 型の等しさで
premise を書き換えるため，専用 runtime constructor を持たない．実行可能な
`MatcherToSlotRawCert`／`SlotToSlotRawCert` は reconstruction 境界まで保持され，そこで終端
demand または等式へ射影される．

この family が state-free であることにより，closure body，matcher literal，substitution，
preservation の帰納法を推論器の履歴から独立に記述できる．その代わり，DD derivation から
certificate を作る際には，消去する state が value-flow freeze 条件を満たした証明が必要になる．

[`TypePM/Reconstruction.lean`](../TypePM/Reconstruction.lean) の `ExprDeriv` family は successful
inference trace の proof-relevant reconstruction である．constructor が `RuntimeTyping` を
oracle として保持することはない．`ExprDeriv.toRuntimeTyping` が最終的に state-free certificate
へ射影する．

```text
infer Σ Γ e = some result
  → infer_success_reconstruct
  → ExprDeriv Σ (result.S Γ) e result.resolvedTarget
  → infer_success_runtimeTyping
  → RuntimeTyping Σ (result.S Γ) e result.resolvedTarget
```

`CoherentExpr` は `ExprDeriv` の役割名であり，別コピーの judgment ではない．`CoreTyping` と
canonical coercion plan は reconstruction の factorization を表す内部補助層である．

`PrincipalityCounterexample` は `RuntimeTyping` certificate family 全体を source principal-type
specification として使えないことだけを示す．`DDTyping` の principality に関する結果ではない．

## 5. capability freeze と state erasure の基盤

scheme captureの表現上の解消に向け，`Syntax`／`PolySyntax`にscheme専用の`PolyCap n`／
`PolyTy n m`を導入した．bound variableは`Fin n`／`Fin m`，solver metavariableは既存の
`CapVar`／`TyVar`であり，通常の`Cap`／`Ty`とunifierにはbound constructorを追加しない．
`PolyTy.applyMeta`はmetavariable節だけを書き換え，通常型からのliftはbound occurrenceを生成できない．
`PolyScheme`は二つのbinder数とdependentな`PolyTy` payloadだけを保持する．named binder listは
`PolyScheme.close`の入力に限られ，閉じたschemeには保存されない．具体化はcaller-suppliedな
`Fin` openingを通じてのみ通常の`Ty`へ戻る．
旧binder-collision形について，同じ自然数番号のsubstitution imageが`bound`ではなく`mvar`に留まり，
後続substitutionとの逐次適用でもbound nodeが固定される回帰を構成済みである．`Fin` indexにより
payloadは構成時からalpha-normal formであり，substitutionごとのfresh nominal renameを必要としない．
現在は移行基盤の段階であり，以下の既存`Scheme.NoCapture`分析はexpression `Scheme`のpayload移行後に
無条件のpoly-substitution algebraへ置換する．

capability-origin ledgerは現行DD familyへ統合済みである．raw derivationと同じ構造のOrigin
certificateが，instance，fresh allocation，selective export，matcher finalization，solve
admissibility，`let` terminal generalization stabilityを追跡する．public `DDTyping` は空ledgerから
このcertificateを構成できるderivationだけを受理する．

`DemandTypingRegression` の二例は，Origin情報を追跡しない局所導出で起きる境界を固定する．

- `capFreezeProgram`: context の量化 matcher scheme の fresh capability instance を後続solveが
  `Any`へ構造化するraw derivation．
- `letCapFreezeProgram`: lambda domain のcapability metaを `let` generalizationで束縛し，bodyの
  lookup後に別の構造へ強化するraw derivation．

これらは現行public `DDTyping` の正例ではない．Origin-awareな局所solveが該当deltaを拒否することは
証明済みであり，プログラム全体について `¬ DDTyping capFreezeProgram` と
`¬ DDTyping letCapFreezeProgram` を閉じるnegative regressionも構成済みである．or-pattern，
delegating matcher，let-polymorphic producerのpositive Origin certificateも構成済みである．

state erasureについては，入力cutより前のorigin policyを保存するsupply-scopedな
`AdmissiblePostBetween` と，終端substitutionをそのpostへ分解する`StateFactorization`を定義済みで
ある．postの合成，boundedness，ledger refinement，alignment全分岐のfactorizationに加え，式，
user pattern，primitive pattern，data pattern，arm，clauseを含む全14 Origin familyについて，
`SchemesClosed`と入力boundednessだけからfactorizationを得る無前提の相互定理がある．canonical
scheme／dual-scheme instanceについては，rename-only ledgerからbinder imageだけのvariable-only
transportを回収する補題もある．また，variable，literal，`something`，lambda，tupleについては
state-freeな`RuntimeTyping`への初期erasure補題を構成済みである．後続cutを量化した強いerasureは，
literal，`something`，lambda，tuple，fix，application，`fixMatcher`，constructor／primitive，
expression list，checking cut／listへ拡張済みであり，data／primitive patternの4 familyは無前提の
相互closureまで完成している．user patternのexpression-independentなleaf／tuple／listとmatcher armの
再帰合成も同じlater-cut invariantを持ち，value patternはchild expressionのlater-cut erasureから
構造的に合成できる．and／or，pattern-function application，pattern constructorにもchild invariant
からの構造補題があり，`matchAll`もtarget／pattern／matcher／bodyの4 child invariantとfactorizationを
共通の最終cutへ合成する構造補題を持つ．pattern constructorでは後続cutの`CapCompatible`安定性が
明示的な残余条件として分離されている．

本質的な残課題は，完成したstate factorizationを使い，Origin derivationの各constructorから
`RuntimeTyping` constructorへ情報を射影する相互帰納証明を完成することである．この射影では
supply，prevailing substitution，ledgerを
消去しつつ，scheme instanceのvariable-only条件，matcher final capability，terminal hole capability，
`let` generalizationを回収する．variable leafではactual marked ledgerからfresh binder imageの
variable-only性を回収できるが，binder-maskingによる`Scheme.applySubst`の合成則は
`AdmissiblePostBetween`だけからは従わない．context／schemeと前後のsubstitutionのboundedness，
solved form，actual marked ledgerへのadmissibilityをすべて満たしながら合成則が壊れるbinder-capture
反例もLeanで固定した．そのため，局所的なscheme compositionを明示する健全なtransport補題までを
切り出した．必要十分なrange hygieneの3経路を表す`Scheme.NoCapture`から逐次合成則を証明済みで
あるが，lookup時点がno-captureでも後続のadmissible suffixがcaptureを起こしてvalue-flow instanceを
失わせる第二反例がある．したがって，context中のschemeごとのavoidanceを後続solveで保存する状態が
必要であり，過去のleaf-local premiseだけでは足りない．
`Context.NoCapture`，context substitutionの逐次合成，binder-local instance composition，canonical
value-flow transportは証明済みであり，variable transportの残余はlookup前後の2つの`NoCapture`へ
簡約されている．clauseには
matcher finalizationが選ぶcapability／shape evidence，matcher producerにはscoped rename-only postを
total renamingへ拡張する補題が必要である．cut以上をidentityでmaskするtotalizationとbounded object上の
agreementは証明済みだが，producer外のstructural leafには適用できない．`RuntimeTyping` derivationの
存在をDDのpremiseにする定義は循環するため採らない．

## 6. dynamics と安全性

[`TypePM/Semantics.lean`](../TypePM/Semantics.lean) は type-erased evaluation と matching machine
を定義する．[`TypePM/Dynamic.lean`](../TypePM/Dynamic.lean) の `ValueTy` は literal，constructor，
tuple，closure，matcher literal，coerced matcher value を型付けする．closure body と matcher
literal は `RuntimeTyping` certificate を保持する．

[`TypePM/Preservation.lean`](../TypePM/Preservation.lean)，
[`TypePM/DynamicMetatheory.lean`](../TypePM/DynamicMetatheory.lean)，
[`TypePM/Safety.lean`](../TypePM/Safety.lean) は次を証明する．

- typed environment での expression evaluation は `RuntimeTyping` を `ValueTy` へ保存する．
- typed matching state の全 successor は typed である．
- 非終端 typed state は局所 `StepReady` の下で一段進む．
- 一段保存を反復し，到達可能な全 matching state が typed である．
- 空 stack に到達した成功 branch の substitution は source pattern の binding context で型付く．

空 successor list は正当な match failure であり stuck ではない．primitive-pattern 内の value
pattern capture は depth-first・左から右の `PPatCoreOrder` から導出する．

global 条件は `FrozenSigWF` だけである．`SignatureChecker` の `frozenSigWFCheck` が有限 checker，
`frozenSigWFCheck_sound` がその soundness を与える．

最終的に欲しい公開定理は次の合成である．

```text
DDTyping + FrozenSigWF
  → RuntimeTyping          全familyのstate factorization済み／runtime射影は未完成
  → runtime safety         証明済み
```

## 7. Damas–Milner 断片

[`TypePM/DamasMilner.lean`](../TypePM/DamasMilner.lean) は pattern-free な一 sort system を
`DM.Typing`／`DM.Typings` として定義する．recursion は core と同じ direct-self singleton に
制限される．`DM.Typing.emb` は capability binder を使わず二 sort の `RuntimeTyping` certificate
へ埋め込み，`dm_coherent` は reconstruction certificate まで持ち上げる．

[`TypePM/DMTerminalAcceptance.lean`](../TypePM/DMTerminalAcceptance.lean) は terminal acceptance
の具体例を固定する．全 `DM.Typing` に対する executable acceptance は未証明である．

## 8. 回帰の読み方

- `DemandTypingRegression`: raw DD の旧freeze反例，局所Origin拒否，public freeze負回帰，state replay，supply boundedness．
- `AcceptanceGapRegression`: or-pattern 正例，nested matcher DD 拒否，constructor export freeze．
- `ApplicationCoercionRegression`: 関数引数の slot demand と matcher-expected 拒否．
- `CertifiedInferenceRegression`: terminal validator と成功時 reconstruction．
- `ProducerStrengtheningRegression`: producer freeze の拒否／control 成功．
- `PatternCtorCapabilityRegression`: pattern-constructor capability projection．
- `PatternFunctionSafetyRegression`: pattern function と matching safety の接続．
- `DynamicSafetyRegression`: end-to-end evaluation safety．
- `DynamicCaptureRegression`: value-pattern capture．
- `DynamicDispatchRegression`: matcher cursor と dispatch．
- `RecursiveExamples`: list／multiset matcher，direct-self recursion，coverage．
- `GeneralizationRegression`: binder 番号衝突下の instance と generalization．
- `ElaborationRegression`: canonical coercion plan と reconstruction factorization．

正例と負例は設計境界を対で固定する．変更時は受理結果だけでなく，DD derivation，raw trace，
runtime certificate，実行結果のどの層を検査する回帰かを確認する．

DD関連moduleの役割は次のとおりである．

| module | 役割 |
|---|---|
| `DemandTyping` | raw DD family，ledger-aware alignment，pure ledger transition |
| `DemandTypingOrigin` | 全raw derivationに対応するintrinsic Origin certificateとpublic `DDTyping` wrapper |
| `DemandTypingLedgerMetatheory` | ledger extension，freeze，supply-scoped transition補題 |
| `DemandTypingOriginMetatheory` | 全Origin familyのledger evolution定理 |
| `DemandTypingInferenceSoundness` | successful executable traversalから`DDSynth`／`DDSynthOrigin`を再構成する直接soundness帰納パッケージ |
| `DemandTypingErasure` | state-erasure開発全体のpublic facade |
| `DemandTypingErasureCore` | scoped residual post，factorization core，初期runtime erasure |
| `DemandTypingErasureFactorization` | 全14 Origin familyのpremise-free state factorization |
| `DemandTypingErasureTransport` | canonical scheme instanceのbinder-image-local transport |
| `DemandTypingRegression` | raw境界，Origin-aware局所solve，DD回帰 |

## 9. 検証条件

全 module は [`TypePM.lean`](../TypePM.lean) から import される．変更後はリポジトリ直下で
`lake build` を実行する．形式仕様は `tex/` で `make` を実行し，`type-pm-mech.pdf` を生成する．
`sorry`，`admit`，project-defined `axiom`，typing derivation を premise に持つ oracle で証明を
埋めない．
