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

## 2. 唯一の source typing: SourceTyping

[`TypePM/DemandTyping.lean`](../TypePM/DemandTyping.lean) が raw な demand-directed family を，
[`TypePM/DemandTypingOrigin.lean`](../TypePM/DemandTypingOrigin.lean) が各 raw derivation と同じ形の
intrinsic Origin certificateを，
[`TypePM/DemandTypingTerminalAuditTree.lean`](../TypePM/DemandTypingTerminalAuditTree.lean) が
公開終端に固定した再帰的 audit と public wrapper を定義する．式層は次の二判断とalignmentからなる．

```text
q; S; Ω; Γ ⊢ e ⇒ τraw      ⊣ q'; S'; Ω'    synthesis
q; S; Ω; Γ ⊢ e ⇐ τexpected ⊣ q'; S'; Ω'    checking
S; Ω ⊢ τraw ≼ τexpected    ⊣ S'             alignment
```

`SourceTyping Σ Γ e τ` は `initialSupply Σ Γ`，`Subst.id`，空ledgerから上のsynthesisを開始し，
終端substitutionをraw resultへ適用した型だけを公開するwrapperである．Lean上ではraw derivation
とOrigin certificateを別のinductive familyにすることで，既存のtyping構造を複製せずにledgerの
履歴をintrinsicに対応付けている．source acceptance はこの二つに，同じOrigin proofを辿る
terminal auditを組み合わせる．Origin情報または公開終端で必要な三種のfactsを忘れた公開wrapperは
持たない．

ここでは次の三層を区別する．raw acceptance（raw受理）は，producer保護まで通った`inferRaw`の成功と，
そこから再構成される`DemandSynthRun`である．audited acceptance（監査済み受理）は，raw derivation，
Origin certificate，terminal auditをまとめた`SourceTyping`である．public acceptance（公開受理）は，
`inferRaw`の結果に有限の`wBridgeCheck`を適用する`infer`の成功である．唯一の公開source judgmentは
引き続き`SourceTyping`だけであり，`DemandSynthRun`を第二のsource型システムとして公開しない．一方，
`SourceTyping`自体がauditを含むため，`SourceTyping`と`infer`の受理同値は，raw derivationに対してauditが
完全であることを意味しない．

| 層 | Lean上の代表 | 含む条件 |
|---|---|---|
| raw受理 | `inferRaw`／`DemandSynthRun` | demand-directed traversal，Origin整合，producer保護 |
| 監査済み受理 | `SourceTyping` | raw derivationに三種のterminal auditを追加 |
| 公開受理 | `infer` | `inferRaw`成功後に`wBridgeCheck = true` |

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
placeholderなどdemand-directed内部の局所変数は `structuralFlexible` として生成される．constructor exportは
公開payloadに残る像のstructural leaf（capability構文中の変数）だけを選択的にfreezeする．
ここでfreezeとは，後続solveによるstructural strengtheningを禁止するための固定である．
matcher finalizationは最終
capabilityに現れるmatcher-owned leafをfreezeするが，active contextのtop-level slot demandまたは
direct-selfの引数slotから借りたleafは新規freeze対象から除く．例えば
`multiset : MatcherSlot κ α → Matcher (List κ) (List α)`の`κ`は引数から借りたinterfaceなので，
call siteで`Any`へ特殊化できる．一方，selfの結果だけに現れるleafや既にexport済みのleafは除外しない．

三状態の差は次の型推論例に現れ，それぞれの受理・拒否境界は機械化されている．
`Pack : ∀κ α. Matcher κ α -> Packed`へ`something`を渡す
programでは，constructor-localな`κ`を`structuralFlexible`として`Any`へ特殊化するため受理できる．
独立なconstructor instanceが返す`makeF : Matcher κ1 Int -> Int`と`makeM : Matcher κ2 Int`の適用は，
exportで`renameOnly`になった`κ2 := κ1`だけを必要とするため受理できる．一方，context lookupから得た
`producer : ∀κ. Matcher κ Int`を`Matcher (List Any) Int`要求へ渡すprogramは，rename-onlyな像を
`List Any`へ構造化できないため拒否し，最初からそのconcrete capabilityを持つcontrolだけを受理する．
入力contextに自由な`κr`を持つ`r : Matcher κr Int`は未登録すなわち`rigid`であり，`Matcher Any Int`
要求から`κr := Any`へcallerの仮定を書き換えない．したがって`structuralFlexible`は局所特殊化，
`renameOnly`はexport済みproducerのalpha-renamingと非strengthening，`rigid`は外部仮定の固定を担う．
`renameOnly`な`κn`と`structuralFlexible`な`κf`の等式は`κf := κn`へ向け，逆向きにはしない．exportは
`structuralFlexible -> renameOnly`へ一方向にfreezeする．ledgerはsolverの解を制限するが，coercion
branchの選択には使わない．

lambda は fresh domain を生成する．application は fresh domain／codomain pair を用意し，function
synthesis，function typeとのordinary alignment，argument checkingの順でstateを渡す．`let` はvalueの
終端型を prevailing context に対して一般化し，body lookup ごとに fresh instance を作る．さらに
Origin certificateは，bodyの終端substitutionを適用しても同じschemeが得られること，すなわち
`S' σ = Gen(Σ, S' Γ, S' τ1)` を要求する．これにより一般化後のproducer binderを後続solveで
遡及的に構造化できない．

### 2.2 synthesis-first checking

`DemandCheck` の規則は一つだけである．

1. expected type を使わず `DemandSynth` する．
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
solve が失敗すれば judgment は成立しない．`demandClass_variableExpected`，
`DemandAlign.variableExpected`，`expectedCoercionPlan_variableExpected`は，未解決expected variableが
関係的規則と実行selectorの両方でordinary／raw経路に限られることを直接固定する．

このno-guess方針とlistの左から右のstate threadingには観測可能な順序依存がある．well-formedな
`use : (MatcherSlot Any Int -> Int) -> Used`を持つclosed probeでは，
`lambda f. (use f, f something)`は最初のchecking cutが`f`のdomainをslotへ確定するため受理される．
逆順は最初の通常適用がdomainをraw `Matcher Any ?target`へ確定し，後続の`use`と一致しないため
拒否される．これは意図された設計境界であり，pre-scan，子の並べ替え，checking obligationの遅延，
source-order permutation invarianceは現行calculusに含めない．`AcceptanceGapRegression`はpublic
`inferType`の正負に加え，`demandedUseFirstProgram_sourceTyping`，
`ordinaryUseFirstProgram_not_sourceTypable`，`source_order_affects_source_typability`でsource judgment
レベルの正負を固定する．

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

### 2.4 文献用語との対応

現行識別子は実装上の不変量を正確に表すため維持する．次表の「近い文献概念」は同義語ではなく，
読者が既存文献から本開発へ移るための橋である．本開発固有の強化点を最終列に明記する．

| 現行概念 | 近い文献概念 | 出典 | 本開発での相違・強化 |
|---|---|---|---|
| `ExactCapMGU`／`ExactTargetMGU`／`ExactPairedMGU` | relevantなsolved-form idempotent MGU | Robinsonのfirst-order unification；Damas--Milnerのprincipal type-scheme | MGU性と冪等性だけでなくconstraint外の恒等性，両sortのsupport/range confinement，target像中のcapability rangeまで証明書に含める |
| `OneWayDelta`／`matchCap` | first-order matching（one-way solve） | producer/consumer非対称なmatchingの標準的な向き | consumer capabilityだけを束縛しproducerを固定した後，capability適用済みtargetのexact MGUも同じdeltaに含める |
| `q; S; Ω`（fresh supply・prevailing substitution・origin ledger） | ordered algorithmic contextとcontext application | [Dunfield--Krishnaswami 2013](https://doi.org/10.1145/2500365.2500582) | 一つのcontextではなく三成分に分離する．`q`は割当境界，`S`は解の情報増加，ledgerはcapability固有のsolve権限を担う |
| ledgerの`rigid`／`renameOnly`／`structuralFlexible` | rigid--flexible metavariable discipline | rigid parameterとflexible existentialを分けるunification／bidirectional typing | 二値ではなく，外部へ流れたproducerにalpha-renamingだけを許す中間状態`renameOnly`を持つ |

Dunfield--Krishnaswamiのcomplete contextは記号 `Ω` を使い，unsolved existentialを持たない．
本開発のledgerも内部文書で `Ω` と略記するが同じ対象ではないため，論文ではledgerに別記号を使う．

### 2.5 pattern，arm，clause

式以外の demand-directed family は executable traversal と同じ割当順を関係として記述する．主な family は
`DDPattern`／`DDPatterns`，`DDPPat`／`DDPPats`，`DDDPat`／`DDDPats`，
`DDArms`，`DDClause`／`DDClauses` である．

pattern constructor は target instance と capability projection を同じ signature entry から
得る．or-pattern は両 alternative の binder 名を位置対応させ，型を align する．matcher
literal は全 clause の共有 target を生成し，shape，catch-all order，data-arm exhaustiveness，
primitive-pattern binder 線形性，arm binder 線形性，`CoverageOK` を finalization で要求する．

### 2.6 SourceTyping と ledger の証明済み性質

- alignmentの非 ordinary branchならexpected typeはslot-headedである．
- matcher-headed expected type の derivation は ordinary equality に限られる．
- unresolved variable-headed expected type の derivation も ordinary equality に限られ，実行selectorは
  raw synthesized typeを保つ．
- 各 family の出力 supply は入力 supply を拡張する．
- 出力 substitution は入力 substitution と solve delta の chronological replay に分解できる．
- 恒等 substitution から始まる全14 raw demand-directed family は solved form を保存する．より一般に，各 family
  は入力 substitution の冪等性から出力 substitution の冪等性を導く．
- 公開型，dual，bindings，hole ledger の flexible variable は終端 supply で有界である．
- exact MGU は constraint 外の fresh variable を slot や matcher に構造化しない．
- 全expression／pattern／arm／clause familyにraw derivationと同型のOrigin certificateがある．
- ledger transitionは入力ledgerを保ち，fresh supplyの範囲内だけを追加・freezeする．
- scheme／dual instance，constructor／fresh allocation，selective export，matcher finalizationの
  origin policyがcertificateのconstructorに固定されている．
- variable instance は canonical scheme opening の代数的 transport で終端へ移す．追加の terminal
  facts は `let` generalization，matcher finalization，pattern-constructor compatibility の三種であり，
  再帰的 terminal audit が公開する終端 substitution に対して保持する．
- closed signature 上で terminal audit を持つ closed-program derivation は，全 family の相互 state erasure により
  `TypingInvariant` へ射影できる．
- source-facingな安全性境界では，このsignature closednessを`FrozenSigWF.schemesClosed`から
  供給し，callerに別premiseとして要求しない．
- public producer-strengthening regressionは多相producerの構造的strengtheningを拒否し，
  concrete producerと安全なvariable renamingを受理する．

## 3. executable inference

[`TypePM/Inference.lean`](../TypePM/Inference.lean) の `inferRaw` は停止する W-style traversal で
ある．`InferState` は supply，prevailing substitution，constraint trace，source trace，
capability-origin ledger を持つ．`infer` は `inferRaw` の結果を有限の `wBridgeCheck` で検査し，
失敗時は `none` を返す．

`inferRaw`の成功からは同じcut列を持つ`DemandSynthRun`を再構成できるが，この段階ではterminal auditも
`SourceTyping`も得ていない．`wBridgeCheck`が成功して初めて公開soundness定理が`SourceTyping`を構成する．
従って`inferRaw`成功を後二者と同一視してはならない．`SourceTyping`の存在と`infer`成功は，
`FrozenSigWF`の下では既存の受理同値定理どおり一致する．

executable traversalのorigin ledgerとdemand-directed側のintrinsic Origin certificateは，同じ三originと
freeze policyを別々の役割で記録する．前者はsolverを実行時にfail closedにする状態，後者は
関係的なdemand-directed derivationで各solveが許可されたことを証明する履歴である．consumer demandのために
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

`infer` 成功から `SourceTyping` へのsoundnessは三段で構成する．第一段はsolver bridgeとconstructor
sliceであり，successful traversalのsupply，prevailing substitution，origin ledgerをraw demand-directed
derivationの入出力indexへ正確に一致させる．第二段の10-family相互帰納はexpression synthesis／
checking，expression list，user pattern／pattern list，matcher，arm，clauseを同じfuel inductionで
再構成する．第三段はappend-only historyで全recursive callを一つのroot終端へ接続し，validatorの
`WBridgeWF`から `let` generalization，matcher finalization，pattern-constructor compatibilityの
三事実をterminal auditへ載せる．

公開定理はcaller premiseを成功等式だけに戻す．

```text
Inference.infer_success_sourceTyping :
  infer signature context expression = some result →
  SourceTyping signature context expression result.resolvedTarget
```

したがって `WBridgeWF` と `HistoryPrefix` はcertified runを組み立てる内部indexであり，公開APIへ
漏れない．この経路は `TypingInvariant` を介さずsource typingを直接構成する．一方，次節の
`infer_success_typingInvariant` は動的メタ理論向けの独立した内部経路として維持する．

逆向きの受理完全性はdemand-directedのOrigin treeとterminal auditを同時に再帰する．exact solver witnessを
実行solverのresultへ移し，fresh allocation，context normalization，producer protection，fuel boundを
保ったfuelled traversalを全expression／checking／pattern／arm／clause familyについて構成する．
demand-directed側と実行側のprevailing substitutionは同一である必要はなく，相互にfactorするidempotent stateの
`StateBisimulation`で結ぶ．このためraw metavariable名の違いを公開定理へ漏らさない．

各局所runは成功等式だけでなくvalidator eventのcoverage extensionを返す．ordinary eventは
traversal自身から，`let` generalization，matcher finalization，pattern-constructor compatibilityは
terminal auditから得る．ただしpattern constructorのauditはdemand-directed側のdual／capabilityを記録する一方，
実行traceはbisimilarだが名前の異なるoperandsを持ちうる．そこで`PairedValidatorRunExtension`は
両operandsとそのbisimulationを保持する．exact-state leafはその対角な特別場合として埋め込み，
matcher／`let` eventは各局所cutのdemand-directed／実行operandを保持したままpaired chronologyへ合成する．rootの
`PairedRootCertifiedSynthesis`はこのchronologyとtype／dual alignmentを束ね，三種のterminal-sensitive
条件をpaired witnessから`wBridgeCheck`の全有限条件へ射影する．Originとauditは`Prop`，concrete runは
`Type`なので，fuelに対するstrong recursionは各cutのpaired runを`Nonempty`で返す．canonical
initial cutで`PairedRootCertifiedSynthesis`へ束ね，公開facadeが受理命題の内部でのみその証明消去
境界を開く．

```text
SourceTyping.infer_isSome :
  SourceTyping signature context expression target →
  FrozenSigWF signature →
  (infer signature context expression).isSome = true
```

`FrozenSigWF`はM4と共有するglobal signature条件である．terminal factsをbisimulation越しに移す際，
その`schemesClosed`と`armExhaustiveBasic`を使う．`RawSourceVisible`，`FreezeCompatible`，solver
success，validator bridge，既知のinference successは公開premiseではない．ここで証明したのは
validator単体の任意のraw runに対する無条件完全性ではなく，terminal-audited `SourceTyping` fragmentから
再構成したtraceに対する受理完全性である．`TerminalAuditCounterexample`は，整形式signatureでも
`inferRaw`成功から`wBridgeCheck = true`は従わないことを具体的に示す．

soundnessと受理完全性は
[`TypePM/DemandTypingInferenceEquivalence.lean`](../TypePM/DemandTypingInferenceEquivalence.lean)
で合成する．中心定理`Inference.sourceTypable_iff_infer_isSome`は一般contextに対して

```text
FrozenSigWF signature →
  ((∃ target, SourceTyping signature context expression target) ↔
    (infer signature context expression).isSome = true)
```

を与える．`Inference.annotation_freeness`は空contextへの特殊化である．sourceの`Expr`には
type-ascription constructorがないため，型を入力として要求せずclosed termのsource typabilityを
判定できる，という意味でannotation-freenessと呼ぶ．`Inference.sourceTypableDecidable`は
`FrozenSigWF`の証明を受け，同じ実行可能なBoolean判定から
`Decidable (∃ target, SourceTyping ...)`を構成する．

型を返すAPIについては，`Inference.inferType_success_sourceTyping`が

```text
inferType signature context expression = some target →
  SourceTyping signature context expression target
```

を証明する．さらに`sourceTypable_iff_inferType_some_sourceTyping`は，source typabilityがあれば
`inferType`の具体的な返値とその返値自身の`SourceTyping` derivationを同時に得る．一方，入力した任意の
`SourceTyping` derivationのtargetと返値型が構文的に等しいとは主張しない．

`SourceTyping.target_unique_modulo_renaming`は，完全性内部の同じ決定的な実行runを共通代表として
二つの`SourceTyping` targetを結ぶ．各辺の`TargetRenaming`は，公開型に残るcapability／target variableの
全有限scope上でforward／reverse substitutionがpointwise inverseな`LocalRenamingOn`であり，
source targetと共通実行targetを両方向に写す．これは一般contextにも成立する．ただしinitial
supply以前のmetaまで固定する形は偽である．`f : ?0 -> ?0, x : ?1`のcontextで`f x`を導出すると，
argument constraint `?1 = ?0`のexact MGUをどちら向きに取るかにより`?0`と`?1`の双方を公開できる．
`DemandTypingTargetUniquenessRegression`は両方をterminal audit込みの`SourceTyping`として固定する．

[`TypePM/TypeInstance.lean`](../TypePM/TypeInstance.lean) は，二sort substitutionが変更できる有限scopeを
明示する`ScopedTypeInstance`と，source type自身の`fcv`／`ftv`をscopeに取る`TypeInstance`を定義する．
`Subst.restrict`はscope外を恒等に戻し，scopeがsourceのfree variableを含むとき型への作用を保存する．
instance witnessのchronological compositionを元のsource scopeへrestrictすることで，`TypeInstance.refl`と
`TypeInstance.trans`が成立する．`TargetRenaming`のforward／reverseはそれぞれinstance witnessになり，
`TargetRenamingEquivalent`は両方向の`TypeInstance`を与える．

[`TypePM/SourcePrincipality.lean`](../TypePM/SourcePrincipality.lean) の
`Inference.inferType_principal`は一般contextについて

```text
FrozenSigWF signature → inferType signature context expression = some principal →
  SourceTyping signature context expression principal ∧
  ∀ target, SourceTyping signature context expression target →
    TypeInstance principal target
```

を証明する．`inferType_closed_principal`は空contextへの公開特殊化である．この結果は
`TypingInvariant`のprincipality反例を使わず，`SourceTyping.target_unique_modulo_renaming`と
renamingからinstanceへの有限scope bridgeだけから従う．

open termのより精密な比較は
[`TypePM/RelativePrincipality.lean`](../TypePM/RelativePrincipality.lean) にある．
`ContextTargetInstance Γ τ Γ' τ'`は，`Γ`と`τ`のfree capability／target metaの和だけを変更する一つの
paired substitutionが，contextとtargetを同時に`Γ'`と`τ'`へ写すことを表す．
`SourceTyping.TerminalPair`は新しいsource judgmentではなく，既存のaudited `SourceTyping` witnessから
raw target，terminal substitution，Origin，terminal auditを保持したままterminal-normalized contextを
公開するviewである．`Inference.infer_relative_principal`は，成功runの
`ResolvedContext result.state.prevailing context`／`result.resolvedTarget`と，任意の`SourceTyping`
derivationのterminal pairが相互に`ContextTargetInstance`であることを示す．これによりexact MGUが入力metaを
どちら向きに解いても，contextとtargetを別々のsubstitutionで比較することなくopen principalityを述べられる．

## 4. TypingInvariant は内部 invariant である

[`TypePM/Source.lean`](../TypePM/Source.lean) の `TypingInvariant` は fresh supply，prevailing solver
state，origin ledger を消去した expression invariant である．`ExprsTy`，pattern resolution，
arm／clause certificate と相互に構成される．source acceptance は定義しない．

coercion certificate も同じ消去原則に従う．`TypingInvariant` と `ValueTy` の matcher-to-slot
constructor は終端 producer／consumer capability 間の `CapabilityDemand` だけを持ち，raw
matching，MGU，後続 substitution を持たない．slot-to-slot solve は終端 slot 型の等しさで
premise を書き換えるため，専用 `TypingInvariant` constructor を持たない．実行可能な
`MatcherToSlotRawCert`／`SlotToSlotRawCert` は reconstruction 境界まで保持され，そこで終端
demand または等式へ射影される．

`TypingInvariant.coerceProductMatcher` は product-to-slot の直接constructorへ融合せず，独立した
unary product liftとして維持する．融合は検討済みだが，`let`をまたいでmatcher viewの選択を
利用位置まで遅延できることと，明示的coercion planの二段構造を失うため採用しない．

この family が state-free であることにより，closure body，matcher literal，substitution，
preservation の帰納法を推論器の履歴から独立に記述できる．その代わり，`SourceTyping` derivation から
invariant を作る際には，消去する state が value-flow freeze 条件を満たした証明が必要になる．

[`TypePM/Reconstruction.lean`](../TypePM/Reconstruction.lean) の `ExprDeriv` family は successful
inference trace の proof-relevant reconstruction である．constructor が `TypingInvariant` を
oracle として保持することはない．`ExprDeriv.toTypingInvariant` が最終的に state-free invariant
へ射影する．

```text
infer Σ Γ e = some result
  → infer_success_reconstruct
  → ExprDeriv Σ (ResolvedContext result.state.prevailing Γ)
      e result.resolvedTarget
  → infer_success_typingInvariant
  → TypingInvariant Σ (ResolvedContext result.state.prevailing Γ)
      e result.resolvedTarget
```

`CoherentExpr` は `ExprDeriv` の役割名であり，別コピーの judgment ではない．`CoreTyping` と
canonical coercion plan は reconstruction の factorization を表す内部補助層である．

`PrincipalityCounterexample` は `TypingInvariant` family 全体を source principal-type
specification として使えないことだけを示す．`SourceTyping` の principality に関する結果ではない．

## 5. canonical scheme と terminal state erasure

### 5.1 canonical `Scheme`

expression scheme の表現は canonical `Scheme` に統一されている．scheme payload は
`PolyCap n`／`PolyTy n m` を使い，量化変数を `Fin n`／`Fin m` の bound index，solver が扱う
自由変数を `CapVar`／`TyVar` の metavariable として別 constructor・別 datatype に置く．したがって
unifier の通常型 `Cap`／`Ty` に bound constructor はなく，solver substitution が scheme binder を
捕捉する経路もない．`Scheme.applyMeta` は metavariable occurrence だけに作用し，bound index は
構造的に固定される．

generalization は signature と context の外にある solver metavariable を選び，その場で有限 index
へ close する．完成した `Scheme` は選択に使った nominal binder 名を保存しない．instance は
`ValueOpening` または `FreshOpening` という有限 opening を通して通常型へ戻り，canonical fresh
allocator は index `i` を incoming supply の `next + i` へ割り当てる．close／open 左逆，opening の
injectivity・freshness・boundedness，metavariable substitutionとの identity／composition／transport
は二 sort の payload 全体について証明済みである．同じ自然数を持つ bound index と自由
metavariable が衝突しないことも回帰で固定している．

### 5.2 solved-form preservation

state erasure は終端 substitution が solved form であることを使う．capability-only，target-only，
paired，二段階 matcher／slot solve，one-way capability matching の各局所操作について，入力が
冪等なら時系列合成後も冪等であることを証明している．この局所結果を traversal の順に合成し，
alignment family と，expression synthesis／checking，list，user／primitive／data pattern，arm，
clause，pattern-constructor capability を含む全14 raw demand-directed familyについて

```text
S.Idempotent → S'.Idempotent
```

を得る．公開 derivation は `Subst.id` から始まるため，その終端 substitution は無条件に冪等である．

### 5.3 terminal audit

Origin certificate は chronological な生成・solve・freeze を記録するが，`TypingInvariant` への射影は root の
終端 substitution で行う．そこで terminal audit は導出木を同じ形で辿り，追加の終端事実を必要とする
三つの境界を記録する．これは終端で何らかの再検査が必要であることを表すが，現在の各再検査がraw derivationに
対して完全であることまでは意味しない．`LetFacts` は終端 context／value から再計算した generalization の一致，
`MatcherFacts` は terminal hole capability から再収集した evidence，shape，clause capability，arm
exhaustiveness，coverage，`PatternCtorFacts` は終端 dual／capability 間の `CapCompatible` を保持する．
variable node 自体に追加 field はなく，canonical scheme opening の代数的 transportから終端instanceを
直接構成する．audit factsはsolver stateを `TypingInvariant` に持ち込まず，erasure時に必要な終端事実だけを
供給する．

`LetFacts` を省き，任意の後続substitutionを許す場合に局所cutだけを考えた反例は，空signature／contextのcutで value type が
`α0 -> α1`，cut substitutionが恒等写像の場合である．auditのない関係がこのcut以後の任意suffixを
許すと仮定する．cut schemeは
`Gen(∅, ∅, α0 -> α1) = ∀a b. a -> b`だが，bodyの後続solve
から生成されたかを問わずsuffix `R = [α1 := α0]`の後にrootで再計算すると
`Gen(∅, ∅, R(α0 -> α1)) = ∀a. a -> a`になる．閉じた二binder schemeへの`R`の作用は恒等なので，
`R(∀a b. a -> b) != ∀a. a -> a`である．auditなしではdomain／codomainを独立にinstantiateできる
過剰なschemeを保持するため，terminal auditはこのraw cutを拒否する．matcher／pattern constructorの
factsも，同じ再検査原理をterminal hole evidence／capability compatibilityへ適用する．このlet例は，
不一致を生む任意suffixの代数的な必要性を示すものであり，そのsuffixが実際のsource traversalから到達可能で
あることを示すsource programではない．実走査のlet eventについては，記録時のcontext，target，schemeが
正確で，append-only historyを通じて保存される局所履歴を構成的に証明した．一方，すべての後続solveが
各pending let cutのschemeを保存するという終端安定性は，別の全走査不変条件として未証明である．

これに対し，matcher finalizationには実際に到達可能な整形式・closed source programについて，terminal auditに
よる受理損失（rawでは受理されるが公開推論では拒否されること）がある．
`RecursiveExamples.listSignature`へ，`observability K = none`である観察不可能なcapability constructor `K`を
引数にだけ使う整形式なdata constructor

```text
consumeK : Matcher K Int -> Witness
```

を加える．一要素tupleを分解し，その要素を引数matcherへ委譲する二節matcherを`fix self argument`で包み，
次の閉じたlambdaを作る．`self`は使わず，`fix`は引数slot用の局所capabilityを生成するためだけに用いる．

```text
λ opaqueMatcher.
  (consumeK opaqueMatcher,
   (fix self argument.
      matcher [generalTuplePP(1) -> argument; catch-all]) opaqueMatcher)
```

`TypePM/TerminalAuditCounterexample.lean`はsignatureの`FrozenSigWF`を定理として証明する．compile-time
guardはraw traversalの成功とraw resolved target

```text
Matcher K Int -> (Witness × Matcher (K) (Int))
```

を計算し，通常の定理`raw_success_demand_synth_run`は任意のraw成功等式から対応する`DemandSynthRun`を
構成する．ここで右辺の`(K)`／`(Int)`は一要素product capability／typeである．9個の検査結果は

```text
(true, true, true, true, true, true, true, false, true)
```

であることもcompile-time guardで固定し，`traceFinalizationSuffixCheck`だけが失敗して公開`infer`は`none`を
返す．局所finalization時には
借用slotのcapabilityは変数なので`Shape.Evidence.known (.var κ)`として扱えるが，外側の適用でその変数が`K`へ特殊化される．
終端再検査は`Shape.ofCap K`をmatcher自身が観察した構造と同じ形に展開し，`observability K = none`のため
拒否する．しかしこのmatcherが直接観察するのは外側の一要素productだけであり，要素の観察は引数matcherへ
委譲している．従ってこれは，raw demand-directed derivationに対するterminal auditの受理損失を示す
具体的なsource反例である．

この反例が独立の宣言的型付けに対して「安全」となる定理はまだない．現在の安全性定理はauditを含む
`SourceTyping`を前提とするため，公開拒否された本例には適用できない．形式化済みなのは，閉lambdaが即座に
closureへ評価されること，具体的raw成功の計算とそれをdemand-directed derivationへ移す一般接続，および
拒否原因が上記一検査だけであることまでである．従って安全なprogram全体に対する損失の正確な範囲は
未確立である．

単に借用変数を早くfreezeすると，この例をraw solverで拒否するだけで，引数matcherに応じた意図的な
特殊化も失う．逆にすべてのopaque constructorをfinalizationで許すと，matcher自身が不透明な内部構造を
観察する不正な場合まで通す．修正候補は，matcher自身が得たevidenceと，引数slotから完全な値として借りた
capabilityの由来を区別し，後者を再帰的に観察しないように由来を追跡するfinalization，または同じ区別を保つ
終端での再型付けである．

capability-origin ledger と Origin certificate は引き続き instance，fresh allocation，selective
export，matcher finalization，solve admissibility を時系列に保証する．public producer-strengthening
regressionは多相producerの拒否をconcrete producerと安全なvariable renamingの成功と対にし，上の
局所cutだけを考えた反例は`LetFacts`の必要性を示す．`DamasMilnerWLetStability`は，必要な変数分離条件を
満たす一つの後続W stepについてschemeを保存する補題を与える．これを実走査の全stepへ適用する不変条件は
まだ構成していない．
or-pattern，delegating matcher，let-polymorphic producerはpositive regressionとして維持されている．

### 5.4 terminal-fixed mutual erasure

`StateFactorization` は各局所出力から一つの root terminal substitution までの suffix を表す．全14
Origin family の相互 factorization と terminal audit を組み合わせ，expression，expression list，
checking，user／primitive／data pattern，pattern list，arm，clauseを同じ終端 cutへ固定した相互帰納で
消去する．各 child の局所 substitution を公開型へ残さず，終端 context，終端 type，終端 capability
だけから対応する `TypingInvariant`／pattern／arm／clause certificate を構成する．

特に variable／`let` は canonical scheme transport，matcher は terminal evidence，pattern constructor
は terminal compatibility を使う．matcher-to-slot alignment は終端 `CapabilityDemand`，slot-to-slot
alignment は終端型等式へ射影される．これにより closed-program wrapper について

```text
signature.SchemesClosed →
SourceTyping signature [] e τ → TypingInvariant signature [] e τ
```

が `SourceTyping.typingInvariant` として成立する．`TypingInvariant` の存在を demand-directed rule の premise に置く循環はなく，この定理は `SourceTyping` derivation
自身の solved-form preservation，Origin history，terminal audit から得られる．これはstate erasureの
正確な低レベルinterfaceであり，公開M4では`FrozenSigWF.schemesClosed`が先頭のpremiseを供給する．

## 6. dynamics と安全性

[`TypePM/Semantics.lean`](../TypePM/Semantics.lean) は type-erased evaluation と matching machine
を定義する．[`TypePM/Dynamic.lean`](../TypePM/Dynamic.lean) の `ValueTy` は literal，constructor，
tuple，closure，matcher literal，coerced matcher value を型付けする．closure body と matcher
literal は `TypingInvariant` proof を保持する．

[`TypePM/Preservation.lean`](../TypePM/Preservation.lean)，
[`TypePM/DynamicMetatheory.lean`](../TypePM/DynamicMetatheory.lean)，
[`TypePM/Safety.lean`](../TypePM/Safety.lean) は次を証明する．

- typed environment での expression evaluation は `TypingInvariant` を `ValueTy` へ保存する．
- typed matching state の全 successor は typed である．
- 非終端 typed state は局所 `StepReady` の下で一段進む．
- 一段保存を反復し，到達可能な全 matching state が typed である．
- 空 stack に到達した成功 branch の substitution は source pattern の binding context で型付く．

空 successor list は正当な match failure であり stuck ではない．primitive-pattern 内の value
pattern capture は depth-first・左から右の `PPatCoreOrder` から導出する．

さらに [`TypePM/Readiness.lean`](../TypePM/Readiness.lean) は `StepReady` を typing から構成する．
`StepReady`／`MAtomReady` は (a) 埋め込み式評価(value pattern の式・clause の body／next)の収束，
(b) `listOfV`／`decodeTuple` のデコード成功，(c) 成功する clause／arm への到達，の三種を束ねた
帰納述語だが，(b)(c) は typed 状態では仮定でなく定理である:

- 到達 (c) は coverage を使わず，`CatchAllLast`(最終 bare-hole catch-all は全 dispatchable
  pattern と shape 適合)と `ArmExhaustive`(`basicArmExhaustive` は irrefutable arm を要求)だけ
  から出る．coverage は引き続き preservation 側(継続 atom の型付け)の条件である．
- デコード成功 (b) は evaluation preservation と canonical form から出る．list 側は
  `FrozenSigWF.listCtorsExclusive`(`List` を結果に持てる data constructor は canonical な
  `nil`／`cons` のみ; `frozenSigWFCheck` の `listCtorCheck` 条項が table 全体を検査)が支える
  `listOfV_isSome`，tuple 側は `ValueTy.product_inversion` による `decodeTuple_isSome` を使う．

公開形は `MStateTy.progress_of_evals`: typed な非終端 top-level 状態は，埋め込み評価の収束
(`StateEvals`; 各評価は derivation-local な `EvalRuntimeSigAgrees` を伴う)だけから一歩進む．
すなわち局所progressの未放電の前提は「有限の評価導出が存在すること」だけに縮む．これは
収束しない場合を余帰納的な発散判断で分類する主張ではない．capture admissibility は
ordered route(`captureAdm_of_order_at`)と primitive route(`captureAdm_of_primitive_success`)の
二経路で放電し，`ppm_of_captureAdm` が typed・pristine な capture 環境ごと PPM を構成する．

式層では局所progressの収束前提を，fuel付き参照インタプリタの
no-stuck定理で大域的に扱う（**`typed_never_stuck_runtime`**）．
証明の構造:

- 各層に kernel 前提つきの standalone 定理を置く: `evalSafe`(式)・`matomSafe`(atom 一歩)・
  `stepSafe`／`searchSafe`(状態・探索)・`dispatchSafe`／`armsSafe`(clause／arm 歩行)・
  `ppmSafe`(`CaptureAdm` 駆動の header 照合)・`ppmSafe_primitive`(primForm の浅い直接解析)．
  kernel は常に「同じ fuel の真に下」(`∀ fuel' < fuel`)に束縛される．
- `NoStuckAt` が式・atom・状態・探索の 4 成分を束ね，`noStuck_master` が fuel 上の
  strong induction で全 fuel へ閉じる．clause dispatch だけ `DispatchKernelAt` 契約として
  分離し，`dispatchKernelAt_discharge` が matcher literal の inversion
  (pristine が cursor=start を強制・`matcherLiteral_inversion`・`matcher_inversion`・
  catch-all clause が shape-true witness)から放電する．
- 安全性の意味論的成分(結果値の `ValueTy`・`ValuePristine`)は機能的に再証明せず，
  adequacy(`evalFuel_ok`)＋`EvalRuntimeSigAgrees.of_global`＋既存の関係的 preservation で
  回収する．新規に必要なのは構文的スコープ層(`ScopedValue` 系)だけで，これは closure が
  存在量化された文脈を持つ `ValueTy` に触れずに変数 lookup の全域性を与える．
- 一般形は非空のruntime pattern-function表も扱う．前提は
  `∀ context, RuntimeSigAgrees signature context SF`（source定義との全contextでの整合）と
  `RuntimeSigScoped SF`（各runtime本体に自由な式変数がないこと）である．`stepSafe`は
  pattern-function applicationをMNodeへ展開し，embedded parameterをenclosing MNodeで
  実引数へ戻すため，これらを通常のatom reducerへ渡さない．
- 論文1断片では`signature.patternFuns = []`を明記し，`runtimeSigAgrees_nil`から
  `∀ context, RuntimeSigAgrees signature context []`を構成する
  `SourceTyping.never_stuck_paper1`を使う．空表の`RuntimeSigScoped`は自明である．
- `evalFuel_eventually_ok`は有限の関係的評価が十分大きいすべてのfuelで同じ値になることを
  証明する．`typed_all_timeout_iff_no_finite_eval`は`evalFuel_ok`とno-stuckも組み合わせ，
  全fuelでのtimeoutと有限の関係的評価が存在しないことの同値を明示する．別の余帰納的発散判断
  との同値は主張しない．一般のterminationは非目標で
  あり，幅優先探索（breadth-first search; BFS）の`matchAll`に対するmatching completenessは
  将来課題である．

global signature条件は `FrozenSigWF` だけである．これは従来のdynamic obligationsに加えて
`signature.SchemesClosed`と，デコード全域性を支える`listCtorsExclusive`(`List`を結果に
instantiate できる data constructor は canonical な`nil`／`cons`のみ)をfieldとして持つ．
`SignatureChecker`の`frozenSigWFCheck`は全tableのscheme closednessと`listCtorCheck`も直接検査する
有限checkerであり，`frozenSigWFCheck_sound`がその証拠を含む`FrozenSigWF`を構成する．
function-valuedな`armExhaustive`だけは，signature構築時に固定した
`armExhaustive = basicArmExhaustive`をsoundness theoremへ渡す．lookupで隠れる重複entryもtable全体の
検査対象である．

source-facingな公開安全性は次の形で機械化済みである．

```text
SourceTyping signature [] e τ
  + FrozenSigWF signature
      ├─ schemesClosed ─→ SourceTyping.typingInvariant
      └─────────────────→ core_safety
  → SourceTyping.SafeResult signature e τ SF
```

`SourceTyping.safe`は同じ公開型の内部`TypingInvariant`と，preservation／progress／到達可能性／
matching consistencyを含む`CoreSafety`を束ねる．`Inference.SafeResult`は推論成功から再構成した
source `SourceTyping`も保持し，`Inference.infer_closed_safe`はclosed inferenceをこのdemand-directed経路へ接続する．
低レベルstate erasureがclosednessを明示的に受けることと，公開callerが別premiseを渡さないことを
区別する．

## 7. Damas–Milner 断片

[`TypePM/DamasMilner.lean`](../TypePM/DamasMilner.lean) は pattern-free な一 sort system を
`DM.Typing`／`DM.Typings` として定義する．recursion は core と同じ direct-self singleton に
制限される．`DM.Typing.emb` は capability binder を使わず二 sort の `TypingInvariant` proof
へ埋め込み，`dm_coherent` は reconstruction certificate まで持ち上げる．
同moduleの`inFragmentExpr`はpattern-free syntaxを実行可能に判定し，`STy.ofTy?`は
capability-inertな一sort imageだけをdecodeする．`STy.emb`とdecoderの往復，imageの特徴付け，
埋込みの単射性，全`DM.Typing`がこのsyntax fragmentに入ることを証明済みである．

[`TypePM/DamasMilnerAcceptance.lean`](../TypePM/DamasMilnerAcceptance.lean)は，一sort substitutionの
chronological compositionと有限scope restriction，monotype／scheme／contextの一般性，canonical
scheme openingのprincipality，coreの`instantiateScheme`との一致を与える．これらは
全`DM.Typing`受理証明のvariable／let case用の基礎である．

[`TypePM/DamasMilnerAcceptanceMutual.lean`](../TypePM/DamasMilnerAcceptanceMutual.lean)は，DMの
式／式列typingを相互帰納し，fresh supply，paired residual，retired let cuts，provenance surfaceを
constructor間で輸送する．公開rootは内部certificateをcanonical initial stateで初期化し，

```text
DM.Typing.inferenceSucceeds :
  FrozenSigWF signature → DM.Typing context expression target →
  Inference.inferenceSucceeds signature context.emb expression = true
```

を与える．これはDM derivationが選ぶ`target`と`inferType`返値の構文的一致を主張しない．公開結論は
埋込みcontext上でのexecutable acceptanceに限られ，型の一般性比較はprincipality定理の役割である．

[`TypePM/DamasMilnerConservativity.lean`](../TypePM/DamasMilnerConservativity.lean)は，監査済み
source judgmentからDMへのclosed-program方向を証明する．`eraseTy`は関数・積を一sortへ
構造的に写し，dataをcomponentの積へ，基本型とskolemをDMの`Int`へ正規化し，
matcher／slot wrapperとcapabilityを忘れる．`SchemeErases`は
core schemeの全value-flow instanceをDM instanceに写し，`ContextErases`はlookupとfree-variable
listの一致をcontext全体に保持する．`SchemeErases.generalize`は
`FrozenSig.SchemesClosed.signatureTargets`でglobal target metavariableを排除し，`let`のcore
generalizationをDM generalizationへ写す．

`TypingInvariant.toDM`／`ExprsTy.toDM`は`InFragmentExpr`の証拠の下で内部導出を構造的に
消去する．classifierがconstructor，primitive，pattern，matcherを排除し，direct-self
`fix`だけを残す．coercion ruleが現れてもwrapperの消去で同じDM導出に戻る．公開定理

```text
DM.sourceTyping_to_dm :
  FrozenSigWF signature → InFragmentExpr expression →
  SourceTyping signature [] expression target →
  ∃ dmTarget, DM.Typing [] expression dmTarget
```

はwitnessとして`eraseTy target`を使う．この定理はcallerに`TypingInvariant`を要求せず，
`SourceTyping.typingInvariant signatureWF.schemesClosed`による監査済みclosed state erasureから
得た導出だけを消去する．入力contextが空でないconverseや，任意のsource targetと
DM principal targetの構文的一致は主張しない．後者の型比較はprincipalityと分離する．
D2のsource-to-DM射影とD1のDM-to-acceptanceを合成すれば，指定したclosed fragmentのsource typingから
公開推論器の成功まで到達するが，その合成にもtarget equalityは含まれない．

[`TypePM/DMTerminalAcceptance.lean`](../TypePM/DMTerminalAcceptance.lean) は terminal acceptance
の具体例を固定する．全 `DM.Typing` に対する一般定理は上記
`DM.Typing.inferenceSucceeds`である．

## 8. 回帰の読み方

回帰には二つの役割がある．第一は受理・拒否やメタ定理の設計境界を固定することである．第二は，
定理が対象とするcoreが意図したEgisonの機能をモデル化していることを，具体的な実行結果で確認する
ことである．後者のend-to-end回帰（入力から最終結果までを通す再実行可能なテスト）は，原則として

```text
infer success → SourceTyping → exact evalFuel result → Eval adequacy → all-fuel no-stuck
```

を同じfixtureについて検査する．安全性定理だけでは，matcherの分解結果が意図した集合であることや，
非線形patternの等値比較が正しい向きで働くことまでは決まらないためである．variable-onlyという
value-flow schemeのbinderをcapability変数にだけ写す規則が同一fixtureを拒否する場合は，型付き定義，
正確なruntime実行，公開推論の負例を分け，拒否が仕様どおりであることも固定する．

- `DemandTypingRegression`: raw demand-directed の旧freeze反例，局所Origin拒否，public freeze負回帰，state replay，supply boundedness．
- `AcceptanceGapRegression`: or-pattern 正例，nested matcher demand-directed 拒否，unresolved lambda domainの
  executable source-order正負とsource typability counterexample，constructor export freeze．
- `ApplicationCoercionRegression`: 関数引数の slot demand と matcher-expected 拒否．
- `CertifiedInferenceRegression`: terminal validator と成功時 reconstruction．
- `TerminalAuditCounterexample`: 整形式な閉じたdelegating matcherについて，raw Wと
  `DemandSynthRun`は成功するが，9検査のmatcher finalizationだけが失敗して公開推論が拒否することを
  固定する．raw resolved type，borrowed capabilityの終端像，空のprotected set，closureへの評価も検査し，
  `SourceTyping`相対の完全性とraw受理に対するaudit損失を区別する．
- `InferenceRegression`: 公開inference traversalと主要な成功／拒否境界．
- `SignatureChecker`: 全tableのscheme closedness，open pattern-function scheme，lookupで隠れる
  open schemeの拒否．
- `DemandTypingInferenceSoundnessRegression`: terminal `let` とrecursive matcherに対するpublic
  `infer_success_sourceTyping`．
- `DemandTypingInferenceCompletenessRegression`: list／multiset matcherと`matchAll`に対する
  premise-free `SourceTyping.infer_isSome`．
- `DemandTypingInferenceEquivalenceRegression`: 一般／closed受理同値の両方向，`inferType`返値の
  demand-directed soundness，source typabilityの`Decidable` API．
- `DemandTypingTargetUniquenessRegression`: open contextでsource metaを固定する一意性が偽である
  exact-MGU orientation境界．
- `TypeInstance`／`SourcePrincipality`／`RelativePrincipality`: 有限scope二sort instance preorder，
  `inferType`返値のtarget principality，terminal-normalized context／targetの同時相対principality．
- `DemandTypingSafetyRegression`: closed inferenceから`SourceTyping.safe`を通るevaluation safety．
- `ProducerStrengtheningRegression`: producer freeze の拒否／control 成功．
- `PatternCtorCapabilityRegression`: pattern-constructor capability projection．
- `PatternFunctionSafetyRegression`: pattern function とmatching safetyの接続，および非空runtime表を
  用いる閉programの`typed_never_stuck_runtime`具体化．nullary `unit`は公開推論，`SourceTyping`，
  exact evaluation，adequacy，全fuel no-stuckを接続する．parameter付き`pass`は，embedded parameterが
  実引数`$x`へ展開され，bindingがbodyへ戻って`[7]`を返すところまで正確に評価する．同programの
  公開推論拒否も固定する：共有capability binderのimageを，後続の`.something`に合わせて`Any`へ
  強めることはvariable-only規則が禁止する．
- `DynamicSafetyRegression`: end-to-end evaluation safety．
- `DynamicCaptureRegression`: value-pattern capture．
- `DynamicDispatchRegression`: matcher cursor と dispatch．
- `ReadinessRegression`: typed dispatch fixture 上で `MStateTy.progress_of_evals` を発火させる．
  `StepReady`・デコード成功・committed clause／arm は与えず，埋め込み評価の収束だけを供給する．
- `InterpreterRegression`: fixture を fuel 20 の kernel 簡約(`rfl`)で実行し，adequacy 経由で
  preservation へ接続する．`program_never_stuck` は公開 `typed_never_stuck` を fixture の
  typing と `freeVars = []`(`rfl`)だけで発火させる．
- `FeatureExecutionRegression`: Egison機能との対応を優先して検査するend-to-end回帰．
  `NonLinear`は`pair $x #x`の一致時に`[1]`，不一致時に`[]`を正確に返すことを固定する．
  `Multiset`はまず実際の`List`上のsingletonを`(1, [])`へ分解するruntime経路を検査する．さらに
  `Pair`を二要素collectionの有限carrierとして使い，同じ対象から`(1, 2)`と`(2, 1)`の両分解を
  この順で列挙する．非線形patternと二要素fixtureは公開推論，`SourceTyping`，kernel簡約による
  `evalFuel = ok`，`evalFuel_ok`による関係的評価，全fuel no-stuckまで接続する．二要素fixtureは
  multiset選択の有限具体例であり，任意長の再帰的multiset matcherや`join`の実行完全性は主張しない．
- `GeneralMultisetExecutionRegression`: 入力長に特化しない`fix` matcher関数と，それを
  `.something`に適用した主要programを公開推論，`SourceTyping`，正確な`evalFuel`結果，
  adequacy，全fuel no-stuckへ接続する．実行側は
  同じ再帰定義について，空・singleton・三要素・重複要素の`nil`／`cons`，入れ子`cons`，`join`を
  検査する．`submultisetSplits`は連続するprefix／suffixだけを返す`splits`とは異なり，各出現位置を
  左右へ割り振る全二分割を，左側の要素数と元の添字順で列挙する．同値な値を持つ異なる出現は別分岐
  として残る．入れ子`cons`は現在のdepth-first・左から右の探索順を固定する．
  matcher入力slotから借りたcapabilityを新たなfreeze対象から除く正例と，matcher-ownedの結果leafを
  引き続きfreezeする負境界も固定する．従って全入力listの機能的正当性，BFS completeness，標準multiset matcherの全interfaceは
  主張しない．
  さらに論文3節の特殊化された三節を同じ定義に追加する．`$ :: _`は対象全体を一度返す．
  `#$val :: $`はEgisonと同じ値先行の`member val tgt`／`deleteFirst val tgt`を
  `removeFirstChoice val tgt`へコンパイルし，最初の一致だけを除くか，不在なら正常な不一致を返す．
  `$ ++ $`は`submultisetSplits`で全二分割を列挙する．各節について公開推論から全fuel no-stuckまでを
  接続し，重複・不在・三要素の列挙順を正確な値で検査する．
- `CompositionFeatureRegression`: 一般multiset matcher，非線形pattern，pattern functionを同一の
  `matchAll`で合成するP2回帰．`join`で左右を分け，左右の`cons`で選んだ要素について，`$x`で整数を
  束縛し，`#x`で等値を検査し，各要素にnullary（引数を取らない）`unit()` pattern functionを適用する．
  重複する二つの`1`を異なる出現位置として選ぶ成功例は，同じ値を持つ2分岐を正確に返す．等しい整数を
  持たない例は正常なmatch failureとして`[]`を返す．両fixtureについて公開推論，`SourceTyping`，正確な
  `evalFuel`結果，adequacyによる関係的`Eval`，全fuel no-stuckまで接続する．
- `RecursiveExamples`: list／multiset matcher，direct-self recursion，coverage．
- `GeneralizationRegression`: binder 番号衝突下の instance と generalization．
- `ElaborationRegression`: canonical coercion plan と reconstruction factorization．
- `DMTerminalAcceptance`: concrete terminal acceptanceと，公開
  `DM.Typing.inferenceSucceeds`へ接続されるDM fragmentの受理境界．

正例と負例は設計境界を対で固定する．変更時は受理結果だけでなく，`SourceTyping` derivation，raw trace，
typing invariant，実行結果のどの層を検査する回帰かを確認する．

demand-directed関連moduleの役割は次のとおりである．

| module | 役割 |
|---|---|
| `DemandTyping` | raw demand-directed family，ledger-aware alignment，pure ledger transition |
| `DemandTypingOrigin` | 全raw derivationに対応するintrinsic Origin certificate |
| `DemandTypingLedgerMetatheory` | ledger extension，freeze，supply-scoped transition補題 |
| `DemandTypingOriginMetatheory` | 全Origin familyのledger evolution定理 |
| `DemandTypingIdempotence` | alignmentと全14 raw demand-directed familyのsolved-form保存 |
| `DemandTypingInferenceSoundness` | exact solver／alignment bridgeとexact-state runの基礎 |
| `DemandTypingInferenceSoundnessFixMatcher`／`Let`／`Patterns`／`Matcher` | constructor別の再構成slice |
| `DemandTypingInferenceSoundnessMutual` | 全10 traversal familyのraw exact-state相互再構成 |
| `DemandTypingInferenceSoundnessComplete`／`Certified`／`Public` | terminal-audited run，validator bridge，公開 `infer_success_sourceTyping` |
| `DemandTypingInferenceCompletenessStateMutual`／`ContextBisimulation`／`Traversal` | demand-directed／実行stateの相互factorization，context正規化，成功run package |
| `DemandTypingInferenceCompletenessPatternMain`／`MatcherMain`／`Main` | 全構文familyのfuel budget，raw traversal package，constructor別再構成 |
| `DemandTypingInferenceCompletenessPatternCtorCapComplete`／`PatternCertified` | pattern-constructor capability推論の完全性，user-pattern相互再帰とpaired validation package |
| `DemandTypingInferenceCompletenessPairedChecking`／`MatcherClauseCertified` | expression checking，matcher arm／clause listのpaired certified traversal |
| `DemandTypingInferenceCompletenessMatcherFinalizationCertified`／`MatcherGlobal` | matcher finalizationのbisimulation輸送とmatcher literal全体のpaired reconstruction |
| `DemandTypingInferenceCompletenessGlobalCertified`／`GlobalRecursion` | constructor dispatcherとfuelに対するclosed strong recursion |
| `DemandTypingInferenceCompletenessValidatorCoverage`／`CertifiedRun`／`PairedValidatorRun` | compositional event coverage，成功run，demand-directed／実行operandを結ぶpaired chronology |
| `DemandTypingInferenceCompletenessValidatorBisimulation`／`Acceptance`／`PairedRoot` | terminal auditの実行stateへの輸送，paired rootから有限validatorへの直接射影 |
| `DemandTypingInferenceCompletenessRootBuilder`／`GlobalRoot`／`Public`／`Regression` | canonical initial cutへの特殊化，公開 `SourceTyping.infer_isSome`，premise-free recursive matcher回帰 |
| `DemandTypingInferenceEquivalence`／`DemandTypingInferenceEquivalenceRegression` | 一般contextの受理同値，closed annotation-freeness，`inferType`返値soundness，条件付きdecidabilityと公開回帰 |
| `InferenceGeneralizationNaturality` | 二sort substitutionとscheme close／generalizationの可換性，binder列が保存される一つのexact solver stepに対するlet一般化保存 |
| `InferenceGeneralizationAudit` | 実際のlet eventの局所忠実性，append-only履歴での合成，局所忠実性と別途与えた終端安定性からのgeneralization check成功 |
| `DemandTypingInferenceRawOrdinaryValidator` | terminal-sensitiveでない6検査の集約，局所state操作・alignment・primitive patternに対する検査履歴の保存補題．raw traversal全体の定理はまだ含まない |
| `TerminalAuditCounterexample` | 整形式な閉じたprogramについてraw成功とmatcher-finalizationだけの公開拒否を固定し，raw成功等式から`DemandSynthRun`を得る一般接続とclosure評価を与える回帰 |
| `DemandTypingTargetUniqueness`／`DemandTypingTargetUniquenessRegression` | 全residual二sortmetaの局所renamingを法とする一般context `SourceTyping` target一意性，入力meta固定版の反例 |
| `TypeInstance`／`SourcePrincipality`／`RelativePrincipality` | 有限scope二sort instance preorder，一般／closed target principality，同一postによるopen context／target相対principality |
| `DamasMilnerAcceptanceTheorem`／`DamasMilnerAcceptanceMutual` | Algorithm Wのretired-state／normalized witnessと，全DM typingから公開inference acceptanceへの相互帰納 |
| `DemandTypingErasure` | state-erasure開発全体のpublic facade |
| `DemandTypingErasureCore` | scoped residual post，factorization core，初期typing-invariant projection |
| `DemandTypingErasureFactorization` | 全14 Origin familyのpremise-free state factorization |
| `DemandTypingErasureTransport` | canonical scheme openingの終端transport |
| `DemandTypingTerminalAudit`／`DemandTypingTerminalAuditTree` | `let`／matcher／pattern constructorの三種の終端事実，再帰audit，public `SourceTyping` wrapper |
| `DemandTypingTerminalAuditBuilder` | raw derivation，Origin certificate，終端 substitution からの terminal audit 構築 tactic |
| `DemandTypingTerminalAuditErasure`／`DemandTypingTerminalErasure` | terminal-fixedな`TypingInvariant`への相互射影とmatcher終端再構成 |
| `DemandTypingRegression`／`DemandTypingTerminalAuditErasureRegression` | raw境界，Origin-aware局所solve，terminal audit，公開state-erasure定理の回帰 |
| `Soundness` | `SourceTyping.safe`，`Inference.infer_closed_safe`，source typingからconcrete safetyへの公開facade |
| `Readiness`／`ReadinessRegression` | typing＋埋め込み評価収束からの`StepReady`構成，公開`MStateTy.progress_of_evals`，その実行回帰 |
| `Interpreter`／`InterpreterAdequacy`／`InterpreterRegression` | fuel付き参照インタプリタ（`ok`／`timeout`／`stuck`で発散と詰まりを分離），adequacy（`ok`⇒関係的導出），fixtureの実行回帰と`program_never_stuck` |
| `FeatureExecutionRegression` | 非線形patternの一致／不一致，実際の`List` singletonの分解，二要素multisetの複数分解を検査し，主要fixtureを公開推論，`SourceTyping`，正確な`evalFuel`結果，adequacy，全fuel no-stuckへ接続する機能対応回帰 |
| `GeneralMultisetExecutionRegression` | 入力長に特化しない再帰multiset matcherの型付き定義と，空・一要素・三要素・重複・入れ子`cons`・全`join`分割の正確な実行，depth-first結果順，主要適用の公開推論から全fuel no-stuckまでを固定する機能対応回帰 |
| `CompositionFeatureRegression` | 一般multisetの`join`／`cons`，`$x`／`#x`による非線形照合，nullary `unit()` pattern functionを同一`matchAll`で合成し，成功時の2分岐と不一致時の`[]`を公開推論から全fuel no-stuckまで固定するP2機能対応回帰 |
| `TermFreeVars`／`InterpreterScoping`／`InterpreterSafetyDefs` | 構文的自由変数層（`Expr.freeVars`・`Pattern.scopeVars`・`Pattern.exprVarsUnder`・`Env.names`），値／環境／状態のスコープ述語（`ScopedValue`など；closureの存在文脈をfv包含で回避），`Safe`契約・`AtomsScoped`・`stackBinders` |
| `InterpreterMatomSafe`／`InterpreterStepSafe`／`InterpreterEvalSafe` | 層別no-stuck定理（kernel前提つき）：atom一歩（`matomSafe`），pattern-function application・MNode内部step・embedded parameter展開を含む状態一歩と探索（`stepSafe`・`searchSafe`／`searchListSafe`），式層（`evalSafe`／`evalListSafe`／`evalSubstsSafe`；中間値の型付け・pristine性はadequacy＋関係的preservationで回収） |
| `InterpreterPpmSafe`／`InterpreterPpmPrimitive`／`InterpreterDispatchSafe` | clause header照合の安全性（`CaptureAdm`駆動の`ppmSafe`／`ppmListSafe`と，primForm patternの浅い直接解析`ppmSafe_primitive`），clause／arm歩行の安全性（`dispatchSafe`／`armsSafe`・`DispatchBranchProps`；`pdMatch_scoped`等の補題込み） |
| `InterpreterNoStuck`／`InterpreterDispatchBridge` | fuel上のstrong induction（束`NoStuckAt`＋`noStuck_master`；dispatch契約は`DispatchKernelAt`として分離），matcher literalのinversionからdispatch契約を放電する`dispatchKernelAt_discharge`，非空runtime表を扱う**公開headline `typed_never_stuck_runtime`**，空表特殊化`typed_never_stuck`，論文1のsource-facing特殊化`SourceTyping.never_stuck_paper1` |
| `DemandTypingSafetyRegression` | closed inferenceを公開`SourceTyping` safety packageへ接続するend-to-end回帰 |

## 9. 検証条件

全 module は [`TypePM.lean`](../TypePM.lean) から import される．変更後はリポジトリ直下で
`lake build` を実行する．形式仕様は `tex/` で `make` を実行し，`type-pm-mech.pdf` を生成する．
`sorry`，`admit`，project-defined `axiom`，typing derivation を premise に持つ oracle で証明を
埋めない．

公理監査：`AxiomAudit` は，`PublicTheorems` の見出し定理と README の定理表が指す公開定数
（計27個）の公理閉包を `#audit_standard_axioms` で計算し，`propext`・`Classical.choice`・
`Quot.sound` 以外の公理（`native_decide` が導入する補助公理，`sorryAx`，project-defined
`axiom`）が現れた時点で elaboration を失敗させる．検査は許容集合方式なので，公理の生成名の
変化に依存しない．監査対象は double-backquote 名前リテラルで解決するため，公開定理の改名は
監査リストの更新をビルドエラーとして強制する．`TypePM.lean` から import されるので，
`lake build`（および CI）は常にこの監査を含む．`native_decide` は executable regression
（具体プログラムの受理・拒否・実行結果の検査）に限定し，メタ理論の証明鎖では使わない．
