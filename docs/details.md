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

[`TypePM/DemandTyping.lean`](../TypePM/DemandTyping.lean) が source typing を定義する．式層は
次の三 family からなる．

```text
DDSynth Σ q S Γ e τraw q' S'
DDCheck Σ q S Γ e τexpected q' S'
DDAlign q S τraw τexpected q' S'
```

`DDTyping Σ Γ e τ` は `initialSupply Σ Γ` と `Subst.id` から `DDSynth` を開始し，終端
substitution を raw result に適用した型だけを公開する closed wrapper である．

### 2.1 fresh supply と prevailing substitution

`q = (nextCap, nextTy)` は二 sort の fresh counter である．capability metavariable を一つ
生成すれば `nextCap` だけ，target metavariableを一つ生成すれば `nextTy` だけ進む．`S` は
その構文位置までに確定した paired substitution である．子 judgment の出力 `q'; S'` は
左から右に次の子へ渡される．

lambda は fresh domain と codomain を生成する．application は function synthesis，function
type との ordinary alignment，argument checking の順で state を渡す．`let` は value の
終端型を prevailing context に対して一般化し，body lookup ごとに fresh instance を作る．

### 2.2 synthesis-first checking

`DDCheck` の規則は一つだけである．

1. expected type を使わず `DDSynth` する．
2. synthesis の出力 cut で `DDAlign` を一回行う．

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
exact solution である．

### 2.4 pattern，arm，clause

式以外の DD family は executable traversal と同じ割当順を関係として記述する．主な family は
`DDPattern`／`DDPatterns`，`DDPPat`／`DDPPats`，`DDDPat`／`DDDPatList`，`DDArm`／
`DDArms`，`DDClause`／`DDClauses` である．

pattern constructor は target instance と capability projection を同じ signature entry から
得る．or-pattern は両 alternative の binder 名を位置対応させ，型を align する．matcher
literal は全 clause の共有 target を生成し，shape，catch-all order，data-arm exhaustiveness，
primitive-pattern binder 線形性，arm binder 線形性，`CoverageOK` を finalization で要求する．

### 2.5 DDTyping の証明済み性質

- `DDAlign` の非 ordinary branch なら expected type は slot-headed である．
- matcher-headed expected type の derivation は ordinary equality に限られる．
- 各 family の出力 supply は入力 supply を拡張する．
- 出力 substitution は入力 substitution と solve delta の chronological replay に分解できる．
- 公開型，dual，bindings，hole ledger の flexible variable は終端 supply で有界である．
- exact MGU は constraint 外の fresh variable を slot や matcher に構造化しない．

## 3. executable inference

[`TypePM/Inference.lean`](../TypePM/Inference.lean) の `inferRaw` は停止する W-style traversal で
ある．`InferState` は supply，prevailing substitution，constraint trace，source trace，
capability-origin ledger を持つ．`infer` は `inferRaw` の結果を有限の `wBridgeCheck` で検査し，
失敗時は `none` を返す．

origin ledger の各 capability variable は `rigid`，`renameOnly`，`structuralFlexible` のいずれか
である．consumer demand のために生成した variable は structural solve を許せるが，value-flow
instance や export 後の producer image は variable-only に freeze される．

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

## 4. RuntimeTyping は内部 certificate である

[`TypePM/Source.lean`](../TypePM/Source.lean) の `RuntimeTyping` は fresh supply，prevailing solver
state，origin ledger を消去した expression certificate である．`ExprsTy`，pattern resolution，
arm／clause certificate と相互に構成される．source acceptance は定義しない．

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

## 5. capability freeze と未完成の state erasure

現行 DD family は supply と substitution を持つが origin ledger を持たない．そのため，通常
equality solve が value-flow producer 由来の fresh capability を構造化する derivation を DD 側
だけでは排除できない．

`DemandTypingRegression` の二例がこの不足を固定する．

- `capFreezeProgram`: context の量化 matcher scheme の fresh capability instance が後続 solve
  で `Any` に構造化される．
- `letCapFreezeProgram`: lambda domain の capability meta が `let` generalization で束縛され，
  body の二つの lookup が別々の構造へ instance 化される．

どちらも現在の raw DD rules では閉じるが，value-flow variable-only 条件を満たす
`RuntimeTyping` certificate は作れない．従って無条件の `DDTyping → RuntimeTyping` は現定義の
ままでは偽である．

解決には，producer capability の生成，scheme instance，`let` generalization，export freeze
を追跡する provenance を DD family 自体へ統合する必要がある．その後，この provenance を
帰納的に消去して `RuntimeTyping` を構成する．`RuntimeTyping` derivation の存在を DD の premise
にする定義は循環するため採らない．

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
  → RuntimeTyping          state erasure（未完成）
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

- `DemandTypingRegression`: DD の正負例，state replay，supply boundedness，freeze 境界．
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

## 9. 検証条件

全 module は [`TypePM.lean`](../TypePM.lean) から import される．変更後はリポジトリ直下で
`lake build` を実行する．形式仕様は `tex/` で `make` を実行し，`type-pm-mech.pdf` を生成する．
`sorry`，`admit`，project-defined `axiom`，typing derivation を premise に持つ oracle で証明を
埋めない．
