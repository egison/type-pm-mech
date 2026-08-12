# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．型には matcher を生成する
`Matcher κ τ` と，matcher を必要とする消費位置を表す `MatcherSlot κ τ` がある．

source program の型付け可能性を定義する judgment は `DDTyping` だけである．実行時安全性の
証明では，推論中の supply や substitution を消去した内部 certificate `RuntimeTyping` を使う．
両者の役割は次の一方向に整理する．

```text
DDTyping + FrozenSigWF.schemesClosed
              │ state erasure
              ▼
         RuntimeTyping ──────────────┐
                                    ├─→ DDTyping.SafeResult ──→ runtime safetyの各性質
FrozenSigWF ── core_safety ─→ CoreSafety
```

`RuntimeTyping` は source acceptance を定義する第二の型システムではない．逆に
`RuntimeTyping e τ` から `DDTyping e τ` や推論成功を導くことも意図しない．

## DDTyping

[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean) は，全 source form と pattern／arm／
clause 層について demand-directed な型付けを定義する．式層の中心は synthesis と checking
の二判断である．

```text
q; S; Ω; Γ ⊢ e ⇒ τraw      ⊣ q'; S'; Ω'    synthesis
q; S; Ω; Γ ⊢ e ⇐ τexpected ⊣ q'; S'; Ω'    checking
```

`q = (qκ, qτ)` は capability metavariable と target metavariable の次の番号を持つ fresh
supply，`S` はその cut までに得た paired substitution，`Ω` は capability variable の生成由来を
記録する origin ledger である．各規則は子を左から右へ調べ，出力 `q'; S'; Ω'` を次の子へ
渡す．公開 wrapper は canonical initial supply，恒等置換，空 ledger から始め，最後に
`S' τraw` を公開する．Leanでは rawな synthesis derivation，それに構造を一致させた intrinsic
Origin certificate，公開される終端 substitution での audit certificateを分けて
表現する．これらを合わせた判断が公開 source typingである．

`Ω(χ)` は次の三値を取る．未登録の変数は `rigid` として扱う．

- `rigid`: signatureや入力contextに由来し，solveはその変数を固定する．
- `renameOnly`: 既に外へ流れたproducerであり，非structuralな変数へのrenameだけを許す．
- `structuralFlexible`: constructor内部やconsumer demandの局所変数であり，export前だけ構造化を許す．

expression schemeとpattern-function schemeのcapability binderはinstance生成時から
`renameOnly` である．constructor／primitive instanceと単発fresh consumerは
`structuralFlexible` として生成し，使用後にexported payloadへ残る像のleafだけを
`renameOnly` へfreezeする．matcher literalは，最終capabilityに現れる全DD-owned explicit ledger
keyのstructural leafだけをfreezeする．これにはmatcher開始前に生成された `fixMatcher`
placeholderのowned leafも含まれる．ordinary equalityとone-way matcher-to-slot solveはいずれも，
そのcutの `Ω` に対してadmissibleなdeltaでなければならない．

```text
DDTyping Σ Γ e τ  iff
  ∃ τraw q' S' Ω',
    initialSupply Σ Γ; id; ∅; Γ ⊢ e ⇒ τraw ⊣ q'; S'; Ω' ∧
    TerminalAudit S' ∧
    τ = S' τraw
```

この定義は `infer` の成功や `RuntimeTyping` certificate の存在を前提にしない．

## Synthesis，checking，coercion

`DDCheck` は式を一度 synthesize し，その直後の cut で expected type と一度だけ align する．
ここで「一度だけ」とは導出全体で一回ではなく，各 checking cut につき一回という意味である．

非恒等 coercion は，cut で解決した expected type の head が `MatcherSlot` の場合だけ起こる．

| resolved source | resolved expected | alignment |
|---|---|---|
| `Matcher κp τp` | `MatcherSlot κc τc` | matcher-to-slot |
| product of matchers | `MatcherSlot κc τc` | product lift，matcher-to-slot |
| product of slots | `MatcherSlot κc τc` | slot-tuple lift |
| `MatcherSlot κp τp` | `MatcherSlot κc τc` | slot-to-slot equality |
| その他 | その他 | ordinary equality |

expected type が未解決変数なら ordinary equality だけを行う．coercion のために変数を slot
へ推測せず，ordinary equality の失敗後に別 branch を試す rollback も行わない．各 solve は
exact MGU または exact one-way solutionであり，constraint外のmetavariableを構造化しない．
さらにdeltaはcutの `Ω` に適合するため，`renameOnly` producerを `Any` やconstructor capabilityへ
後から強化するsolveは公開判断に入らない．

coercion の場所は `matchAll` や matcher literal に固定されない．たとえば
`use : MatcherSlot κ τ → ρ` へ `m : Matcher κ τ` を渡す場合，関数適用が domain を決め，
引数の checking cut で matcher producer と slot demand が対応付けられる．`matchAll` の
matcher 引数と matcher clause の next-matcher も同じ `DDCheck` を使う．

## RuntimeTyping と安全性

[`TypePM/Source.lean`](TypePM/Source.lean) の `RuntimeTyping` は，fresh supply，solver の実行順，
origin ledger を持たない state-free certificate である．closure と matcher value はこの
certificate を保持し，preservation はそれを `ValueTy` へ移す．
matcher-to-slot coercion も実行器の matching／MGU 成功証拠を保持せず，終端 capability 間の
`CapabilityDemand` だけを保持する．slot-to-slot solve は終端型の等しさへ消去される．実行用の
raw solver certificate は reconstruction がこの意味的証拠へ射影するまでの境界にだけ残る．

実行可能推論については次の経路が機械化済みである．

```text
infer Σ Γ e = some r
  → Reconstruction.ExprDeriv Σ (ResolvedContext r.state.prevailing Γ)
      e r.resolvedTarget
  → RuntimeTyping Σ (ResolvedContext r.state.prevailing Γ)
      e r.resolvedTarget
```

中心となる定理は `infer_success_reconstruct` と `infer_success_runtimeTyping` である．公開
`infer` は停止する `inferRaw` と有限の fail-closed terminal validator の合成であり，caller
が bridge certificate や `InferenceInputWF` を渡す必要はない．

`FrozenSigWF` の下では，`RuntimeTyping` を持つ式の評価，matching state の一段保存，局所
progress，到達可能 state の保存，成功 branch の substitution typing を証明済みである．
`FrozenSigWF` はこれらの動的整合性に加えて，signature中の全schemeがbinder外の
metavariableを持たない `SchemesClosed` を含む．実行可能checker `frozenSigWFCheck` の成功から
`frozenSigWFCheck_sound` が，signature構築時に固定する
`armExhaustive = basicArmExhaustive` と合わせてこの単一のglobal条件を構成する．一般の program
termination は主張しない．

## 接続の現在地

`DDTyping → RuntimeTyping` の state erasure は完成している．public `DDTyping` は
canonical initial supply，恒等置換，空 ledger から始まる raw derivation，構造が対応する
Origin certificate，終端 substitution での audit certificateを保持する．全 raw DD
family で出力 substitution の idempotence を保存することと，各子の出力から根の終端までの
chronological factorization を使い，全14 family の相互 erasure から closed-program の
`RuntimeTyping` を得る．`RuntimeTyping` 自体の存在を `DDTyping` の premise に置く循環はない．

`infer → DDTyping` の executable soundness は完成している．公開定理
`Inference.infer_success_ddTyping` は，成功した fuelled traversal を同じ cut 列を持つ raw DD
derivationへ相互再構成し，validator が与える一つの終端 certificate から terminal audit を構成して，
報告された `resolvedTarget` の `DDTyping` を返す．caller が `WBridgeWF` や history を渡す必要はない．

`DDTyping` からの公開動的安全性も完成している．低レベルの `DDTyping.runtimeTyping` は
signature closednessを明示的に受け取るが，公開定理 `DDTyping.safe` は
`FrozenSigWF.schemesClosed`からその証拠を内部で供給する．したがってclosed programについて

```text
DDTyping signature [] e τ →
FrozenSigWF signature →
DDTyping.SafeResult signature e τ SF
```

が成立する．`DDTyping.SafeResult` は同じ公開型の `RuntimeTyping` と，preservation／progress／
matching safetyを束ねた `CoreSafety` を保持する．`Inference.infer_closed_safe` はclosedな推論成功を
`infer → DDTyping → safety` の公開経路へ接続する．

`DDTyping → infer` の受理完全性も完成している．DD derivation と terminal audit を同時に再帰し，
exact solve，fresh allocation，context normalization，producer protectionを同じ executable traversalへ
再現する．各局所runが蓄積するvalidator event coverageをrootでterminal auditと合成し，有限の
`wBridgeCheck`を通す．公開定理はM4と同じglobal signature条件だけを受け取る．

```text
DDTyping.infer_isSome :
  DDTyping signature context e τ →
  FrozenSigWF signature →
  (infer signature context e).isSome = true
```

`RawSourceVisible`，`FreezeCompatible`，solver success，validator bridgeなどの実装向け条件は
caller premiseに残らない．`FrozenSigWF`はterminal factsを実行側の終端stateへ輸送する際の
scheme closednessとcanonical arm checkerを含み，M4とM5で共有する公開signature境界である．

`nestedCapProgram` と swapped 版は DD で型付かず，推論器も拒否する意図された負例である．
一方，or-pattern，delegating matcher，let-polymorphic な matcher producer は維持すべき正例で
あり，public Origin certificate を伴う回帰で固定済みである．

## Roadmap

roadmap は次の依存関係に従う．`RuntimeTyping` を source typing に戻したり，その derivation の
存在を `DDTyping` の premise に加えたりせず，DD derivation 自身が安全性と実行可能推論への
接続に必要な情報を持つ形を完成させる．

```text
[x] 1. freeze provenance と public 回帰
        │
        ▼
[x] 2. DD state erasure ─────────→ [x] 4. DD の公開安全性

[x] 3. infer success → DDTyping ─┐
                                 ├→ [ ] 6. 受理同値と注釈不要性
[x] 5. DDTyping → infer success ─┘
```

記号は `[x]` が完了，`[~]` が一部完了，`[ ]` が未完了を表す．

### 進捗サマリ

全7 milestoneのうち，完了6，未着手1である．

| milestone | 状態 | 完了した中心部分 | 残る中心部分 |
|---|---|---|---|
| 0. 基盤 | 完了 | DD判断，exact solve，runtime certificate，既存動的安全性 | なし |
| 1. freeze provenance | 完了 | Origin ledger，public正例／負例回帰 | なし |
| 2. DD state erasure | 完了 | canonical `Scheme`，全14 familyのfactorizationとidempotence，terminal audit，固定終端への相互erasure，closed-program公開定理 | なし |
| 3. infer success → DDTyping | 完了 | 全 traversal family の exact-state 相互再構成，terminal audit，public中心定理と回帰 | なし |
| 4. DDの公開安全性 | 完了 | `FrozenSigWF`へのclosedness統合，`DDTyping.safe`，closed inferenceからの公開安全性経路 | なし |
| 5. DDTyping → infer success | 完了 | 全構文familyのaudited traversal完全性，validator event coverage，public `DDTyping.infer_isSome` | なし |
| 6. 受理同値 | 未着手 | milestone 3と5の両方 | 受理同値と`inferType`の結果型との関係 |

現在の次段は milestone 6である．milestone 3の executable soundnessとmilestone 5の
acceptance completenessを合成し，`FrozenSigWF`の下でsource typabilityと公開推論器の
受理を同値として公開する．

`infer` 成功から `RuntimeTyping` を再構成する既存定理は，引き続き実行系の内部 certificate への
独立した経路である．新しい source-facing 経路はまず `DDTyping` を直接再構成する．一般 context
で両者を無条件に合成したとは主張せず，closed-program の `DDTyping → RuntimeTyping` は
milestone 2の定理を用いる．

### [x] 0. 現在の基盤

次は完成済みの出発点であり，後続 milestone で維持する不変量である．

- 全 expression／pattern／arm／clause form に `DDSynth`／`DDCheck` family がある．
- checking は synthesis 後の一 cut で一度だけ alignment を行う．
- 非恒等 coercion は slot-headed expected type に限られる．
- exact MGU，state replay，supply extension，boundedness が証明されている．
- `infer` の成功から reconstruction と `RuntimeTyping` を構成できる．
- `RuntimeTyping`，`ValueTy`，matching-state judgment 上の動的安全性が証明されている．

### [x] 1. Capability freeze provenance の public 回帰を完成する

core 実装は完了している．全 DD family の raw derivation に構造を一致させた intrinsic Origin
certificateがあり，`q; S; Ω` を状態として追跡する．scheme／dual instance は binder imageを
`renameOnly`，constructor instanceとfresh consumerは `structuralFlexible` とし，exportとmatcher
finalizationは外へ残るstructural leafだけを選択的にfreezeする．ordinary equalityとone-way solveは
cutのledgerに対してadmissibleなdeltaだけを受理する．`let` certificateは終端 substitution 後にも
同じgeneralization schemeが得られる安定性を要求する．public wrapperも空ledgerから始める．

originを追跡しない局所導出で現れた反例は，public `DDTyping` 全体の導出不能性まで閉じた
negative regressionとして固定されている．

完了条件：

- [x] ledger の extension，freeze，substitution replay に関する基本補題が全 DD family で成り立つ
  （基本的な supply-scoped ledger 補題と transition 補題は実装済み）．
- [x] `capFreezeProgram` と `letCapFreezeProgram` が public `DDTyping` では導出不能であることを証明する
  （問題となる局所導出，ledger-aware solveによる拒否，program全体のnegative regressionを実装済み）．
- [x] or-pattern，delegating matcher，let-polymorphic producer など既存の正例について public Origin
  certificate を構成する（実装済み）．
- [x] `nestedCapProgram`，matcher-expected product application など既存の負例は導出不能なままである．
- [x] public `DDTyping` は canonical initial ledger から開始し，外部の freeze premise を要求しない．

### [x] 2. DD state erasure を証明する

ledger-aware な DD derivation から supply，prevailing substitution，origin ledger を消去し，
`RuntimeTyping` certificate を構成する相互証明は完了している．expression だけでなく，
expression list，checking，user／primitive／data pattern，arm，clause を含む全 family を
同じ根の終端 substitution へ射影する．

完了した構成は次のとおりである．

- [x] 全14 DD familyの無前提 `StateFactorization` を構成する．
- [x] checking alignment全5分岐を終端 `RuntimeAlignment` へ射影する．
- [x] solver metavariableとscheme bound variableを別datatypeにしたcanonical `Scheme`へ移行し，
  binder名，mask，`NoCapture` 条件を source scheme から除去する．
- [x] finiteなbound indexのopening，fresh allocation，generalization，substitution合成，
  variable value-flow transportを構成する．
- [x] exact solveがidempotentな入力 substitutionからidempotentな出力を作ることを，
  alignment familyとraw DD全14 familyで証明する．
- [x] derivationと同じ形のterminal-audit treeを構成し，`let` generalization，
  matcher finalization，pattern-constructor compatibilityを根の終端 substitutionで固定する．
- [x] chronological factorizationとidempotenceを各子へ渡す固定終端の相互erasureを構成する．
- [x] closed signatureについて
  `DDTyping.runtimeTyping`，すなわち
  `DDTyping signature [] e τ → RuntimeTyping signature [] e τ` を公開定理として閉じる．

<details>
<summary>state erasureの設計</summary>

schemeのbound variableは有限なbound index，推論器のmetavariableは `CapVar`／`TyVar` であり，
構文レベルで異なる．ambient substitutionはbound occurrenceを生成できないため，旧来の
binder-name衝突，mask，`NoCapture` 保存条件は不要になった．generalizationは選んだmetavariableを
直ちにcanonical schemeへcloseし，instance生成はcaller-suppliedなfinite openingで行う．

消去証明は「任意の将来 suffix に対して各nodeが安定する」とは仮定しない．その主張は
`let` のgeneralized setが後続solveで変わり得るため強すぎる．代わりに公開 `DDTyping` は，
raw derivationとOrigin certificateに加え，同じ木構造を持つterminal auditを公開終端
substitutionに対して保持する．auditは局所suffixで一般には保存されない三種類の事実を記録する：

- `let` が終端contextと終端value typeから同じschemeをgeneralizeすること．
- matcherの終端capabilityに対してshape，clause capability，exhaustiveness，coverageが成立すること．
- pattern constructorの引数capabilityと結果capabilityが終端でcompatibleであること．

各raw DD familyはexact solveのidempotenceを保存する．また，各子の出力状態から根の終端状態への
`StateFactorization` がchronological substitutionを与える．相互erasureはこのfactorizationと
idempotenceを再帰的に渡し，variable opening，checking alignment，`let`，matcher／clause，
pattern constructorを含む各constructorを終端の `RuntimeTyping` familyへ射影する．terminal
auditは `RuntimeTyping` の存在を保持するoracleではなく，solverを含まない有限な代数的・
検査可能事実だけを保持する．

</details>

一般の内部定理は入力contextへ根の終端 substitutionを適用した `RuntimeTyping` を構成する．
canonical initial stateと空contextに特殊化すると，公開した型をそのまま持つclosed-program
corollaryが得られる．これによりMilestone 2は，型付けderivationをpremiseに持つoracleや
blanketなcapability transportを追加せず完了した．

### [x] 3. 実行可能推論の DD soundness を証明する

public `infer` の成功を唯一の前提として，報告された型の `DDTyping` を再構成する定理は完成している．

```text
infer Σ Γ e = some r
  → exact-state mutual DD reconstruction
  → terminal-audited certified run
  → DDTyping Σ Γ e r.resolvedTarget
```

証明は三層に分けている．まず solver と checking alignment の成功を exact DD transitionへ写し，
expression，pattern，arm，clauseを含む traversal 10 familyを fuel に関して相互再構成する．次に
append-only historyにより全 recursive callを同じroot終端へ接続し，validatorの `WBridgeWF` から
局所suffixでは保存されない `let`，matcher，pattern constructorの三事実だけをterminal auditへ
載せる．最後にcanonical initial stateのcertified runをpublic `DDTyping`へ射影する．

中心定理は次である．

```text
Inference.infer_success_ddTyping :
  infer signature context expression = some result →
  DDTyping signature context expression result.resolvedTarget
```

`WBridgeWF` と `HistoryPrefix` は証明内部でのみ用いる．callerに追加のwell-formedness premiseや
typing certificateを要求しない．`fixMatcher`のsupply-indexed skeleton，`letE`の終端
generalization，matcher finalization，pattern constructor，`matchAll`を含む全分岐を同じ相互定理で
閉じ，terminal `let` とrecursive matcherをpublic APIの回帰で固定している．

#### 完了条件

中心定理：

```text
infer signature context e = some result →
  DDTyping signature context e result.resolvedTarget
```

これにより，公開推論器の成功は唯一の source typing に対して sound である，という通常の API を
得る．空contextへ特殊化した場合は，`FrozenSigWF`が供給するclosednessの下でこの定理と
milestone 2を`Inference.infer_closed_safe`として合成できる．一般contextの
`infer_success_runtimeTyping` は既存の独立したreconstruction経路を使う．

### [x] 4. DDTyping から公開動的安全性を導く

`FrozenSigWF` に `SchemesClosed` を統合し，milestone 2のstate erasureが必要とするclosednessを
単一のglobal signature条件から取得する．実行可能checker `frozenSigWFCheck` は全signature
schemeのclosednessも有限に検査し，成功時に完全な `FrozenSigWF` を構成する．
function-valuedな`armExhaustive` fieldだけは，signature構築時の定義的等式をchecker soundnessへ渡す．

公開定理は次の形で完成している．

```text
DDTyping signature [] e τ →
FrozenSigWF signature →
DDTyping.SafeResult signature e τ SF
```

`DDTyping.safe` は同じ型の内部 `RuntimeTyping` と `CoreSafety` を返すため，expression evaluationと
matching machineの既存定理をこの入口から利用できる．`Inference.SafeResult` は推論成功から得た
source `DDTyping` も保持し，`Inference.infer_closed_safe` はclosed inferenceを同じDD入口へ通す．

### [x] 5. DDTyping に対する推論器の受理完全性を証明する

DD derivationのOrigin treeとterminal auditを同時に左から右へ読み，対応する
fuelled traversalの成功を全expression，checking，pattern，arm，clause familyに対して再構成する．
DDのexact solve witnessとexecutable solver resultはmutual factorizationで対応させ，
`StateBisimulation`，context normalization，supply boundednessをrecursive callの間で保存する．

各constructorは成功runに加えてordinary validator eventと三種のterminal-sensitive eventの
coverage extensionを返す．pattern constructorではDD導出が記録するdual／capabilityと実行trace中の
operandsを同一視せず，その間のbisimulationをpaired witnessとして保持する．rootでそれらを
`PairedRootCertifiedSynthesis`に束ね，pattern-constructor compatibilityはpaired witnessから直接，
`let` generalizationとmatcher finalizationはexact branchから，producer protection，type／dual
alignmentと合わせて`wBridgeCheck`の全条件へ射影する．
Originとauditは`Prop`，concrete runは`Type`に属するため，main recursionは
`Nonempty PairedRootCertifiedSynthesis`を返し，公開facadeが受理命題の内部でだけその証明消去境界を
開く．

中心定理：

```text
DDTyping.infer_isSome :
  DDTyping signature context e τ →
  FrozenSigWF signature →
  (infer signature context e).isSome = true
```

公開premiseはsource derivationとM4でも使う`FrozenSigWF`だけである．
`RawSourceVisible`，`FreezeCompatible`，solver success，caller-supplied bridge，既知のinference
successは残さない．これはvalidator単体が任意のraw runを受理するという無条件完全性ではなく，
terminal-audited `DDTyping` fragmentから生成したtraceに対する相対的な完全性である．

### [ ] 6. 受理同値と注釈不要性を公開する

milestone 3 と 5 を合成し，closed program について source typability と公開推論器の成功を
対応付ける．

```text
FrozenSigWF signature →
  ((∃ τ, DDTyping signature [] e τ) ↔
    (infer signature [] e).isSome)
```

この同値を本 mechanization の annotation-freeness 定理とする．あわせて，`inferType` が返す型と
DD derivation の型の関係を定式化し，DD fragment に対する decidability と，必要なら条件付き
principality を独立に議論する．`RuntimeTyping` 全体の principality 反例を DDTyping の結果として
流用しない．

## 機械化済みの主な性質

- `DDCheck` の非恒等 branch は slot-headed expected type に限られる．
- matcher-headed expected type では ordinary equality しか起こらない．
- DD family の supply は単調に進み，substitution は chronological delta replay に分解できる．
- exact solveと全14 raw DD familyは substitution のidempotenceを保存する．
- DD が公開する型，pattern dual，bindings，hole ledger は終端 supply で有界である．
- exact MGU は constraint 外の metavariable を推測しない．
- matcher literal は shape，catch-all order，data-arm exhaustiveness，binder 線形性，coverage
  evidence をすべて要求する．
- `infer signature context expression = some result` から
  `DDTyping signature context expression result.resolvedTarget` を導く．
- closed signature上で `DDTyping signature [] e τ` から `RuntimeTyping signature [] e τ` を導く．
- `FrozenSigWF` は全signature schemeのclosednessを含み，実行可能checkerがこの条件も検査する．
- `DDTyping signature [] e τ` と `FrozenSigWF signature` から，同じ型の内部certificateと
  concrete safetyを束ねた `DDTyping.SafeResult` を導く．
- `infer` の成功から reconstruction certificate と `RuntimeTyping` を再構成できる．
- `FrozenSigWF` の下で concrete evaluation と matching machine の安全性が成り立つ．
- `sorry`，`admit`，project-defined `axiom` はない．

## モジュール案内

| 層 | 主な module | 役割 |
|---|---|---|
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| DD typing | `DemandTyping`, `DemandTypingOrigin`, `DemandTypingInferenceSoundness*`, `DemandTypingErasure`, `DemandTypingRegression*` | raw規則，intrinsic Origin certificate，推論成功からpublic DD typingへの再構成，state erasureと回帰 |
| runtime certificate | `Source`, `Reconstruction`, `CoherentSurface`, `CoherentTyping` | state-free certificate と再構成 |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，origin ledger，validator，成功時の再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety`, `Soundness` | evaluation，matching machine，`DDTyping.safe`による公開安全性入口 |
| fragments | `DamasMilner`, `DMTerminalAcceptance` | pattern-free DM 断片 |

詳細な定義・定理・回帰の対応は [`docs/details.md`](docs/details.md)，論文形式の規則は
[`tex/main.tex`](tex/main.tex) にある．Lean の public import surface は
[`TypePM.lean`](TypePM.lean) である．

## 検証

```sh
lake build
cd tex
make
```

TeX の出力は `tex/type-pm-mech.pdf` である．
