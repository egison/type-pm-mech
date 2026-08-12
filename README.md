# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．matcherを生成する型
`Matcher κ τ`と，matcherを必要とする消費位置の型`MatcherSlot κ τ`を分け，coercionを
消費側のdemandから決める．

source programの型付け可能性を定義するjudgmentは`SourceTyping`だけである．公開推論器`infer`は，
well-formedなsignatureの下で`SourceTyping`の存在を正確に判定する．closed programについては，
このsource typingから評価とmatching machineの安全性まで接続済みである．

## 現在の到達点

中心となる接続は次の四つである．

```text
infer Σ Γ e = some r
  ── soundness ──→ SourceTyping Σ Γ e r.resolvedTarget

SourceTyping Σ Γ e τ + FrozenSigWF Σ
  ── completeness ──→ (infer Σ Γ e).isSome = true

SourceTyping Σ [] e τ + FrozenSigWF Σ
  ── state erasure / safety ──→ TypingInvariant Σ [] e τ + CoreSafety

DM.Typing Γ e τ + FrozenSigWF Σ
  ── normalized Algorithm W replay ──→ inferenceSucceeds Σ Γ.emb e = true
```

したがって一般contextについて，次の受理同値と決定可能性が得られている．

```text
FrozenSigWF Σ →
  ((∃ τ, SourceTyping Σ Γ e τ) ↔ (infer Σ Γ e).isSome = true)
```

主な公開定理は[`TypePM/PublicTheorems.lean`](TypePM/PublicTheorems.lean)から参照できる．

| 定理 | 主張 |
|---|---|
| `Inference.infer_success_sourceTyping` | `infer`が返した型には`SourceTyping` derivationがある |
| `SourceTyping.infer_isSome` | `FrozenSigWF`の下で`SourceTyping`を持つprogramを`infer`が受理する |
| `Inference.sourceTypable_iff_infer_isSome` | source typabilityと公開推論器の成功が同値である |
| `Inference.sourceTypableDecidable` | source typabilityを公開推論器で決定できる |
| `SourceTyping.target_unique_modulo_renaming` | 同じsourceのtargetはresidual二sortmetaのrenamingを法として一意である |
| `Inference.inferType_principal` | `inferType`の返値は有限scope二sortinstance preorder上でprincipalである |
| `Inference.infer_relative_principal` | open termのresolved contextとtargetを同じsubstitutionで相対比較できる |
| `SourceTyping.safe` | closed `SourceTyping`から同じ型の内部invariantと動的安全性を得る |
| `DM.sourceTyping_to_dm` | closed・pattern-freeの`SourceTyping`を型消去して`DM.Typing`を得る |
| `DM.Typing.inferenceSucceeds` | 任意の`DM.Typing` derivationを埋込みcontext上で公開推論器が受理する |

targetのrenaming一意性に加えて，target単体のinstance preorder上のprincipalityと，open contextで
context／targetを同時に比較する相対principalityまで証明済みである．一般のprogram terminationは
主張しない．Damas--Milner側の結果はexecutable acceptanceであり，DM derivationが選ぶtargetと
`inferType`返値の構文的一致は主張しない．

### 証明済みのメタ理論

| 領域 | 現在の到達点 |
|---|---|
| 基盤 | soundness，completeness，受理同値，決定可能性，安全性，target一意性を公開定理として接続済み |
| principality | 二sort instance preorder，closed target principality，open context／target相対principalityを証明済み |
| Damas--Milner | 任意の`DM.Typing`のexecutable acceptanceと，closed source fragmentからDMへの型消去を証明済み |
| source order | no-guessとchronological state threadingによる順序依存を意図された仕様として正負回帰で固定済み |

### Principality

`TypeInstance`はsource typeのfree capability／target metaだけを変更できる有限supportのpaired
substitutionでinstance関係を定める．`ScopedTypeInstance`は二つのscopeを明示する．restrictionが
型への作用を保つことと，chronological compositionを元scopeへ再restrictionすることにより，反射性と
推移性を証明済みである．局所二sort renamingは両方向の`TypeInstance`を与える．

`Inference.inferType_principal`は一般contextで次を与え，`inferType_closed_principal`が空contextへの
特殊化を公開する．

```text
FrozenSigWF Σ → inferType Σ [] e = some principal →
  SourceTyping Σ [] e principal ∧
  ∀ target, SourceTyping Σ [] e target → TypeInstance principal target
```

open contextではcontext由来のmetaをすべてrigidにした強い形を採らない．`ContextTargetInstance`は
normalized contextとtargetのfree metaの和を有限scopeとし，同じpaired substitutionを両方へ作用させる．
`SourceTyping.TerminalPair`は第二のsource judgmentではなく，既存のaudited derivationからその終端
substitutionで正規化したcontextと公開targetを取り出すviewである．`Inference.infer_relative_principal`は
成功runの`ResolvedContext`／`resolvedTarget`と，任意の`SourceTyping` derivationのterminal pairが
相互に`ContextTargetInstance`であることを証明する．closed specializationはcontext成分が空なので
`TypeInstance` principalityへ戻る．

### Damas--Milner acceptanceとconservativity

`DamasMilner`はpattern-free expression classifierとcapability-inert type decoderを持ち，埋込みの
像と単射性を証明する．`DamasMilnerAcceptance`は一sort substitutionの合成／restriction，monotype／
contextの一般性，canonical scheme openingのprincipalityとcore instantiationとの一致を証明する．
公開定理`DM.Typing.inferenceSucceeds`は次を与える．

```text
FrozenSigWF Σ → DM.Typing Γ e τ →
  Inference.inferenceSucceeds Σ Γ.emb e = true
```

証明はDM derivationをconstructorごとにAlgorithm Wの監査済みrunへ再生し，公開推論器のterminal
acceptanceへ接続する．結論はacceptanceだけである．DM derivationが選んだ`τ`は推論器のprincipal
targetの特殊化であり得るため，`inferType`の返値と`τ.emb`の構文的一致は主張しない．

逆方向の`DamasMilnerConservativity`では，`eraseTy`が関数・積を一sortへ構造的に写し，基本型を
DMの`Int`へ正規化して，matcher／slot wrapperとcapabilityを消去する．`ContextErases`はcore contextの
各scheme useとDM contextを関係づけ，`SchemeErases.generalize`がclosed signatureの下でlet
generalizationを保存する．`TypingInvariant.toDM`はpattern-free expressionの内部invariantを
DM derivationへ構造的に消去する．公開定理`DM.sourceTyping_to_dm`は次を与える．

```text
FrozenSigWF Σ → InFragmentExpr e → SourceTyping Σ [] e τ →
  ∃ τdm, DM.Typing [] e τdm
```

実際のwitnessは`eraseTy τ`である．必要な`TypingInvariant`は仮定ではなく，
`SourceTyping.typingInvariant`の監査済みclosed state erasureから得る．open contextのconverseは
主張しない．二つの定理を合わせると，指定したclosed fragmentではsourceからDMへの保守的な射影と，
得られたDM derivationの実行可能受理が成立する．型の比較はprincipality層に分離される．

### Source-order依存

checking cutはその時点のprevailing substitutionを適用したexpected headだけを観測し，未解決変数を
slotへ先読みして構造化しない．listはsource順にstateを渡すため，既知のslot demandが先に現れる
programは受理されても，同じ要素を逆順にしたprogramは拒否され得る．
`AcceptanceGapRegression.source_order_affects_source_typability`はこの差を`SourceTyping`の存在と
非存在の組として固定する．pre-scan，子の並べ替え，checking obligationの遅延，source-order
permutation invarianceは現行仕様に含めない．

将来この境界を変更する場合も通常単一化の失敗をcoercionの根拠に戻してはならず，未解決headの
constraintまたはchecking obligationを遅延する別calculusとして設計する必要がある．それは受理集合を
変えるため，基盤とそのcalculusに依存するメタ定理を再確立する必要がある．

## judgmentの役割

| 層 | 役割 |
|---|---|
| `SourceTyping` | source acceptanceを定義する唯一の公開judgment |
| `Reconstruction.ExprDeriv` | 成功した推論traceを再構成するproof-relevantな内部証明 |
| `TypingInvariant` | supply，substitution，origin ledgerを消去した動的メタ理論用の内部invariant |
| `ValueTy`／matching-state judgments | preservation，progress，matching safetyを記述するruntime側の型付け |

向きは`SourceTyping → TypingInvariant → runtime safety`である．`TypingInvariant`を第二のsource
type systemとして使ったり，その存在からsource acceptanceや推論成功を逆向きに導いたりしない．

`SourceTyping`は，canonical initial stateから始まるdemand-directed derivation，capabilityの由来を
追跡するOrigin certificate，終端substitutionで検査するterminal auditを束ねる．`infer`の成功や
`TypingInvariant`の存在を定義のpremiseには持たない．詳細は[`docs/details.md`](docs/details.md)を参照．

## demand-directed coercion

checkingは式を先にsynthesizeし，そのcutで解決したexpected typeのheadを一度だけ調べる．非恒等
coercionはexpected headが`MatcherSlot`の場合に限られる．

| resolved source | resolved expected | alignment |
|---|---|---|
| `Matcher κp τp` | `MatcherSlot κc τc` | matcher-to-slot |
| product of matchers | `MatcherSlot κc τc` | product liftの後にmatcher-to-slot |
| product of slots | `MatcherSlot κc τc` | slot-tuple lift |
| `MatcherSlot κp τp` | `MatcherSlot κc τc` | ordinary equality |
| その他 | その他 | ordinary equality |

expected typeが未解決変数ならordinary equalityだけを行う．coercionのために変数をslotへ推測せず，
ordinary equalityの失敗後に別branchを試すrollbackも行わない．solverはconstraint外のmetaを
構造化せず，capabilityのsubstitutionはOrigin ledgerが許す範囲に限られる．

この原則は`matchAll`専用ではない．たとえば`use : MatcherSlot κ τ → ρ`へ
`m : Matcher κ τ`を渡す場合も，関数適用のargument checking cutで同じalignmentを使う．

## 現在固定している境界

- matcher literalはactual clause evidence，shape，catch-all order，data-arm exhaustiveness，
  binder線形性，coverageをすべて要求する．
- value-flow schemeのcapability binderはvariableにだけinstance化し，consumer demandに合わせて
  producer capabilityを後から構造化しない．
- recursionはsingleton direct-selfの単相`fix`だけをcoreに含む．alias，mutual recursion，
  higher-order originはfail closedとする．
- `nestedCapProgram`とswapped版は拒否し，or-pattern，delegating matcher，let-polymorphic matcher
  producerは受理する．これらは正負回帰で固定済みである．
- 未解決lambda domainを複数箇所で共有すると，左から右のchecking順序が受理結果に影響し得る．
  これはno-guessとchronological state threadingから生じる意図された言語境界であり，source
  typabilityの正負定理と実行回帰で固定する．source要素の順序不変性は主張しない．

回帰ごとの対応と内部証明の構成は[`docs/details.md`](docs/details.md)，論文形式の規則とメタ理論は
[`tex/main.tex`](tex/main.tex)に記載する．

## モジュール案内

| 層 | 主なmodule | 役割 |
|---|---|---|
| public index | `PublicTheorems` | 主要な公開定理の入口 |
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| source typing | `DemandTyping*` | raw規則，Origin，terminal audit，soundness／completeness，state erasure |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，trace，terminal validator |
| principality | `TypeInstance`, `SourcePrincipality`, `RelativePrincipality` | 二sort instance preorder，target principality，context相対principality |
| internal typing | `Source`, `Reconstruction`, `CoherentTyping` | `TypingInvariant`と成功traceの再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety`, `Soundness` | evaluation，matching machine，公開安全性 |
| fragments | `DamasMilner`, `DamasMilnerAcceptance`, `DamasMilnerAcceptanceMutual`, `DamasMilnerConservativity`, `DMTerminalAcceptance` | pattern-free DM断片，canonical opening代数，全DM typingの公開受理，closed sourceからDMへの保守性，受理回帰 |

全moduleのpublic import surfaceは[`TypePM.lean`](TypePM.lean)である．詳細なmodule対応，定理，回帰一覧は
[`docs/details.md`](docs/details.md)を参照．

## 検証

```sh
lake build
cd tex
make
```

形式仕様の出力は`tex/type-pm-mech.pdf`である．`sorry`，`admit`，project-defined `axiom`は使わない．
公開定理が標準3公理（`propext`・`Classical.choice`・`Quot.sound`）のみに依存することは，
[`TypePM/AxiomAudit.lean`](TypePM/AxiomAudit.lean)が`lake build`のたびに検査し，逸脱はビルドエラーになる．
