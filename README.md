# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．matcherを生成する型
`Matcher κ τ`と，matcherを必要とする消費位置の型`MatcherSlot κ τ`を分け，coercionを
消費側のdemandから決める．

source programの型付け可能性を定義するjudgmentは`SourceTyping`だけである．公開推論器`infer`は，
well-formedなsignatureの下で`SourceTyping`の存在を正確に判定する．closed programについては，
このsource typingから評価とmatching machineの安全性まで接続済みである．

## 現在の到達点

中心となる接続は次の三つである．

```text
infer Σ Γ e = some r
  ── soundness ──→ SourceTyping Σ Γ e r.resolvedTarget

SourceTyping Σ Γ e τ + FrozenSigWF Σ
  ── completeness ──→ (infer Σ Γ e).isSome = true

SourceTyping Σ [] e τ + FrozenSigWF Σ
  ── state erasure / safety ──→ TypingInvariant Σ [] e τ + CoreSafety
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
| `SourceTyping.safe` | closed `SourceTyping`から同じ型の内部invariantと動的安全性を得る |

ここで証明済みなのはtargetのrenaming一意性までであり，型のinstance preorder上のprincipalityは
まだ主張しない．一般のprogram terminationも主張しない．

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
  現在は回帰で挙動だけを固定しており，恒久的な言語境界にするかは未決定である．

回帰ごとの対応と内部証明の構成は[`docs/details.md`](docs/details.md)，論文形式の規則とメタ理論は
[`tex/main.tex`](tex/main.tex)に記載する．

## Roadmap

完了済みのsoundness，completeness，受理同値，安全性，target一意性を基盤`F`とする．今後は
principality系とDamas--Milner系を独立に進め，source-order依存について設計判断を行う．

```text
[x] F. soundness / completeness / safety / target uniqueness
    ├──→ [ ] P1. 二sort instance preorder
    │          └──→ [ ] P2. closed principality
    │                    └──→ [ ] P3. context相対principality
    ├──→ [ ] D1. 全DM.Typingのexecutable acceptance
    │          └──→ [ ] D2. DM断片でのconservativity
    └──→ [ ] O. source-order依存の設計判断
```

| ID | 作業 | 依存 | 達成後に主張できること |
|---|---|---|---|
| P1 | capability／target metaを同時に扱うinstance preorderを定義し，renamingとの関係を証明する | F | targetをmetavariable名ではなく一般性で比較できる |
| P2 | `inferType`が返すclosed targetのprincipalityを証明する | P1 | closed source programのprincipal typeを公開推論器が計算する |
| P3 | contextとtargetの同時instance化を含む相対principalityを定式化する | P2 | open termでも，明示したcontext可変性の下でprincipal typeを計算する |
| D1 | 任意の`DM.Typing` derivationから公開推論器の成功を導く | F | pattern-free let-polymorphismを推論器が取りこぼさない |
| O | 現在のsource-order依存を採用するか，規則を変更するか決める | F | typabilityの順序依存を意図された仕様または明示した不変性定理として説明できる |
| D2 | pattern-free・capability-inert・direct-self断片でDMとの双方向対応を証明する | D1；型比較にはP2／P3 | 二sort coreが指定したDM断片の保守的拡張である |

### P1--P3: principality

最初に，substitutionが変更してよい有限scopeを明示した二sort instance preorderを定義する．P2では
空contextに限定し，`inferType`の返値中のresidual metaを暗黙に量化したprincipal monotypeを扱う．
目標は次の形である．

```text
FrozenSigWF Σ → inferType Σ [] e = some principal →
  SourceTyping Σ [] e principal ∧
  ∀ target, SourceTyping Σ [] e target → TypeInstance principal target
```

P3でopen contextへ拡張する際は，context由来のmetaをすべてrigidにした強い形を採用しない．exact MGUの
向きによって異なる入力metaがtargetへ残り得るため，contextとtargetの組を同じsubstitutionで比較する
相対関係が必要である．

### D1--D2: Damas--Milner断片

現状は`DM.Typing → TypingInvariant`の埋込みとpolymorphic identityの受理例だけがある．D1では任意の
DM derivationから埋込みcontext上のsource typabilityを構成し，完成済みの受理完全性へ接続する．DM
derivationが選んだ型はprincipal targetの特殊化であり得るため，`inferType`が同じ型を構文的に返すとは
要求しない．

D2では対象となるpattern-free fragmentを明示し，`SourceTyping`の存在を境界に逆方向も証明する．
これをP2／P3と合成すると，coreの推論結果とDMのprincipal typeの対応を議論できる．

### O: source-order依存

現状を採用する場合は，no-guessとchronological state threadingの意図された帰結として仕様化する．
変更する場合は，通常単一化の失敗をcoercionの根拠に戻さず，未解決headのconstraintまたはchecking
obligationを遅延する設計を検討する．後者は受理集合を変えるため，基盤`F`と完了済みのP／D定理を
新しいcalculusに対して再確立する必要がある．

推奨する順序は，calculusに依存しないP1を先に行い，次にOを決定し，その後P2とD1を進め，最後に
P3とD2へ進む形である．

## モジュール案内

| 層 | 主なmodule | 役割 |
|---|---|---|
| public index | `PublicTheorems` | 主要な公開定理の入口 |
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| source typing | `DemandTyping*` | raw規則，Origin，terminal audit，soundness／completeness，state erasure |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，trace，terminal validator |
| internal typing | `Source`, `Reconstruction`, `CoherentTyping` | `TypingInvariant`と成功traceの再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety`, `Soundness` | evaluation，matching machine，公開安全性 |
| fragments | `DamasMilner`, `DMTerminalAcceptance` | pattern-free DM断片 |

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
