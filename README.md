# type-pm-mech — Egison core の型推論と安全性

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．型には matcher を生成する
`Matcher κ τ` と，matcher を必要とする消費位置を表す `MatcherSlot κ τ` がある．

source program の型付け可能性を定義する judgment は `DDTyping` だけである．実行時安全性の
証明では，推論中の supply や substitution を消去した内部 certificate `RuntimeTyping` を使う．
両者の役割は次の一方向に整理する．

```text
source program
     │
     ▼
 DDTyping                 唯一の source typing
     │ state erasure      未完成：capability freeze 情報の統合が必要
     ▼
 RuntimeTyping            内部の state-free certificate
     │ preservation / progress
     ▼
 runtime safety
```

`RuntimeTyping` は source acceptance を定義する第二の型システムではない．逆に
`RuntimeTyping e τ` から `DDTyping e τ` や推論成功を導くことも意図しない．

## DDTyping

[`TypePM/DemandTyping.lean`](TypePM/DemandTyping.lean) は，全 source form と pattern／arm／
clause 層について demand-directed な型付けを定義する．式層の中心は synthesis と checking
の二判断である．

```text
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  DDCheck
```

`q = (qκ, qτ)` は capability metavariable と target metavariable の次の番号を持つ fresh
supply，`S` はその cut までに得た paired substitution である．各規則は子を左から右へ調べ，
出力 `q'; S'` を次の子へ渡す．公開 wrapper は canonical initial supply と恒等置換から始め，
最後に `S' τraw` を公開する．

```text
DDTyping Σ Γ e τ  iff
  ∃ τraw q' S',
    DDSynth Σ (initialSupply Σ Γ) id Γ e τraw q' S' ∧
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
exact MGU または exact one-way solution であり，constraint 外の metavariable を構造化しない．

coercion の場所は `matchAll` や matcher literal に固定されない．たとえば
`use : MatcherSlot κ τ → ρ` へ `m : Matcher κ τ` を渡す場合，関数適用が domain を決め，
引数の checking cut で matcher producer と slot demand が対応付けられる．`matchAll` の
matcher 引数と matcher clause の next-matcher も同じ `DDCheck` を使う．

## RuntimeTyping と安全性

[`TypePM/Source.lean`](TypePM/Source.lean) の `RuntimeTyping` は，fresh supply，solver の実行順，
origin ledger を持たない state-free certificate である．closure と matcher value はこの
certificate を保持し，preservation はそれを `ValueTy` へ移す．

実行可能推論については次の経路が機械化済みである．

```text
infer Σ Γ e = some r
  → Reconstruction.ExprDeriv Σ (r.S Γ) e r.resolvedTarget
  → RuntimeTyping Σ (r.S Γ) e r.resolvedTarget
```

中心となる定理は `infer_success_reconstruct` と `infer_success_runtimeTyping` である．公開
`infer` は停止する `inferRaw` と有限の fail-closed terminal validator の合成であり，caller
が bridge certificate や `InferenceInputWF` を渡す必要はない．

`FrozenSigWF` の下では，`RuntimeTyping` を持つ式の評価，matching state の一段保存，局所
progress，到達可能 state の保存，成功 branch の substitution typing を証明済みである．
一般の program termination は主張しない．

## 未完成の接続

現在の主な未完成部分は二つである．

1. `DDTyping → RuntimeTyping` の state erasure
2. `DDTyping → infer` の受理完全性

一つ目には capability origin の freeze 情報が必要である．現行 `DDSynth` は `q` と `S` を
持つが origin ledger を持たないため，量化された matcher producer の capability を後続 solve
が構造化したことを derivation だけから排除できない．`capFreezeProgram` と
`letCapFreezeProgram` はこの不足を固定する回帰である．解決方針は，producer capability の
生成・instance・一般化・export に必要な freeze provenance を DD family 自体へ統合し，その
情報を用いて `RuntimeTyping` へ射影することである．`RuntimeTyping` の存在を `DDTyping` の
premise に埋め込む循環的な定義は採らない．

二つ目には，上記 freeze 統合に加え，現行 executable selector が product source の認識に
raw type を使う箇所を cut-resolved view と一致させる必要がある．最終目標は追加 premise の
ない次の定理である．

```text
DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`nestedCapProgram` と swapped 版は DD で型付かず，推論器も拒否する意図された負例である．
一方，or-pattern，delegating matcher，let-polymorphic な matcher producer は DD の正例である．

## 機械化済みの主な性質

- `DDCheck` の非恒等 branch は slot-headed expected type に限られる．
- matcher-headed expected type では ordinary equality しか起こらない．
- DD family の supply は単調に進み，substitution は chronological delta replay に分解できる．
- DD が公開する型，pattern dual，bindings，hole ledger は終端 supply で有界である．
- exact MGU は constraint 外の metavariable を推測しない．
- matcher literal は shape，catch-all order，data-arm exhaustiveness，binder 線形性，coverage
  evidence をすべて要求する．
- `infer` の成功から reconstruction certificate と `RuntimeTyping` を再構成できる．
- `FrozenSigWF` の下で concrete evaluation と matching machine の安全性が成り立つ．
- `sorry`，`admit`，project-defined `axiom` はない．

## モジュール案内

| 層 | 主な module | 役割 |
|---|---|---|
| syntax | `Syntax`, `Term`, `ClauseEvidence` | 型，source form，matcher evidence |
| DD typing | `DemandTyping`, `DemandTypingRegression` | source typing，alignment，基本メタ理論と回帰 |
| runtime certificate | `Source`, `Reconstruction`, `CoherentSurface`, `CoherentTyping` | state-free certificate と再構成 |
| inference | `Inference*`, `BridgeChecks`, `CertifiedInference` | raw W，origin ledger，validator，成功時の再構成 |
| dynamics | `Semantics`, `Dynamic`, `Preservation`, `Safety` | evaluation，matching machine，安全性 |
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
