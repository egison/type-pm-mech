# P2 非 CAS formal core：証明ターゲット

## 状態と目的

状態：設計判断・証明境界は固定済み，Lean への再構成は未実施（2026-08-02）．

この文書は，`Matcher κ τ`／`MatcherSlot κ τ` を用いて
`type-pm-mech` の証明を組み直す際の**完了判定**を定める．対象は，検証・freeze
済み signature を入力とする非 CAS の Egison core である．

現行の `type-pm-paper` は source calculus から再帰を外し，`list`／`multiset` を
既に型付けされた外部 interface として扱っている．しかし，実際の両 matcher 定義は
next matcher として `list m`／`multiset m` を直接自己参照する．したがって，利用側
だけでなく定義本体を型検査する Egison core の完成には，singleton direct-self の
source typing，型推論，評価，型安全性が必要である．

本書は再構成作業のターゲットを固定する文書であり，論文の形式仕様を変更したこと
自体を意味しない．実装と証明が揃った段階で，英語版 `main.tex` と日本語版
`ja/main.tex` の非再帰境界を本書に合わせて同期する．

## 固定する設計判断

1. `Matcher κ τ` と `MatcherSlot κ τ` は独立した型構文として残す．
   `Matcher` は runtime matcher 値の固有 producer capability を表し，
   `MatcherSlot` は利用位置の consumer demand と target を表す．両者の接続は
   producer-stable な一方向検査であり，同一視や通常の対称単一化ではない．
2. capability 変数と target 型変数は別 sort，別 substitution，別 quantifier とする．
3. Algorithm W の全体に対して要求するのは，論文と同じ
   **conditional reconstruction soundness** までとする．W の completeness，full
   Principal Type Property，qualified principality は完成条件に含めない．
4. source calculus は `Expr.fix f x e` に相当する singleton・direct-self・単相再帰を
   含む．再帰 binder は RHS の検査中に同一の monotype placeholder を返し，binder
   外へ出た後でだけ一般化する．
5. `ShapeCap` と `CoverageOK` は分離するが，source の matcher literal typing は常に
   actual clause list に対する `CoverageOK` を要求する．frozen signature が要求する
   pattern constructor の一般節が一つでも欠ければ，formal core では型エラーとして
   拒否する．既存 Lean の runtime 証明で `ordinary`／`covered` mode を残す場合，
   `ordinary` は coverage proof を消去する証明内部の weakening 先に限り，source
   language の受理 mode にはしない．full Egison が同じ不足を warning として扱う
   方針は formal core の外側に置く．
6. P1 の capture admissibility と埋込み計算の `StepReady` は P2 から独立した前提
   として最終定理に明示してよい．P2 に由来する capability-admissibility は
   declarative source typing，二種 Gen／Inst，runtime invariant から導き，最終定理の
   前提に残さない．Algorithm W の soundness は，推論成功をその declarative typing
   へ接続する．

本書では active P2 規則に合わせて，ある state の一ステップ探索が要求する埋込み
評価の局所停止性を `StepReady` と呼ぶ．旧一添字文書の `StepTotal` と同じ役割で
あり，一般の source program 全体の停止性ではない．

## 対象とする source core

対象となる source core は，既存の一添字 calculus が扱う lambda，application，
`let`，tuple，data constructor，matcher literal，`matchAll`，pattern function，および
matching state に，次を加えた二添字版である．

- `Matcher κ τ` と `MatcherSlot κ τ`
- capability／target の二種 scheme，generalization，instantiation，annotation
- actual matcher clause からの evidence，`ShapeCap`，`CoverageOK`
- `CoverageOK` を必須 premise とする matcher literal typing
- `fix f x.e` による singleton direct-self

term／runtime 構文は既存の `Expr.fix` と self 名つき `Value.closure` を再利用できる．
相互再帰用の新しい term syntax は追加せず，P2 型を使う `HasTy`，`ValueTy`，
`EnvTyped`，`WTState` と W の judgment を新設・移行する．

`list`／`multiset` の core-facing 定義は `fix` で表す．完全な表層定義に含まれる
`loop` pattern，複数節 `match`，型クラス，ライブラリ補助関数は，既存の core
construct または型付け済み primitive への elaboration を仮定してよい．ただし，
`list`／`multiset` 本体の recursive matcher 値を外部定数として仮定してはならない．

論文 core の frozen list pattern signature は `[]`／`::`／`++` の三構築子とする．
現行 `TypePM/Examples.lean` の `listM` は三つの一般節を持つため，この signature に
対する受理回帰の候補になる．一方，簡略 `multisetM` は `++` 節と `#$val` 節を
省いているため，formal core の source typing では拒否する負の回帰にする．multiset
の正の回帰には，三つの一般節と最後の catch-all を持つ paper-complete clause
interface の core elaboration を使う．
refinement／value-pattern 節は表層挙動への忠実性のため追加できるが，Coverage の
構築子列挙には数えない．表層固有の分解本体は `ProgramWF` で型付いた非 CAS
primitive へ落としてよい．

実 Egison の現在の list pattern signature はさらに `*:` を含み，標準 `multiset`
定義には対応する一般節がない．この四構築子 signature をそのまま formal core へ
freeze するなら，対応節を補うまでその定義は型エラーとして拒否される．標準
ライブラリ全体をこの signature へ移行することは本書の受入条件ではなく，full
Egison 側では同じ検査結果を warning として提示してよい．

## 最終的に得る定理の鎖

定理名は実装時に調整してよいが，主張の境界は以下に合わせる．

### T1．Concrete source bridge

二添字の source `HasTy`，pattern／primitive-pattern／clause／arm judgment，actual
clause-evidence judgment，および concrete `CoverageOK` を定義する．その上で，現在の
抽象 `CoreSpecWF` の各 field を source judgment から構成する．matcher literal の
`HasTy` 導出には必ずその actual clause list の `CoverageOK` を含め，coverage 不足の
literal には source typing derivation が存在しないようにする．少なくとも次を示す．

- 整型な actual clause に対して evidence checker が成功する．
- 一つの actual clause から成功時にちょうど一つの evidence が決まり，同じ入力から
  異なる evidence は得られない．
- evidence は target 型，expected type，consumer demand，結果 annotation から
  producer capability の seed を作らない．
- clause list と evidence list が一対一に対応する．
- 同じ captured runtime environment を実現する二つの source context は，同じ actual
  clause に対して同じ evidence を返す．
- admissible target substitution は evidence と inferred capability を変えず，source
  literal typing の target 側だけを輸送する．capability substitution は evidence，
  `ShapeCap`，`CoverageOK` を共変に輸送する．既存 `literalSubstitute` のように
  capability を不変に保つ形では `cap.apply C = cap` を明示する．
- `CoverageOK` と `CatchAllLast` から，matcher が要求された general clause へ
  catch-all より先に dispatch できる `DispatchOK` を導く．
- `NoHoleBeforePVal` を仮定した P1 bridge，または明示的な `CaptureAdm` premise と
  合成できる．

`RuntimeSpec` や抽象 `CoreSpecWF` に相対的な局所補題だけを，この target の完了とは
数えない．end-to-end 定理では concrete source instantiation を用いる．

### T2．Algorithm W の停止性と conditional soundness

W，pattern inference，slot checking，matcher-literal checking を有限な構文再帰として
定義し，成功または失敗が決定することを示す．W が成功した場合には，返された二種
substitution を context，結果型，残余 obligation の全 occurrence に適用した後，
対応する宣言的導出を再構成できることを示す．matcher-literal checking は
`CoverageOK` を必ず検査し，必要な一般節が欠ける入力では失敗する．概念的な結論は
次である．

```text
W Sigma Gamma e = success (S_cap, S_ty, tau, trace)
WBridgeWF Sigma
---------------------------------------------------
S_cap,S_ty(Gamma) |- e : S_cap,S_ty(tau)
```

`WBridgeWF` がまとめてよいのは，論文の conditional soundness が明示する次の前提に
限る．これらは無名の oracle にまとめず，個別の field または定理として追跡する．

- occurrence-wide な二種 source substitution
- returned substitution による `direct(Γ)` と `CapTargetOK` の保存
- protected target solver の soundness と relative-MGU factoring
- range-fixed composition と final slot-obligation replay の妥当性
- selected-result／escape ledger の lexical soundness
- tagged hole，demand freshening，source clause pass，`clauseEvidence` の対応

この target は，W が成功する全宣言的項を発見することも，返す型が全解の principal
type であることも主張しない．ただし，既に独立層で証明済みの `matchCap` の局所的な
soundness／completeness と witness 一意性は再利用する．

### T3．Singleton direct-self

宣言的 source typing には通常の単相 `fix` 規則を置く．

```text
Gamma, f : mono (tau1 -> tau2), x : mono tau1 |- e : tau2
---------------------------------------------------------
Gamma |- fix f x.e : tau1 -> tau2
```

matcher-producing self occurrence を判定する syntax-directed な `DirectSelf(f,e)`
judgment も定義する．matcher-producing `fix` の RHS における `f` の全自由出現を
shadowing-aware に走査する．tuple，matcher clause の next-matcher／decomposition
expression，nested `matchAll` の中にある `f m` のような，application の head に
直接現れる occurrence は認める．それ以外の別名への alias，関数引数としての受渡し，
返却関数を介した application，相互参照，captured higher-order origin が一つでも
あれば fail closed とする．「その occurrence が capability に影響するか」を一般
flow 解析で判定しない．`list m`／`multiset m` はこの judgment に含まれる．

W の `fix` case と matcher literal の Shape solver は，次の不変量を満たす．

- recursive binder には一つの fresh な単相 full-type placeholder を割り当てる．
- RHS 内のすべての direct-self lookup は同じ placeholder identity を返し，fresh
  instantiate しない．
- solver input の `Known` には source provenance derivation を要求する．供給源は，
  actual `clauseEvidence`，現在の再帰 literal に依存せず既に finalize 済みの別 literal，
  または型付けされた外部 matcher／slot が capability-visible な tagged hole／path へ
  実際に flow した occurrence に限る．未使用の外部値や slot parameter の存在だけから
  無関係な Shape obligation を seed してはならない．
- self-reference，consumer demand，expected result 型，annotation は capability の
  seed にしない．self-reference は同じ generation obligation への `Ref` とする．
- genuine evidence を exact merge し，mismatch を拒否してから `ShapeCap` を
  finalize する．その後に recursive occurrences と demand／annotation を検査する．
- unresolved placeholder を型，scheme，typed AST，runtime certificate へ逃がさない．
- 全 substitution と Shape finalization の後，binder の外側でだけ通常の二種 HM
  generalization を行う．

純粋な `fix f x. f x` のように matcher literal を生成しない単相再帰を，Shape seed
不足だけを理由に拒否する必要はない．ただし，その seedless cycle を structured
matcher capability の根拠にはできない．

この fragment の主要な受入例は次である．

```text
list     : forall p a. MatcherSlot p a
                         -> Matcher (List p) (List a)
multiset : forall p a. MatcherSlot p a
                         -> Matcher (List p) (List a)
```

両者について，定義本体の next matcher に現れる `list m`／`multiset m` を含む
source derivation と W の成功を構成する．型スキームだけを frozen environment に
仮定する検査は，この受入条件を満たさない．

この受入条件の正の回帰として，現行 `listM` を論文の三構築子 signature に対して
検査し，paper-complete multiset clause interface の core elaboration についても
source typing，recursive W，`CoverageOK`，certificate まで検査する．現行の簡略
`multisetM` は，direct-self の形が適切でも coverage 不足により source typing と W が
失敗する負の回帰にする．

### T4．Coverage-preserving runtime invariant

二添字の `ValueTy`，`EnvTyped`，`SubstTyped`，`WTTree`，`WTStack`，`WTState` を，
coverage-required な source semantics 全体へ接続する．既存 Lean 定義の都合で runtime
judgment を `ordinary`／`covered` に mode-index してもよいが，source typing から
構成する invariant は常に coverage を保持する側である．`ordinary` はその invariant
から coverage proof を消去する内部 weakening lemma の結論にだけ用い，source
program を追加で受理する入口にしない．

- matcher 値は生成時の intrinsic capability と target を保持する．
- matcher-to-slot の witness は capability／target／環境／後続 state の対応する全
  occurrence に適用される．
- tuple，lambda，application，`let`，closure，data storage，matcher environment，
  MNode を通っても capability は強化されない．
- `fix f x.e` は self 名を持つ closure に評価され，application 時の自己束縛が同じ
  monotype と intrinsic capability を保つ．
- recursive application の `pushArg` は argument と同じ self closure を整型環境へ
  追加し，続く matcher literal の評価はその環境を matcher value に capture する．
  後に選択された clause 内の next-matcher `f m` は，captured environment から同じ
  self closure を lookup して評価され，同じ finalized capability の matcher 値を作る．
- source-facing invariant は実際の clause list に対する concrete `CoverageOK` を
  保持する．必要なら proof-internal な coverage-erased invariant へ weakening できるが，
  逆向きの持上げや erased invariant だけからの source acceptance は認めない．

動的定理へ進む前に，次の bridge lemma を具体的な source／runtime judgment 上で
証明する．これらを旧 oracle のまま残さない．

- primitive-pattern preservation と，typed hole の順序・target 型・個数の保存
- primitive-pattern の hole と next matcher slot を結ぶ Structural-Hole Transfer
- `CoverageOK + CatchAllLast` からの `DispatchOK`
- pattern-function scheme の利用時 instance transport
- MNode の isolated scope，pattern environment，内部 state typing の保存

### T5．Preservation／Progress／Type Safety

まず，coverage-required な declarative source typing と runtime invariant から，次を
個別の定理として証明する．

1. evaluation derivation 上で必要な `CaptureAdm` の下での式評価の Preservation
2. local `CaptureAdm` の下での matching-state の一段 Preservation
3. `CaptureAdm` と `StepReady` の下での Progress
4. 一段 Preservation の反復による到達する全 matching state の整型性
5. 成功した terminal substitution の型付け
6. matcher consistency

`Step` が空の後続列を返す正当な match failure は stuck と数えない．再帰や埋込み
decomposition が発散する場合も型エラーとはせず，Progress の `StepReady` 前提の外と
する．

これらをまとめる declarative theorem を `core_safety` とする．この定理は
`HasTy` derivation から始まり，Algorithm W や `WBridgeWF` を前提に取らない．
`CaptureAdm` は実際に capture を扱う evaluation／state preservation と progress に，
`StepReady` は progress にだけ要求する．必要なら，到達する全 state に対する前提を
それぞれ `RunCaptureAdm`／`RunStepReady` として定義する．

`core_safety` がまとめる結論は，少なくとも次の五つを別々に取り出せる形に
する．

```text
evaluation preservation
one-step matching-state preservation
local progress under CaptureAdm and StepReady
well-typedness of every reachable state
typing of every successful terminal substitution
```

その上で，Algorithm W の成功を declarative theorem へ接続する
`infer_safe` を別の corollary とする．概念的な前提は次である．

```text
FrozenSigWF Sigma
ProgramWF Gamma0 Sigma SigmaF
WBridgeWF Sigma
infer Sigma Gamma0 e = success tau
for every reachable state s, CaptureAdm(s) and StepReady(s)
------------------------------------------------
the five safety conclusions hold for e at tau
```

この corollary に `capability-admissible`，任意の `RuntimeSpec`，既に型付け済みの
`list`／`multiset` matcher 値を前提として残してはならない．P1 を同じ作業で放電する
場合は，evaluation／reachable state に要求する `CaptureAdm` を
`NoHoleBeforePVal` を含む source well-formedness から導いて除けるが，これは P2
単独の完了条件ではない．

## 前提として残せるものと，証明で除くもの

| 項目 | P2 完成時の扱い |
|---|---|
| 検証・freeze 済み非 CAS signature の整形式性 | 明示的な入力前提として残せる |
| P1 capture admissibility | 独立前提として残せる．後に `NoHoleBeforePVal` から放電可能 |
| 埋込み評価の `StepReady` | Progress の明示前提として残せる |
| W の source-substitution／solver／ledger／clause bridge | 論文どおり conditional soundness の名前付き前提として残せる |
| `CoreSpecWF` の actual source instantiation | concrete source judgment から構成する |
| `CoverageOK` | actual clause list から構成し，source matcher literal typing の必須 premise にする |
| direct-self の `Known` provenance | source/W derivationから証明し，任意入力として残さない |
| capability-admissibility | declarative source typing，二種 Gen／Inst，runtime invariant から導き，最終前提から除く |
| list／multiset の matcher 値または型スキーム | 定義本体から導き，trusted constant として残さない |

既存一添字 `type_safety` の `hevG`，`hgen`，`hsiteReach`，`hclorc`，`hinstF` をそのまま
最終定理へ持ち越さない．必要な内容は concrete source bridge，W の名前付き
conditional premise，二種 substitution，coverage-preserving runtime proof のいずれかへ
分解して位置付ける．runtime proof に mode index を残す場合も，coverage-erased mode は
証明内部の weakening に限る．

Lean では上記前提を theorem parameter や整形式 structure として表現してよいが，
`axiom` を追加しない．また，条件付き定理の premise が未放電であることを `sorry = 0`
という事実で隠さない．

## 対象外

次はこの proof target の blocker にしない．

- W の completeness，full／relative Principal Type Property，qualified principality
- alias，transform，相互再帰，高階 application を通る一般 D4 producer flow
- raw declaration からの observability graph／projection signature／alias table の
  validator，freeze，import，load-unit persistence
- CAS の target-indexed pattern view，kind-aware projection，semantic equivalence
- full Egison の Coverage warning／diagnostic と，標準ライブラリ全体の formal core
  への移行
- 一般の式や再帰の停止性，DFS/BFS の公平性，全結果列挙
- `loop`／sequential pattern／型クラスなど full-language 表層機能そのものの意味論

一般 D4 を対象外にしても，`list` と `multiset` はそれぞれ一つの binder の
direct-self であり，`multiset` が利用する `list` は先に型付け済みの通常 binding と
して扱える．従って，両定義の core-facing 型検査に一般 SCC solver は不要である．

## 実装順序

1. P2 の型構文を既存 source syntax へ統合し，`Matcher`／`MatcherSlot` と二種
   substitution を唯一の経路にする．
2. 二添字 source typing，actual clause-evidence，concrete `CoverageOK` を実装し，
   `CoreSpecWF` を具体化する．
3. non-recursive fragment の W／Gen／Inst／annotation checking と conditional
   soundness を実装する．
4. `fix` の monomorphic placeholder と direct-self Shape obligation を W に追加し，
   non-seeding，seed propagation，mismatch，non-escape，finalization を証明する．
5. `ValueTy`／環境／closure／matching state を二添字・coverage-preserving に移行する．
   既存 mode index を再利用する場合，coverage-erased 側は内部 weakening 専用にする．
6. Preservation／Progress／Type Safety と inference-to-safety corollary を証明する．
7. `list`／`multiset` の正負回帰を通し，論文英語版・日本語版を同時に更新する．

前段の独立 P2 代数層は捨てず，二種 substitution，`matchCap`，observability，
projection，exact merge，annotation，runtime slot invariant，`CoreSpecWF` kernel を
この順序の部品として再利用する．

## 完了チェックリスト

- [ ] `Matcher κ τ` と `MatcherSlot κ τ` が独立した型構文として source typing，W，
      runtime typing の全層で使われる．
- [ ] actual clause-evidence と concrete `CoverageOK` から `CoreSpecWF` を構成できる．
- [ ] W の停止性と，論文の範囲の conditional reconstruction soundness が Lean で
      証明される．
- [ ] W の completeness／principal type を完成済みと主張しない．
- [ ] singleton direct-self の source typing，W，評価，Preservation が接続される．
- [ ] self-reference／annotation／consumer demand が capability を seed しない．
- [ ] `list` と `multiset` の core-facing 定義本体から上記の二種 scheme を導ける．
- [ ] source matcher literal typing と W は `CoverageOK` を必須とし，必要な pattern
      constructor の一般節が欠ける定義を拒否する．
- [ ] 現行 `listM` と paper-complete multiset interface は正の回帰として通し，簡略
      `multisetM` は coverage 不足の負の回帰として拒否する．
- [ ] `pushArg`，matcher closure の environment capture，clause 内の recursive
      next-matcher 再評価を通した runtime typing を証明する．
- [ ] unsafe capability strengthening と recursive exact mismatch の負例を拒否する．
- [ ] coverage-preserving full runtime invariant と Preservation／Progress／Type Safety が
      接続される．mode index を残す場合，coverage-erased mode は source 受理に使わない．
- [ ] 最終定理から P2 由来の `capability-admissible` と任意 `RuntimeSpec` が消える．
- [ ] 最終定理に残る P1／`StepReady`／frozen-signature／W conditional premises が
      名前付きで列挙される．
- [ ] 新しい `sorry`／`axiom`／`admit` がなく，`lake build` が通る．
- [ ] 論文英語版・日本語版と Lean の定義・定理境界が同期し，両版を `make` で
      ビルドできる．

## 既存文書との同期事項

本書に基づく再構成では，次の既存記述を更新する．

- 論文の「source calculus は非再帰」「`multiset` は外部 interface」という境界を，
  singleton direct-self の source typing／W／evaluation／safety を含む境界へ変更する．
- P2 台帳に残る W および direct-self の completeness／principality 要求を撤回し，
  conditional reconstruction soundness に統一する．
- 局所停止性の名称を active P2 の `StepReady` に統一する．
- `ProgramWF` は初期 source context を明示した
  `ProgramWF(Gamma0, Sigma, SigmaF)` の形で定義と定理文を一致させる．source の受理
  mode を表す添字は置かない．
- P1 の状態表示を「設計判断待ち」ではなく「中核設計解決済み，反映待ち」に揃える．

これらを論文へ反映するときは，英語版と日本語版を同じ変更単位で同期する．

## 主な参照先

- 既存の `fix` 構文・単相型付け・self closure 評価：
  [`TypePM/Syntax.lean`](TypePM/Syntax.lean)，
  [`TypePM/Typing.lean`](TypePM/Typing.lean)，
  [`TypePM/Semantics.lean`](TypePM/Semantics.lean)
- 現在の P2 独立層：[`TypePM/P2/`](TypePM/P2/)
- P2 の詳細な設計履歴：
  [`problem/matcher-capability-instantiation.md`](problem/matcher-capability-instantiation.md)
- P1 の採用条件：[`problem/value-pattern-scope.md`](problem/value-pattern-scope.md)
- 実際の `list`／`multiset` 定義：
  [`egison/lib/core/collection.egi`](../egison/lib/core/collection.egi)
- 論文の現行形式仕様：[`type-pm-paper/main.tex`](../type-pm-paper/main.tex)，
  [`type-pm-paper/ja/main.tex`](../type-pm-paper/ja/main.tex)
