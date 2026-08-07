# type-pm-mech — Egison core の機械化

## 最上位目標

本リポジトリの完成目標は，Egison core の **demand-directed な注釈不要性**
（annotation-freeness）を機械化することである．その前提となる仕様を，推論器から独立した
構文主導の状態付き judgment `DDTyping` として定義する方針に固定する．完成定理は
`DDTyping` に対する公開推論器の受理完全性である：

```text
∀ signature e τ,
  DDTyping signature [] e τ →
  (infer signature [] e).isSome
```

`DDTyping` はまだ Lean 上で未定義・未証明である．内部には fresh supply `q` と prevailing
substitution `S` を入出力で thread する synthesis／checking の二判断を置く：

```text
q; S; Γ ⊢ e ⇒ τraw ⊣ q'; S'       -- DDSynth
q; S; Γ ⊢ e ⇐ τexpected ⊣ q'; S'  -- DDCheck
```

closed wrapper `DDTyping` は `initialSupply signature context` と identity substitution から
開始し，終端 substitution を raw result に適用した型を公開する．これは実行関数の成功や
`CoreTyping` の存在を前提にした定義ではなく，fresh allocation，通常 solve，coercion selection，
左から右の構文走査を帰納規則として独立に記述する．core の構文
（[`TypePM/Term.lean`](TypePM/Term.lean)）自体には型注釈の形がないので，上の完成定理が最終的に
保証したい「`DDTyping` を持つ closed program は注釈なしで受理される」の正確な主張である．

これと区別して，広い `HasTy` を前提とする次の命題を
[`TypePM/CoherentTyping.lean`](TypePM/CoherentTyping.lean) の
`Coherent.WideAnnotationFree` と呼ぶ：

```text
∀ signature e τ,  HasTy signature [] e τ → (infer signature [] e).isSome
```

`WideAnnotationFree` は完成目標でも open goal でもなく，境界を固定するために残した
**恒久的に反証済みの命題**である（`wideAnnotationFree_refuted`）．宣言的 `HasTy` の
無条件 coercion 規則（`coerceMatcherToSlot` 等）は動的安全性の包絡としては維持するが，
受理完全性の前提としては広すぎる．

最終目標を成立させる根本原則は **demand-directed coercion**（要求駆動の coercion 挿入）
である．`DDCheck` は必ず先に期待型なしで式を synthesize し，その出力state
`q₁; S₁` を exact coercion cut とする：

```text
q₀; S₀; Γ ⊢ e ⇒ τraw ⊣ q₁; S₁
head (S₁ τexpected) が要求する branch を選択
q₁; S₁ から source と expected を整合
```

non-identity coercion を選べるのは，この cut で `S₁ τexpected` の matcher／slot head が既に
露出している場合だけである．checking 開始前の `S₀` でも，全走査後の substitution でもなく，
synthesis 後かつ当該 coercion 前の `S₁` を見る．特に matcher→slot coercion は expected head が
`MatcherSlot` の場合にだけ許す．λ domain は任意の型として選ばず fresh
metavariable とし，application は function synthesis，fresh domain／codomain，通常 alignment，
argument synthesis，domain check の順で state を thread する．list 構文も左から右へ進める．
要求が未確定なら source は raw synthesized type のままで，通常 alignment が期待metaをそのraw型へ
固定できるが，coercionを成立させるために matcher／slot headを発明しない．各solve deltaはその時点で
解くconstraintに対するMGUまたはone-way solutionに限定し，無関係なmetaを同時に構造化しない．

この順序自体が正当なdemandの由来を与えるため，別のdemand-origin tokenやDunfield--Krishnaswami風の
ordered existential contextは導入しない．また，coercion可否をsemantic entailmentで定義せず，通常の
unificationが失敗してから別のcoercion branchを試す方式も採用しない．coercion branchはunification前に
上のvisible headから決定し，そのbranchのsolveが失敗すればそのcheckは失敗する．

### 関連研究から採用する部分

[Dunfield--Krishnaswami](https://doi.org/10.1145/2500365.2500582) から採用するのは，前の
premise の出力を次の premise の入力へ渡す algorithmic judgment の input/output state
threading だけであり，ordered existential context そのものは採用しない．
[Luo の polymorphic coercion inference](https://doi.org/10.1017/S0960129508006804) にある，
通常の unification が不成立だったことを負の前提として coercion insertion へ進む分岐も採用しない．
[OutsideIn(X)](https://doi.org/10.1017/S0956796811000098) は，広い宣言仕様とは別に guess-free な
solution／simplifier と algorithmic completeness 条件を置く先例として参照するが，式から制約を
生成して後段でまとめて解く constraint-generation／solving architecture は採用せず，`DDTyping`
自身が構文走査中に state と solve を逐次 thread する．

expected-head visibilityと，現行selectorの **raw-source visibility** は区別する．`DDTyping` の
demand規律は前者で定めるが，現行 `expectedCoercionSource` はproduct liftのsourceを
`S₁ τraw` ではなくraw `τraw`から認識する．従って最初の受理定理には，選ばれたproduct liftのheadが
raw sourceにも見えているという別条件 `RawSourceVisible` を置く．この条件はdemandの権威ではなく，
現行実装との対応条件であり，後にcut-indexed coercion eventで外す．

`nestedCapProgram`（と swapped 版）について現在機械化されているのは，`sharedSlot` を選び
demand の無い位置で matcher→slot coercion を使う一つの `HasTy` 導出と，公開推論器による拒否で
ある．これは `WideAnnotationFree` を反証するには十分だが，「すべての `HasTy` 導出がその coercion
だけを通る」という inversion は未証明であり，`DDTyping` の定義にも不要である．代わりに，fresh
lambda-domainと上記のsolve順序から `nestedCapProgram` に `DDTyping` がないことを反転で証明する．
同じproducer対を `let` で多相化した `nestedCapLetProgram` は，各利用がfreshなdomain instanceを
持ち，raw producer型のまま `DDTyping` と公開受理の正例になる．

最初の具体的反例だった or pattern（両分岐で同名を束縛する
`matchAll 0 something ($x | $x) x`）は，or の整合を raw binding context の構文的
等価から binder 名の照合＋型の単一化（`alignBindings`）へ改めたことで解消し，
受理側の regression として固定した
（[`TypePM/AcceptanceGapRegression.lean`](TypePM/AcceptanceGapRegression.lean)）．
constructor instance capability の producer guard による固定も解消した．
`packProgram` = `Pack something`（`∀κ α. Matcher κ α → Packed`）では，fresh `κ` を
局所 solve 中だけ `structuralFlexible` として `Any` へ特殊化し，export 時には prevailing
result に生存する変数 leaf だけを `renameOnly` へ freeze するため，raw／public の両方で
受理される．principality と異なり，受理完全性は
`(something, something)` の機械化反例と両立する：反例が否定するのは推論結果からの
代入による全型付けの回収であって，受理そのものではない．

達成済みの主柱は逆方向の soundness である．

> The soundness of executable type inference for the Egison core is mechanized in Lean 4.

公開 `infer` は raw な停止 W 走査 `inferRaw` と有限な terminal validator を合成し，
`infer_success_sound` は成功等式だけから宣言的 `HasTy` を返す．これは意図する
`InferenceInputWF` 入力に限定した主張より強く，`WBridgeWF` は validator が内部で
構成する証明書であって呼び出し側の仮定ではない．

段階の詳細は次節ロードマップにまとめる．現在は段階 1 が完了し，段階 2 は宣言側，
対称 MGU の公開 wrapper 完全性，origin-aware 局所 solve，全 W traversal の状態／
admissibility 不変量まで進んでいる．core の一意性と Egison コンパイラ全体の検証は主張しない．

## ロードマップ

無制限の principality は機械化済み反例により偽であり，どの段でも復活させない．
各段は独立に主張として成立する形で積む．

### 段階 1: coherent surface typing 基盤 — 済

- **済** coherent surface typing（`Coherent.CoherentExpr` ほか 10 family，
  [`TypePM/CoherentTyping.lean`](TypePM/CoherentTyping.lean)）．reconstruction
  certificate `ExprDeriv` そのものへの定義的 abbreviation（`CoreTyping` と同じ前例）で，
  pattern 層は threaded，式 premise は certificate 自身へ再帰する．
- **済** surface への忘却 `CoherentExpr.toHasTy` と推論成功からの
  `infer_success_coherent`（pattern 層の standalone threaded 境界への忘却は既存の
  `PatternResolutionDeriv.toThreadedSurface`）．
- **済** product lift 構成子の raw-source provenance 添字（`RawSourceVisible` を仮定する
  中間定理で，selector の選択と raw source を結ぶ装置）．W の reconstruction motive は
  selector が実際に頭を検査した raw type を
  faithful に注入し，恒等 witness も常に取れるため判断を制限しない．
- **済** 旗艦例の coherent instance（`listMatcherMatchAll_coherent`）．
- **済** pval-free 吸収補題（fragment 記述の精密化用）：`pval` leaf を含まない
  pattern では threaded surface 境界と reconstruction 証明書が一致する
  （`ThreadedPatternResolution.toDeriv_of_pvalFree`，
  [`TypePM/CoherentSurface.lean`](TypePM/CoherentSurface.lean)）．二 family の差は
  `pval` の式 premise（`HasTy` 対 `ExprDeriv`）だけなので，`pval`-free では
  昇格すべき式 premise が存在しない．

### 段階 2: Damas–Milner 断片の全受理

宣言側は完了している．

- **済** DM 埋め込み `DM.HasTy.emb`
  （[`TypePM/DamasMilner.lean`](TypePM/DamasMilner.lean)）．
- **済** match-free 断片の全 coherence
  （`coherent_of_matchFree`）: `matchAll` と matcher literal を
  含まない式の宣言的型付けはすべて coherent．
- **済** その系 `dm_coherent`: DM のすべての宣言的型付けが埋め込みを経て coherent
  judgment に入る（多相 let 証人の instance `idProgram_coherent` つき）．

算法側は次の順で積む（DM 断片自体は or・matcher 固有の問題と独立に進められる）．

1. **済** MGU 最汎性: [`TypePM/Unification.lean`](TypePM/Unification.lean) の
   proof-carrying kernel が `universal` certificate を構成し，
   `mguCapFuel_universal`／`mguTyFuel_universal`（list・spec-level 版含む）として
   公開する．
2. **済** 受理ギャップの regression 固定 — 既知の三系統をすべて
   [`TypePM/AcceptanceGapRegression.lean`](TypePM/AcceptanceGapRegression.lean) で
   機械化済み．or pattern は宣言的型付けと（修正後の）受理．nested matcher
   capability は `nestedCapProgram`（と逆順の swapped 版）：機械化した `HasTy` 導出は
   λ束縛 domain に `sharedSlot` を選び，demand の無い位置で coercion を使う一方，
   demand-directed な推論器は第一用法で domain を raw matcher 型に固定し第二用法の
   capability を注釈として rigid 比較して拒否する．この導出と拒否の組が広い `HasTy`
   前提の `WideAnnotationFree` を反証する（`wideAnnotationFree_refuted`）．全 `HasTy` 導出が
   同じ coercion に依存するという inversion は未証明である．`let` 多相化した
   `nestedCapLetProgram` の受理に加え，結果が三つの相異なる target 変数を持つ raw
   producer-level shape のままであること（`nestedCapLetProgram_raw_target_shape`）と，raw solve
   trace に `producerToSlot` が無いこと（`nestedCapLetProgram_raw_has_no_producerToSlot`）を
   control として固定した．旧 capability-freeze 反例 `packProgram`
   （`Pack : ∀κ α. Matcher κ α → Packed` に `Pack something`）は paired W 配線後の
   raw／public 受理，結果型 `Packed`，coherent reconstruction，solve-cut の flexible
   ledger snapshot，dead export leaf の非 freeze を固定する正例へ反転した．さらに
   `κ₀ ↦ List κ₁` の prevailing image を export すると生存 leaf `κ₁` だけが
   `renameOnly` になり，後続の構造的 strengthening が拒否される回帰を持つ．
3. **済** or-pattern binder の整合 — or の分岐結果を raw metavariable ID の構文的
   等価で比較する方式をやめ，`alignBindings` が binder 名を位置ごとに照合して
   束縛型を単一化する．certificate 側は deriv／threaded の or 規則を「左右の raw
   結果 Δ＋prevailing 像の等価 premise」へ緩和した（宣言的 Terminal or は不変）．
4. **大半済** origin-aware な再帰的 paired unifier — kernel slice は
   [`TypePM/PairedUnification.lean`](TypePM/PairedUnification.lean) に機械化済み：
   `solvePairedTy` が型構造を再帰しながら capability／target の二 sort を同時に
   解き，matcher／slot 注釈は origin-oriented capability solver（`renameOnly` は
   構造化禁止・rename 像は非 flexible 限定・`structuralFlexible` は構造化許可・
   未登録は rigid）へ送る．全成功は soundness と `AdmissiblePost` 準拠を運ぶ
   proof-carrying certificate（`mguPairedTy_sound`／`mguPairedTy_admissible`）で，
   capability／target 両 component の有限 support certificate も返す．二 sort 合成は
   `Subst.seq` の閉性による．さらに任意の admissible competitor が結果を吸収する
   origin-relative factorization（`mguOrientedCap_universal`／
   `mguPairedTy_universal`）を証明した．`mguTy` が rigid 比較で拒否する同じ
   注釈制約を flexible ledger の下で解く対照回帰
   （`paired_solves_flexible_annotation`／`symmetric_still_rigid`）つき．W の
   `capEq`／`targetEq` もこの solver へ接続し，各 `SolveStep` が cut-local ledger
   snapshot を保持する．constructor／primitive binder は local solve 中だけ flexible，
   完了時には raw binder でなく prevailing image と exported payload の共通 leaf だけを
   freeze し，明示的 export event を残す．payload は expression result に加え，pattern
   result capability／target／bindings，PPat の holes／bindings，DPat bindings まで含む．
   これにより `packProgram` は受理へ反転した．
   `producerToSlot` も exact `CapMatch` substitution の finite support 上で
   `admissibleCapPostCheck` を実行し，`solveResolvedWithLedger_admissible` は三 constraint
   共通に cut-local `AdmissiblePost` を返す．既存 one-way reconstruction certificate と
   `protectedCaps` terminal bridge は維持する．`InferenceLocalFactorization.lean` は
   origin-relative universality と one-way uniqueness から三 branch の ledger-aware 単制約因子化を与える．
   `InferenceTraceFactorization.lean` は evolving residual の scoped 条件の下で一段 snoc する．
   `InferenceFreezeTransport.lean` は selected leaf が更新後 ledger 上で safe rename であるという
   条件付き frozen-residual bridge を与える．残るのはその条件を全 traversal で
   保存する trace-level factorization と，legacy terminal guard を safe rename へ繋ぐことである．
   oriented Cap／Cap-list／paired Ty／Ty-list の
   成功 fuel 単調性と public bound への成功再生は証明済みだが，solvability completeness は
   まだ主張しない．`nestedCapProgram` は demand-directed 原則下の意図された拒否である．
5. **大半済** fuel 単調性と solvability — 単調性（成功は任意のより大きい fuel で
   同じ substitution のまま保存される：`mguCapFuel_mono`／`mguTyFuel_mono`，
   list 版含む）と **∃fuel solvability completeness**（可解な制約はある fuel で
   成功する：`mguCapFuel_complete`／`mguTyFuel_complete`／list 版，可解性との同値
   `mguCapFuel_isSome_iff_unifiable`／`mguTyFuel_isSome_iff_unifiable`）は
   機械化済み．kernel の非重複 match への再構成は不要だった：branch 選択は fuel に
   依存しないので，単調性は fuel の直接帰納で fuel 非依存な行は definitional
   equality により閉じる．完全性は（残 budget 変数数，構造 weight）の辞書式
   well-founded 帰納で，真に不等な head の解が budget 変数を一つ消去することを
   kernel 成功 run の range／elimination certificate
   （`solveCapPair_varCert`／`solveTyPair_varCert`）が供給する．公開対称 wrapper はこの
   well-founded 帰納と同じ入力依存の `mguCapCompleteFuel`／`mguTyCompleteFuel`
   （list 版含む）を使う形へ切り替え，`mguCap_complete`／`mguTy_complete`
   （list 版含む）が可解入力での公開 wrapper の成功を証明し，
   `mguCap_isSome_iff_unifiable`／`mguTy_isSome_iff_unifiable`（list 版含む）で逆向きと合わせる．
   origin-aware kernel 側も `solveCap_success_mono`／`solvePairedTy_success_mono`（各 list 版含む）により
   成功を任意のより大きい fuel へ同一 substitution のまま再生でき，
   `mguOrientedCap_of_fuel_le`／`mguPairedTy_of_fuel_le` が公開 bound 以下の run を wrapper へ繋ぐ．
   残るのは，旧 `capFuel`／`tyFuel` の全 admissible-solvable 入力に対する十分性，
   または input-directed complete driver への置き換えである．逐次 substitution が構造 weight を
   増やし得るため，対称 kernel と同様の変数消去 budget 証明が必要である．
6. **一部済** `inferRaw` の状態不変量と trace-level factorization — 単制約の `universal`
   を，`Subst.seq` で連結された solve trace・capability／target の相互作用・
   one-way `CapMatch`・origin／freeze admissibility・relevant variable 上の因子化
   へ格上げする（段階 2 最大の作業）．履歴側の語彙は
   [`TypePM/InferenceHistory.lean`](TypePM/InferenceHistory.lean) に既設
   （`InferState.HistoryPrefix` の refl／trans／`prevailing_eq`＝prevailing の
   replay 因子化と，各 traversal の prefix 補題群）．さらに
   [`TypePM/InferenceStateExtension.lean`](TypePM/InferenceStateExtension.lean) は
   history prefix，二つの fresh supply，`protectedCaps` 包含を束ねる強い
   `StateExtension`，refl／trans，record／fresh／protect／instantiate／export-freeze／
   単制約成功の extension 補題を持つ．
   [`TypePM/InferenceTraversalStateExtension.lean`](TypePM/InferenceTraversalStateExtension.lean)
   は alignment，expression／pattern／clause／matcher の全相互再帰 helper を持ち上げ，
   最終 `inferRaw_stateExtension` まで supply／producer 単調性を証明する．
   [`TypePM/InferenceAdmissibleTrace.lean`](TypePM/InferenceAdmissibleTrace.lean) は各
   `SolveStep` が自身の ledger snapshot に admissible である invariant，local solver snapshot
   の一致，raw／resolved 単制約実行の保存，history prefix/suffix の代数を与える．
   [`TypePM/InferenceTraversalAdmissibleTrace.lean`](TypePM/InferenceTraversalAdmissibleTrace.lean)
   はこの invariant を全 mutual traversal と protected-result filter へ持ち上げ，初期 empty
   state からの `inferRaw_admissibleTrace` まで証明する．
   [`TypePM/InferenceLocalFactorization.lean`](TypePM/InferenceLocalFactorization.lean) は oriented
   Cap／paired target の relative universality と `CapMatch` の support-restricted uniqueness を組み合わせ，
   `solveResolvedWithLedger` の三 branch すべてに admissible competitor の局所因子化を与える．
   [`TypePM/InferenceTraversalLocalFactorization.lean`](TypePM/InferenceTraversalLocalFactorization.lean) は
   各 `SolveStep` が自身の snapshot／resolved constraint／delta に対する `HasLocalFactorization` を
   持つ `FactorizingTrace` を定義し，全 mutual traversal と terminal protected-result filter へ持ち上げ，
   `inferRaw_factorizingTrace` まで証明する．
   [`TypePM/InferenceRunInvariants.lean`](TypePM/InferenceRunInvariants.lean) の
   `inferRaw_runInvariants` は `StateExtension`／`AdmissibleTrace`／`FactorizingTrace` を raw W 成功時の
   一つの証明書に束ねる．
   [`TypePM/InferenceTraceFactorization.lean`](TypePM/InferenceTraceFactorization.lean) は
   `TraceFactorization` を定義し，prefix residual が次の ledger snapshot に admissible でその
   resolved constraint を解くことを明示前提として，局所因子化を snoc／
   `recordSolve`／`runResolvedConstraint`／`runConstraint` へ安全に合成する．
   [`TypePM/InferenceFreezeTransport.lean`](TypePM/InferenceFreezeTransport.lean) は export で選択した
   leaf の residual 像が更新後 ledger で safe variable rename であるという正確な局所条件の下，
   選択的 `renameOnly` transition 後へ admissibility と scoped trace factorization を同時に輸送する．
   現行 `FixesCapVars` はその強い十分条件として接続済みである．残るのは
   substitution agreement-on-scope，次の residual の admissibility／solvability，export の safe-rename 条件を
   mutual traversal 全体で保存する証明である．
7. **一部済** terminal validator の受理 —
   [`TypePM/DMTerminalAcceptance.lean`](TypePM/DMTerminalAcceptance.lean) は多相 `let` の具体証人
   `let id = λx.x in (id id) 1` について，exact raw result への `inferRaw` 成功，
   `wBridgeCheck = true`，そこからの `WBridgeWF` 構成，結果型 `Int`，公開受理を一本の
   nontrivial 境界として固定する．任意の DM raw 成功に対する validator 受理には，
   instance／alignment／generalization check を通す trace invariant の一般証明がまだ必要である．
8. 到達点: `DM.HasTy → infer 受理`（古典的 ML の注釈不要性保証）．

### 段階 3: `DDTyping` と条件付き受理完全性

1. 未: `DDTyping` の定義 — 推論器から独立な帰納的 `DDSynth`／`DDCheck` を定義し，fresh
   supply と prevailing substitution を入出力で thread する．λ domain は fresh meta，
   application と list は現行 W と同じ左から右の順序とし，各 solve は当該 constraint に
   関係する MGU／one-way solution だけを追加する．`DDCheck` は式を先に synthesize し，その
   直後かつ coercion 前の state で正規化した expected head から branch を一意に選ぶ．branch
   選択後の solve が失敗した場合はその check を棄却する．実行関数の成功や
   `ElaborableHasTy := ∃ CoreTyping` を定義に含めない．
2. 未: `DDTyping` の基本メタ理論 — state extension，prevailing replay，freshness，solve delta の
   relevance，`HasTy` への忘却，reconstruction certificate（`CoherentExpr`）への変換を証明する．例の境界は
   `nestedCapProgram` と swapped 版に `DDTyping` がないこと，`nestedCapLetProgram` に
   `DDTyping` があることをそれぞれ inversion／構成で固定する．前者について全 `HasTy` 導出を
   分類する必要はない．
3. 未: 現行実装に対する最初の受理定理 — `d : DDTyping signature [] e τ` に対し，
   `RawSourceVisible d` と `FreezeCompatible d` を仮定して
   `(infer signature [] e).isSome` を証明する．前者は product lift の選択時に必要な head が
   raw source にも現れているという selector 実装上の条件，後者は現行 producer guard による
   固定と衝突しないという条件であり，どちらも coercion demand の由来を定義する条件ではない．
   証明は `DDSynth`／`DDCheck` の導出帰納を W の走査に同期させ，段階 2 の trace-level
   factorization と terminal-validator 受理を利用する．
4. 未: principal-core factorization の**存在定理**を先に立てる — ∀ surface typing に
   ∃θ plan，`plan : NormalPlan (θ τ₀) τ`．一意性は residual substitution が異なる
   因子化（`α ↦ Slot Any Integer` に `refl`，`α ↦ Matcher Any Integer` に
   `matcherToSlot`）を許すため plan kinds だけでは決まらない．「substitution が
   coercible head を導入しない」等の canonical boundary を定義した後に条件付きで
   狙う．定理は inference acceptance・factorization の存在・（canonicalization 後の）
   一意性の三本に分ける．

### 段階 4: `DDTyping` 受理完全性の最終形

1. 未: solve-cut event（cut-indexed coercion event）を導入し，prevailing substitution 後に
   初めて product head が現れる正当な case も selector が扱えるようにして，中間定理から
   `RawSourceVisible` を外す．
2. **大半済** W を origin-aware paired solver へ切り替え，solve cut ごとの ledger snapshot と
   export 時点の prevailing-image freeze event を接続した．`packProgram` の
   producer-freeze ギャップは解消し，`nestedCapProgram` の拒否は不変である．残るのは
   safe rename の terminal bridge と，trace factorization から中間定理の
   `FreezeCompatible` 仮定を実際に除去する証明である（one-way branch の finite-support
   ledger certificate は済）．
3. 未: canonical core judgment の critical pair を解消し，canonical boundary 下の full plan
   uniqueness と置換に対する naturality を証明する．
4. 到達点: `DDTyping signature [] e τ → (infer signature [] e).isSome`．受理完全性の前提は
   `DDTyping` だけとし，広い `HasTy` 前提の `WideAnnotationFree` は復活させない．

## 概要

非 CAS の Egison core を Lean 4 で機械化するリポジトリである．形式仕様は
[`tex/main.tex`](tex/main.tex)，Lean の public import surface は
[`TypePM.lean`](TypePM.lean) である．

現行 calculus は matcher producer と利用位置の要求を分ける．

```text
Matcher     κ τ   -- 値が生成時から持つ intrinsic capability
MatcherSlot κ τ   -- pattern site が要求する consumer capability
```

capability と target type は別 sort，別変数，別 substitution，別 quantifier を持つ．
producer から slot への接続は対称単一化ではなく producer-stable な one-way check で
行う．動的定理は concrete source/runtime judgments だけを使う．

`Any` はこの one-way check の **consumer 側に明記されたときだけ** wildcard であり，
任意の producer capability を受理する．producer 側の `Any` は wildcard ではない．また，
consumer 変数 `κ` が一度 `Any` に束縛されても，二度目以降の同じ `κ` は保存された
`Any` と厳密に一致しなければならない．従って `[Any, K]` を `[κ, κ]` に合わせることは
失敗する一方，literal `[Any, κ, κ]` の先頭だけは独立した wildcard になる．対称な
`mguCap` では `Any` は通常の rigid ground constructor であり，`Any = Any` のみが
直接成功する（flexible variable を `Any` へ束縛することはできる）．

## 証明している範囲

### Source typing

- lambda，application，`let`，tuple，data constructor，primitive，`something`
- matcher literal，`matchAll`，pattern function
- `f ≠ x` と `DirectSelf.Holds f e` を要求する singleton direct-self の単相
  `fix f x.e`
- user pattern，primitive-pattern pattern，primitive data pattern，clause／arm
- actual clause からの決定的 evidence，`PPatCapsAt`，`ShapeCap`，`CoverageOK`

matcher literal の型付けは，actual clause list に対する `CatchAllLast`，data-arm
exhaustiveness，binder 線形性，`CoverageOK` を必須とする．coverage を欠く literal を
追加 mode で受理する経路はない．
Frozen signature の lookup table は有限 map として扱い，pattern-function 名の
非重複性を `FrozenSigWF` が明示的に保持する．
`HasTy.fix_inversion` は宣言的に型付く `fix` からこの二つの条件を回復し，
`higherOrderFix_untypable` は再帰 binder を引数として渡す具体反例の拒否を固定する．
Pattern-function 定義の本体は freeze 済みの完全な signature で型付けする一方，
自身の scheme は generalization の ambient free-variable 集合から除外する．
その canonical core payload は引数と結果（target 型内部の capability も含む）を一つの
occurrence 列として数える．signature または context に自由な ambient capability は
そのまま自由に保ち，非 ambient な変数は，一度だけ現れるなら全出現を `Any` に
canonicalize し，二度以上現れるなら一つだけ量化して共有を保存する．`PatternDefTy` は
この正規化済み引数／結果に対する，一つの prevailing substitution を伴う
`ResolvedPatternTy` として本体を保持する．この prevailing substitution を canonical な
singleton-default substitution そのものとは同一視しない．利用時の `ValueFlowInst` は共有変数の
rename と target specialization だけを行い，singleton default を後付けの構造置換として偽装しない．
固定済み lookup scheme と context ごとの局所 generalization は，数値 binder 名の
構文的一致ではなく `DualScheme.ValueFlowEquivalent` で結ぶ．これは両 scheme の
`ValueFlowInst` が同じ引数／結果を許し，自由 capability／target 変数集合も等しいことを
要求する．従って alpha-renaming を含む観測不能な binder 表現差を許す一方，宣言の
value-flow 意味と ambient free-variable 境界は変えない．
自己 `papp` は `pval` 内の `matchAll` や matcher clause の next／arm body を含む
全構文を走査して拒否するため，別定義への参照を許しながら直接自己再帰を受理しない．

各 clause は最終 matcher capability でも添字付けされる．nested primitive-pattern
hole はその構造位置の capability と一致し，bare root hole だけが catch-all として
独立した slot capability を消費できる．Pattern constructor の capability projection は
partial evidence を返してよく，`CapCompatible` がそれを最終 capability の canonical
evidence と exact merge できることを要求する．このため，element capability を直接は
観測しない nullary `nil` も周囲の list capability と整合できる．Generic な
`projectSignature`／`CapCompatible` は result type variable へ到達する evidence だけを
運ぶ **result-variable evidence projection** を行う．Actual clause 専用の
`projectClauseSignature` は，その前段に actual hole evidence に対する
**closed field-head validation** を追加し，この二つを混同しない．
wildcard／value-pattern-pattern による `unseen` child は hole obligation を課さない．
一方，closed structured field は結果へ evidence を運ばなくても，actual hole の next
matcher が field の observable path と同じ capability head／arity を持つことを要求する．
`Matcher Any [Integer]` 自体は有効であり，closed list hole の next matcher として
使う場合だけ不適合になる．

さらに formal core の primitive-pattern pattern は depth-first・左から右に走査し，
一度 hole を通過した後に value-pattern-pattern `#$x` が現れる形を禁止する．例えば
`cons $ #$x` や `($, #$x)` は core では不受理だが，`cons #$x $` は受理する．この順序は
`PPatCoreOrder`／`PPat.coreOrderCheck` で表し，`clauseEvidence` の成功条件とする．
`inferRaw` は matcher literal の finalization でこれを検査して不正順序を棄却し，公開
`infer` の terminal validator も最終 substitution の下で clause evidence を再計算する．
従って raw finalization と terminal cut の二箇所が fail closed になる．full Egison では利便性のため
同じ条件を `--pattern-hole-before-primitive-value-pattern-warnings` として警告にしてよい．

Expression context と pattern-function signature の value-flow scheme は，宣言的な
利用を二段階に分ける．最初に量化 capability を binder-local な capability variable
へだけ写し，その結果に量化 target binder だけを support とする構造的な target
substitution を順に適用する．この `ValueFlowInst` relation 自体は binder の像の
相異性や ambient freshness を要求しない．Algorithm W はこの relation を強化した witness として，
両 sort の binder へ互いに異なる fresh variable を signature と context の自由変数に
対して割り当てる．
別 scheme の局所 binder 名はこの ambient scope に含めない．利用側の consumer
demand に合わせて value producer の capability を構造化する instance は作れない．
一方，data constructor，pattern constructor，primitive operation の `Inst` は通常の
binder-supported な二 sort structural instance であり，この variable-only 条件の
対象ではない．
二段階は一つの global paired substitution へ潰さず，capability binder-local な
variable mapping の後へ target specialization を順に適用する．従って，後段が挿入した
自由 capability と同じ
番号の量化 binder があっても捕捉しない．型付け導出の後続輸送も，producer の
capability に対する variable-only mapping と target-only specialization に制限する．
この宣言的 post は単射性，像の相異性，ambient freshness を要求しない．一般の
`RestrictedPost.Chain` から忘却して得ることもできるが，公開再構成が使う target-only
suffix の capability 成分は恒等写像なので，terminal validator は `VariablePost` を
直接構成する．
`let` の輸送では，内側の generalization binder を target ambient の外へ局所的に
freshen してから導出を再構成する．これにより，外側の instance が導入した自由変数と
数値 identifier が一致しても捕捉されない．この freshening は導出される補題であり，
source typing や scheme 等式を追加前提にしない．

### Inference

二種 substitution を持つ executable Algorithm W が expression，pattern，slot，
matcher literal を検査する．各 fresh value instance の producer variable を
`protectedCaps` に記録し，全 solver step がそれらを固定することを実行時にも証明上も
監査する．matcher inference は coverage／exhaustiveness checker を必ず実行する．
Pattern constructor の未観測位置は fresh capability で埋め，literal 全体の prevailing
substitution が確定してから raw hole dual を一度だけ解決する．その後，全 clause の
core order，evidence，`PPatCapsAt` check を最終 capability に対して再計算する．
再計算時の `projectClauseSignature` による closed field-head validation は result type
variable の有無と独立であり，closed structured field の observable capability-head
mismatch も fail closed にする．Generic projection と `CapCompatible` の挙動は変えない．
user pattern constructor の子 pattern が別々の fresh consumer capability を持つために
result-variable の共有構造がまだ見えない場合は，一つの共有 result-variable skeleton を
作り，constructor の各 field type へ展開した demand（例えば `cons` なら
`kappa` と `List kappa`）に子の consumer capability だけを整合させる．最終 zonk 後に
exact projection を再実行し，terminal validator でも最終的な `CapCompatible` を再検査する．
これは pattern consumer 間の制約解決であり，value producer capability を consumer
demand から構造化する seed ではない．protected producer variable は従来どおり固定する．
共有 result variable に到達する field の内部では，到達しない observable subposition を
`Any` に canonicalize して field 全体を整合させる保守的な fallback である．その位置だけを
無視する partial/path-wise alignment と W の completeness は主張しない．
再構成では生成時の raw provenance と，substitution 適用後の実際の index で構造を追う
terminal derivation を分ける．nested child の raw index と親の raw field index が
構文的に同一であることは仮定しない．

[`TypePM/PatternCtorCapabilityRegression.lean`](TypePM/PatternCtorCapabilityRegression.lean)
は，独立な二つの child consumer に対して旧 exact projection が失敗すること，fallback
後にはそれらが同じ fresh `kappa` と `List kappa` に zonk され，exact compatibility が
成功することを直接固定する．同じ回帰は protected-producer ledger が不変であり，全 solver
delta が protected producer を固定することも検査する．さらに target 側は整合するが
capability の rigid head が衝突する pctor を `inferRaw` と公開 `infer` が拒否し，capability
だけを整合させた control twin が公開 `infer` と `infer_success_sound` を通ることを対で固定する．
pattern-function instantiation が実際に ledger へ登録した protected variable を `cons` の
tail child に置く負例では，legacy symmetric unifier が作れる structural delta を
cut-local origin solver が `renameOnly` policy により拒否する
ことを，直接 solver と raw/public inference の両方で検査する．

公開 entry point `infer` は，停止する二 sort W 走査 `inferRaw` の結果に
有限な terminal validator を適用する．validator は成功 trace の supply に基づく
binder-local instance，complete public cut での alignment と capability-variable post，
terminal context までの instance 合成，
generalization，coverage evidence を検査し，再構成に必要な `WBridgeWF` を構成する．
solver replay 自体は cross-sort-aware な `Subst.seq` の逐次合成から無条件に導く．
公開 soundness の経路では，生成時の `FreshInstAt` を後続 solver cut ごとに輸送せず，
終端の binder-local `ValueFlowInst`／`Inst` を有限 checker で直接構成する．
その条件に `HasTy` 自体や同型の導出を oracle として含めない．
`infer signature context expression = some result` ならば，`infer_success_sound` が
prevailing substitution で解決した context と結果型に対する concrete declarative
`HasTy` を与える．`InferenceInputWF` は意図する frozen Egison core 入力の静的境界を
別途記述するが，fail-closed な validator により soundness 定理の追加前提にはならない．
呼び出し側が bridge 証明書を渡す必要もない．
後段 post の target component は前段 target range に後段 capability action も適用するため，
二 sort の componentwise 合成や誤った可換性は仮定しない．
terminal validator が raw 成功を棄却する場合はあるため，completeness や full
principal-type theorem は主張しない．

### Principal core elaboration boundary

surface の `HasTy` は動的安全性の境界として維持しつつ，暗黙 coercion を明示化する
elaboration 層を追加した．[`TypePM/Elaboration.lean`](TypePM/Elaboration.lean) の
`SynthHead` は root の非 coercion 規則，`CoercionPlan` はその外側の coercion spine，
`CheckHead` は両者の合成を表す．`HasTy.factorHead` と `checkHead_iff_surface` により，
任意の surface typing がこの形へ分解でき，明示的 plan の replay が元の `HasTy` を
復元することを証明している．ただし `SynthHead` の再帰 premise はまだ `HasTy` であり，
これは **root factorization** であって再帰的な principal-core theorem ではない．

[`TypePM/CoreTyping.lean`](TypePM/CoreTyping.lean) は，既存の derivation-structured な
`Prop` 証明書 `Reconstruction.ExprDeriv` を `CoreTyping` として公開し，公開 `infer` の成功から
推論が選んだ coercion constructor に沿う oracle-free な core evidence が得られ，その
erase が surface soundness を与えることを固定する．Lean の proof irrelevance により，これは
観測可能な elaboration data ではなく，実行時に返す core AST でもない．`CoreSynthHead` は
再帰 premise をすべて reconstruction evidence に保った非 coercion head，`CoreCheck` はそれと
明示的 `CoercionPlan` の合成であり，`coreCheck_iff_coreTyping` が既存 core certificate との同値を
与える．公開 inference の成功もこの factorization を構成する．
[`TypePM/CanonicalCoercion.lean`](TypePM/CanonicalCoercion.lean) はこの `Prop` 値の
`CoercionPlan` とは別に，型の頭を変える3つの observable primitive step，非空 spine，identity を含む `NormalPlan` を
観測可能な `Type` 値の候補 normal-plan syntax として定義する．これは一般の `trans` を持たず，
product matcher から slot への二段経路を `productMatcher; matcherToSlot` と固定する．product of
slots から一致する aggregate slot へは `slotTuple` 一段である．surface の slot-to-slot check は
capability／target の決定的 unifier と後置換の後で両端が等しいことを証明し，`NormalPlan.refl` へ吸収する．
全 `Step`／`Spine` が端点を変えることと，同じ端点の `NormalPlan` は `refl` だけであることも
証明済みである．空 product の `slotTuple` は constructor 側で禁止し，matcher-product precedence
を syntax にも反映する．既存 surface plan／`HasTy` への replay soundness に加え，`NormalPlan.comp` と
`CoercionPlan.normalizable` により任意の外側 plan が `NormalPlan` を持つことも証明する．空 product は
matcher-first の二段経路へ正規化される．ただし `CoercionPlan : Prop` から `NormalPlan : Type` の値を
計算で取り出せないため，結果は `Nonempty` に包まれる．observable rule 列は同じ端点から一意に
決まることも証明済みである．一方，raw certificate を含む plan
inhabitant 自体の一意性，および公開推論が observable plan data を直接返すことは未証明である．

product-of-matchers から product matcher への規則は
tuple literal 専用ではなく unary な `COERCE-PRODUCT-MATCHER` とした．このため coercion は
`let` の束縛時ではなく変数利用位置にも挿入できる．
`DDCheck` が固定する cut と同様に，現行 `checkExprFuel` は式を期待型なしで先に synthesize し，
その出力 state の prevailing substitution を expected 型へ適用してから head を観測する．
`expectedCoercionSource` はその head が matcher／slot を要求するときだけ，raw synthesized type が
product-of-matchers なら product-matcher lift，slot が要求され raw type が product-of-slots
なら slot-tuple lift という branch を決定的に選び，`alignExprResultAtExpected` がその後の
type equality または slot alignment を行う．branch 選択は alignment より前に確定し，選んだ
branch の solve が失敗しても別 branch へ切り替えない．空 product は両 recognizer に一致するため，
coherence policy として product-matcher branch を先に選ぶ．これは selector の決定性であって，
surface coercion 全体の一意性をまだ意味しない．
`checkExprFuel` と通常の関数適用はこの非再帰 helper を共有する．関数適用は function を推論し，
fresh domain／codomain へ整合してから argument を domain に対して check するため，ordinary
application の引数位置でも product matcher／matcher-to-slot／slot-tuple coercion を挿入できる．
terminal reconstruction は同じ選択から `ExprDeriv.coerceProductMatcher` または
`ExprDeriv.coerceSlotTuple` を構成し，solver trace に型付け oracle を追加しない．現段階の
selector は `S τraw` ではなく raw `τraw` の頭を検査するので，raw metavariable が prevailing
substitution 後に初めて product-of-matchers または product-of-slots になる場合（component
metavariable が初めて matcher／slot になる場合を含む）は completeness の今後の課題として残る．
段階 3 の `RawSourceVisible` はこの実装上の死角だけを隔離し，expected head による demand の
可否とは分けて扱う．

[`TypePM/CapabilityOrigin.lean`](TypePM/CapabilityOrigin.lean) は capability metavariable を
`rigid`，`renameOnly`，`structuralFlexible` に分ける有限 ledger と，ledger に対する admissible
paired post を定義する．identity と cross-sort-aware な `Subst.seq` による合成閉性，変数単位／
ledger 全体の freeze，freeze 後に既存 `VariablePost` 境界へ入る bridge を証明している．さらに
`PhasedPost` は局所 structural post と frozen residual post を分離し，後者だけを既存
`VariablePost` へ接続する．現段階の `AdmissiblePost` が制約するのは capability component だけで，
target component は意図的に制約していない．これは
constructor／primitive の局所 structural instantiation と既存 producer の非強化を区別する
代数的基礎である．W の `InferState.capabilityOrigins` はこの ledger を solver policy として保持し，
一般 fresh capability と constructor／primitive image を `structuralFlexible`，context scheme／
pattern-function image と finalized matcher の visible producer を `renameOnly` と記録する．
`capEq`／`targetEq` acceptance は cut-local ledger に従い，legacy `protectedCaps` は one-way
`producerToSlot` と terminal audit の bridge にだけ残る．この producer-freeze 用 ledger は
`DDTyping` の coercion demand に別証人を要求する仕組みではない．unifier の origin-aware orientation は
[`TypePM/PairedUnification.lean`](TypePM/PairedUnification.lean) の kernel slice として
機械化済みで，W の各 equality solve は ledger snapshot を証明書へ保存し，constructor／primitive
完了時には raw binder ではなく局所 solve 後に外へ生存する prevailing image の leaf を
freeze する export event を記録する．これにより producer guard の freeze ギャップ
（`packProgram`）は解消した．
`nestedCapProgram` について提示した demand-free coercion を使う wide 導出を受理するために，
推論器の拒否を変えるものではない．

`CoreTyping` 証明書の非 coercion head 分解と，外側 plan の `NormalPlan` への論理的 normalization
completeness は得られた．canonical core judgment への強化に残る項目（critical pair の解消，
canonical boundary 下の plan uniqueness，cut-indexed evidence など）はロードマップ節に集約する．

現行 `TerminalPatternResolution` の leaf は freshness 用 `rawContext` と `actualContext` を
独立に選べるため，`HasTy` 全体には algorithmic provenance を持たない導出も含まれる．
[`TypePM/CoherentSurface.lean`](TypePM/CoherentSurface.lean) は pattern-local な coherent 境界を
与える：各 terminal pattern leaf の actual context を definitionally
`rawContext.applySubst prevailing` に固定する indices-only な
`CoherentTerminalPatternResolution(s)`／`CoherentResolvedPatternTy`，一つの raw
`Context`／`PatternCtx` を全 child で共有し raw `MonoCtx` だけを binder 導入順に thread する
強い `ThreadedPatternResolution(s)`，および surface への forgetful map と reconstruction
bridge である．`PatternResolutionDeriv(s)` も同じ raw context と raw binding thread を保持し，
W の pattern reconstruction motive がこれを直接生成する．その `pval` は再帰的な `ExprDeriv` を
要求し，arm と clause も reconstruction family に閉じているため，公開 inference が返す
`CoreTyping` は全構文部分で surface typing oracle へ戻らない．

[`TypePM/CoherentTyping.lean`](TypePM/CoherentTyping.lean) はこれを coherent surface typing として
公開する：`CoreTyping` と同じ前例に従い，`Coherent.CoherentExpr := ExprDeriv` ほか 10 family を
定義的 abbreviation とし（鏡写しの独立 mirror は維持しない），surface への忘却
`CoherentExpr.toHasTy` と推論成功から coherent typing を得る `infer_success_coherent` を持つ．
product lift 構成子は raw-source provenance 添字を certificate 本体に持ち，W の reconstruction
motive（`expectedCoercionSource_deriv`）は selector が実際に頭を検査した raw type と terminal
substitution を faithful に注入する（恒等 witness も常に取れるため判断は制限されない）．
coherence が制限するのは pattern の provenance だけなので，`matchAll` と matcher literal を
含まない **match-free 断片では任意の surface typing が coherent** であり
（`coherent_of_matchFree`），その系として Damas–Milner 断片のすべての宣言的型付けは埋め込みを
経て coherent judgment に入る（`dm_coherent`）．これらを algorithmic completeness や
principality とは呼ばない．

### Runtime safety

runtime matcher value は，生成元の actual clause list と現在の clause cursor を別々に
保持する．suffix cursor は一つの atom dispatch の内部だけで使い，公開 state では
値・captured environment・tree・stack 全体に `Pristine` を要求する．`ValueTy` は
intrinsic capability，target，captured environment，source matcher derivation，coverage
を保持する．matching state の型付けは atom ごとの
prevailing substitution，pattern-function node の隔離された parameter context，
残余 actual argument，内部 stack を追跡する．

runtime の `CapabilityDemand` は，raw `DemandMatches` または検査済み matcher-to-slot
certificate から得られる，正規化済み endpoint compatibility の sound な忘却である．raw consumer
構文や一つの substitution による共有相関そのものは保持しない．同じ consumer variable の二度目を
wildcard として扱わない strict check は忘却前の `DemandMatches`／raw certificate が行い，
`CapabilityDemand` から exact raw origin を逆に復元する converse は主張しない．

Ordered dispatch は失敗済み clause prefix を `DispatchTrace` で追跡する．Frozen
signature の pattern-constructor capability 一意性と coverage-index coherence により，
structured pattern が先行する対応 clause をすべて飛ばして bare-hole catch-all へ到達する
不正な branch を排除する．

`CoreSafety` は次を個別に取り出せる形でまとめ，`core_safety` が concrete
judgment 上の証明を与える．各 preservation／reachability／search 結論は，対象の
concrete derivation に付随する `*RuntimeSigAgrees` mirror と，source context に対する
`RuntimeSigAgrees` を引数に取る．したがって任意の runtime signature を無条件に source
signature と同一視する主張ではない．
[`TypePM/RuntimeAgreementBridge.lean`](TypePM/RuntimeAgreementBridge.lean) は，
`∀ context, RuntimeSigAgrees signature context SF` という一つの global agreement
から，任意の concrete `Eval`／`PPM`／`MAtom`／`Step`／`Search`／`Reaches` 導出に対応する
mirror を，その導出の構造に沿って構成する．従って mirror family は実行導出を外部から
与える oracle ではない．

1. pristine な typed environment からの expression evaluation の preservation
2. matching state 一段の preservation
3. matching state の local progress
4. 到達可能な全 state の型付け
5. 成功した terminal match substitution の型付け
6. 上の終端性質としての matcher consistency

[`TypePM/SignatureChecker.lean`](TypePM/SignatureChecker.lean) は，動的定理の唯一の
global 条件である `FrozenSigWF` を，有限の実行可能検査 `frozenSigWFCheck` の成功から
構成する（`frozenSigWFCheck_sound`）．検査は保守的で fail closed である．canonical な
`nil`／`cons` 宣言が `ListSigWF` を witness し，data constructor は構文的 data root と
binder 被覆を検査して（instantiation の一意性は substitution-agreement の逆補題から
従う），pattern constructor は単一パラメータ collection family（`nil`／`cons`／`join` 型）
に限定して capability projection の明示的 inversion から uniqueness と index coherence を
導出する．各 pattern constructor には `constructorsByFormer` の対応 row と
`(name, arity)` membership を必須とし，row 欠落は fail closed で拒否する．この row は
保守的 coverage index であり，追加 entry は許すが coverage obligation を強めるだけである．primitive は
canonical scheme との一致を検査して delta preservation を
operation ごと（`append`，`splits`）に一度証明する．関数値 field
`armExhaustive = basicArmExhaustive` だけは signature 構成時の定義等式として受け取る．
`DynamicSafetyRegression`／`PatternFunctionSafetyRegression` の `signature_wf` は
この checker の一回の実行（`by decide`）で立ち，`RecursiveExamples` の
`listSignature`／`multisetSignature` には非空 pattern-constructor 表に対する初の
非空虚な `FrozenSigWF`（`listSignature_wf`／`multisetSignature_wf`）が立つ．対応 row を
削った List signature は checker が拒否する．

[`TypePM/DamasMilner.lean`](TypePM/DamasMilner.lean) は，pattern を含まない
`λ`/`let`/direct-self `fix` 断片について，独立に定義した一 sort の Damas–Milner 体系
`DM.HasTy` を与える．その再帰規則は core と同じ `self ≠ argument` と
`DirectSelf.Holds self body` を要求し，**この制限体系のすべての導出が閉じた frozen
signature 上の二 sort 宣言体系へ埋め込まれる**こと（`DM.HasTy.emb`）を証明する．
埋め込みの下で capability sort は不活性で
ある：capability binder は空，capability substitution は自明に作用し（`STy.emb_fcv` = 空），
`let` の一般化は二 sort generalizer と可換（`generalize_emb`）．多相 `let` の証人
`let id = λx.x in (id id) 1` の DM 導出とその埋め込みも固定する．受理の宣言側の準備として，
DM の全型付けが coherent judgment へ入ること（`Coherent.dm_coherent`）は
`CoherentTyping.lean` で証明済みである．`DMTerminalAcceptance.lean` は上の多相 `let` 証人に
対する raw 成功，terminal bridge check，公開受理を固定する．逆方向（conservativity）と
一般の algorithmic acceptance（公開 `infer` が全 DM program を受理すること）はまだ主張しない．

[`TypePM/PrincipalityCounterexample.lean`](TypePM/PrincipalityCounterexample.lean) は，
宣言体系のprincipalityが**そのままの形では偽**であることを機械化された反例で確定する．
閉じた式 `(something, something)` は T-TUPLE でmatcherのproduct型に，
COERCE-PRODUCT-MATCHER でproduct matcher型に型付き，両者の頭構成子（`prod` と `matcher`）は
異なる．tuple式の導出可能型の頭は `prod`/`matcher`/`slot` に限られ（`tuple_ty_head`），
paired substitutionは頭を保存するため，両方をinstanceに持つ導出可能型は存在しない
（`no_principal_type`）．失敗の原因はcoercionの重なりそのもの（使えるproduct matcherの代価）で
あり，capability evidenceとは独立である．制限されたprincipality文はこの重なりを除外する必要が
ある．coercionを持たない DamasMilner 断片は影響を受けない．

[`TypePM/ElaborationRegression.lean`](TypePM/ElaborationRegression.lean) は，この反例の
product 型を canonical な root synthesis として固定し，product matcher view を明示的
`CoercionPlan` として replay する．さらに product 型のまま `let` を越えた変数へ unary lift を
利用位置で適用できることを宣言的に証明する．
[`TypePM/CertifiedInferenceRegression.lean`](TypePM/CertifiedInferenceRegression.lean) は，
executable checker の selector が matcher 期待時に product matcher を，slot 期待時にも
matcher-to-slot の入力となる同じ product matcher branch を決定的に選ぶことに加え，product-of-slots の
slot-tuple 選択と，三種類の coercion を必要とする domain-directed application が公開 inference
で成功することを `#guard` で固定する．各結果が `Int` で，terminal substitution 後の alignment
端点が期待どおりであることも検査し，component ごとの matcher-to-slot を暗黙に挿入する負例は拒否する．
[`TypePM/ApplicationCoercionRegression.lean`](TypePM/ApplicationCoercionRegression.lean) は，対応する
三つの application について，product-matcher，matcher-to-slot，slot-tuple を明示的に使う
surface `HasTy` 導出を与える．さらに空 product の競合を matcher-first の二段 `NormalPlan` へ
固定する．

正当な match failure（後続 state が空）は stuck ではない．値パターン式が原子入力の
context で型付くことを表す局所 `CaptureAdm` は，clause の `PPatCoreOrder`，PP typing，
user-pattern typing，成功した `PPM` から `captureAdm_of_coreOrder` が導く．したがって
`OperationalCaptureAdm` のような caller-supplied premise は公開 safety surface にない．
一段の dispatch が必要とする局所評価・decode 結果だけを `StepReady` として progress に
明示し，一般の program termination は仮定しない．この local progress は古典的な
「型付けだけから一段を発見する」定理ではなく，規則ごとの局所的な実行証拠から concrete
`Step` を組み立てる境界である．

[`TypePM/DynamicSafetyRegression.lean`](TypePM/DynamicSafetyRegression.lean) は，
`SF = []` の concrete frozen signature と実際の `matchAll` 実行について，
`FrozenSigWF`，global runtime agreement，評価・primitive-pattern matching・atom reduction・
step・search・reachability と各 mirror を同時に構成し，`CoreSafety.evalPreservation` を
実際に適用する end-to-end 回帰である．公開 W の結果と保存後の runtime value はともに
`List Int` へ固定する．

[`TypePM/DynamicCaptureRegression.lean`](TypePM/DynamicCaptureRegression.lean) は，合法な
`#$captured` clause について `PPM.pval`，`MAtom.matcher`，`Step`，`Search`，`Reaches`
を具体的に接続する．`AtomTy.mk` から構成した初期 state へ
`CoreSafety.stepPreservation` を適用するため，`captureAdm_of_coreOrder` の value-pattern
分岐が実際の matcher reduction で消費される．結果型は `List Int` に固定する．

[`TypePM/DynamicDispatchRegression.lean`](TypePM/DynamicDispatchRegression.lean) は，具体的な
`cons $x $rest` の実行を，先行 `nil` clause の primitive-pattern mismatch，`cons` clause
先頭 arm の data-pattern mismatch，次 arm の成功へ順に通す．単一の kernel 導出内で
`MAtom.matcherPPFail`，`MAtom.matcherDPFail`，二 child の `PPM.ctor`，`MAtom.matcher` を
発火させ，同じ失敗証拠から `DispatchTrace.nextClause`／`nextArm` も構成する．生成された
`x`／`rest` atom を二段で束縛し，`Step`，`Search`，`Reaches`，`matchAll` の具体評価まで
terminal に閉じる．さらに同じ三段の private cursor 遷移を，非再帰 `Pair α` family の
型付き fixture でも発火させる．後者は `frozenSigWFCheck` と公開 `infer` を通り，非空な
`[(rest, 2), (x, 1)]` へ到達する同一実行に `evalPreservation`，`stepPreservation`，
reachability，search substitution typing，matcher consistency を適用する．

[`TypePM/PatternFunctionSafetyRegression.lean`](TypePM/PatternFunctionSafetyRegression.lean)
は，closed nullary pattern function `unit := ptuple []` を source と runtime の非空
signature に置き，`∀ context, RuntimeSigAgrees` からこの実行に必要な各 mirror を構成する．
非空な `RuntimeSigAgrees.sourceLookup` も step preservation と local progress で実際に消費する．実行は
`papp` から `mnode` へ入り，inner atom reduction と completed-node removal を経て terminal
state に到達する．この一例で `CoreSafety` の六フィールドをすべて具体的に適用し，search
と matcher consistency には実際の `[] ∈ [[]]` を渡す．公開 W の結果も `List Int` に固定する．
加えて非 nullary の `pass(parameter : Unit) := embed parameter` について，context ごとに
fresh な binder を選んだ局所 scheme と固定 lookup scheme の value-flow 外延同値を構成する．これにより
`∀ context, RuntimeSigAgrees` と実際の `patfunEnter` step の `of_global` mirror が，
引数を持つ定義でも成立することを固定する．

### Recursive matcher regressions

[`TypePM/RecursiveExamples.lean`](TypePM/RecursiveExamples.lean) は，外部の
型付け済み matcher 定数ではなく，実際の `fix self m. matcher ...` 本体を検査する．

- list: direct-self source typing と W の成功
- paper-complete multiset interface: list とは別の self binder／clause list に対する
  source typing と W の成功
- simplified multiset: `join` 一般節不足により `coverageCheck = false`，
  `¬ CoverageOK`，raw W，公開 W のすべてが失敗
- generic `listSignature` と `fix` で構成した `listMatcher` を slot に適用し，
  `matchAll` の `cons $x $rest` が束縛した `x` と `rest` の両方を body で使う旗艦例が
  公開 `infer` を通過する．結果型を concrete literal に固定し，成功等式から
  `infer_success_sound` により `HasTy` を再構成する．これは静的 inference 回帰であり，
  再帰 matcher の動的実行は主張しない
- 量化 binder と target specialization 内の自由 capability が同じ番号でも，ordered
  binder-local instance と let generalization が成功

[`TypePM/ProducerStrengtheningRegression.lean`](TypePM/ProducerStrengtheningRegression.lean)
は，同一の structured consumer に対して，fresh capability variable を公開する
polymorphic value producer を公開 `infer` が拒否することと，要求済みの concrete
producer へ置き換えた control twin が成功することを対で検査する．成功側は結果型を
`Int` に固定し，`infer_success_sound` から concrete `HasTy` も構成する．

## 明示的な境界

次はこの formal core の主張に含めない．

- 広い `HasTy` を前提にした Algorithm W の completeness
  （`WideAnnotationFree` は機械化反例により恒久的に反証済み）
- `DDTyping`，`DDSynth`，`DDCheck` の Lean 定義，および `RawSourceVisible`／
  `FreezeCompatible` を仮定する中間受理定理と，それらを外した最終受理定理
  （いずれもロードマップ上の未実装項目）
- `nestedCapProgram` の全 `HasTy` 導出が demand-free coercion に依存するという inversion
  （現在の回帰が示すのは該当する一つの導出と推論拒否）
- 反証済みの無制限 principality
- alias，mutual recursion，transform，高階 origin を含む一般 producer-flow 解析
- raw declaration から frozen signature を構築する validator
- full Egison の warning mode の実装，module/import persistence，標準ライブラリ移行
- CAS の target-indexed pattern view
- 一般の評価停止性

## モジュール

| 層 | 主なファイル | 内容 |
|---|---|---|
| 型代数 | `Syntax`, `Substitution`, `Relation`, `CapMatch`, `Unification` | 二 sort，代入，自然性，one-way match，solver |
| capability | `Observability`, `Shape`, `Projection`, `Canonical`, `CapTarget`, `Recursion` | 観測可能性，evidence，projection，direct-self shape fold |
| source | `Term`, `ClauseEvidence`, `Source`, `SourceSubstitution`, `SourceGeneralization`, `SourceMetatheory`, `PatternFunction` | concrete syntax と宣言的型付け，coverage，安全な一般化と輸送 |
| elaboration | `Elaboration`, `CoreTyping`, `CanonicalCoercion`, `CapabilityOrigin`, `PairedUnification`, `CoherentSurface`, `CoherentTyping` | surface root factorization，raw-threaded recursive core head factorization，outer-plan normalization，origin-sensitive phased post，origin-aware paired solver kernel，pattern-local coherent surface 境界，mutual coherent surface typing，反証済み wide 注釈不要性境界 |
| runtime | `Semantics`, `Dynamic`, `Preservation`, `DynamicMetatheory`, `Reachability`, `Safety`, `RuntimeAgreementBridge` | 評価・matching semantics，state invariant，preservation/progress/safety，global agreement からの derivation-local mirror 構成 |
| W | `InferenceBase`, `Inference`, `InferenceLedgerAdmissibility`, `InferenceLocalFactorization`, `InferenceTraversalLocalFactorization`, `InferenceTraceFactorization`, `InferenceFreezeTransport`, `InferenceAdmissibleTrace`, `InferenceTraversalAdmissibleTrace`, `InferenceInput`, `InferenceHistory`, `InferenceStateExtension`, `InferenceTraversalStateExtension`, `InferenceRunInvariants`, `Reconstruction`, `BridgeChecks`, `CertifiedInference`, `InferenceRegression`, `Soundness` | raw W 走査，origin-admissible local solve／全 traversal の局所因子化証明書／scoped trace 合成／selective freeze 輸送／全 traversal 不変量の統合，入力整形性，append-only history，全 traversal の supply／producer state extension，terminal validation，declarative reconstruction，公開 inference soundness，concrete safety composition |
| 回帰 | `ClauseEvidenceExamples`, `GeneralizationRegression`, `CertifiedInferenceRegression`, `AcceptanceGapRegression`, `DMTerminalAcceptance`, `ApplicationCoercionRegression`, `RecursiveExamples`, `ProducerStrengtheningRegression`, `PatternCtorCapabilityRegression`, `DynamicSafetyRegression`, `DynamicCaptureRegression`, `DynamicDispatchRegression`, `PatternFunctionSafetyRegression` | evidence，source-level binder collision，domain-directed coercion，公開 inference soundness，DM 多相 let の terminal 受理，recursive matcher の旗艦例と正負例，producer non-strengthening と PAT-CON の public control twin，空／非空 runtime signature，capture，型付き ordered dispatch を含む動的安全性の具体適用 |

各ファイルは `TypePM/` 以下にある．

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
使用しない．主定理，一般補題，および `#guard`／kernel reduction で評価する小さな回帰は kernel が
検査する．一部の大きな具体的実行回帰で用いる `native_decide` だけは Lean の native compiler を
追加で信頼するため，この二層を区別する．
