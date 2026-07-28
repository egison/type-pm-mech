# type-pm-mech — type-pm-paper の機械化証明

[`../type-pm-paper/`](../type-pm-paper/)(λ_PM:非自由データ型上のアドホック多相・非線形・バックトラック付きパターンマッチの計算体系と型システム)のメタ理論を Lean 4 で機械化するプロジェクト。定義(構文・操作的意味論・型システム・整型マッチング状態)は完成してビルドが通り、論文 §2/付録 A.1 の実測例は fuel 付きインタプリタ上で `rfl` により機械検証済み(適切性定理を経て関係的意味論 ⇓ の導出の存在まで保証)。メタ理論は論文の補題・定理と 1 対 1 対応で配置し、**Thm 5.1(マッチャー多相性)・Lem 5.2(one-way 一意性+アルゴリズムの健全性/完全性)・Thm 5.7(マッチャー整合性定理、(b) を仮定した合成)・インタプリタ適切性・Search↔Reaches 対応は証明済み**。**Thm 5.1・Lem 5.2(完全)・Lem 5.4(PPP 型保存)・Lem C.2(スロット不変量)・Thm 5.7・適切性・Search↔Reaches に加え、Progress の前提となる正準形補題層も証明済み**。残る `sorry` は **3**(Thm 5.6(a)(b)・Lem 5.5)。

- 証明支援系: **Lean 4**(`lean-toolchain` 固定、v4.31.0 = type-tensor-mech と同一)。外部依存なし(Mathlib 不使用)。
- ビルド: `lake build`(`~/.elan/bin` に elan/lake がある前提)。
- `sorry` は「論文に証明があり、未機械化」の印。新しい公理(`axiom`)は使わない方針。

## ファイル構成と論文対応

| ファイル | 内容 | 論文 |
|---|---|---|
| `TypePM/Syntax.lean` | 型 τ・スキーム σ・式 e・パターン p・pp・dp・値 v・原子/木/スタック/状態・Σ_D/Σ_P/Σ_F・binds/出現関数 | §3.1 Fig 1, §3.2 |
| `TypePM/TypeRel.lean` | 型代入・ftv・単一化可能性 ~・one-way instance ⊑・改名・スキーム/シグネチャのインスタンス化・**one-way 一意性(証明済)** | §4 Notation, **Lem 5.2** |
| `TypePM/Semantics.lean` | 構造的等価 ≡・pdMatch・PPM・6 項関係 MAtom・状態簡約 Step・探索 Search・評価 Eval(5 判断の相互帰納) | §3.3 Fig 2–3 |
| `TypePM/Exec.lean` | fuel 付き実行可能インタプリタ(DFS)+ `matchOneWay`(⊑ の線形時間アルゴリズム) | §3.3, Lem 5.2 |
| `TypePM/Typing.lean` | PP/PD 判定・双対パターン判定 PatTy・式判定 HasTy(T-MATCHALL/T-MATCHER/T-SOME/3 コアーション)・整合性 Def 4.2・PATFUN-DEF | §4 Fig 4, 付録 A Fig 5, Def 4.1/4.2 |
| `TypePM/WellTyped.lean` | 値の型付け v : τ・型付き代入・WT-ATOM/WT-MNODE/WT-STACK/WT-STATE | §5.3, 付録 C Fig 6 |
| `TypePM/Metatheory/Polymorphism.lean` | **マッチャー多相性(証明済:構成子合成そのもの)** | **Thm 5.1** |
| `TypePM/Metatheory/Preservation.lean` | **PPP 型保存(証明済:pp 構造帰納+リスト版相互、(a)-oracle 仮定つき)・matcher-value slot invariant(証明済:値レベル slot 規則の反転)**・型安全性 (a)(b)(sorry) | **Lem 5.4, Lem C.2**, Thm 5.6, 付録 C |
| `TypePM/Metatheory/Canonical.lean` | **正準形補題層(証明済)**:VShape⊇ValueTy・積型正準形・改名/one-way の形状保存・「構造前提が something/積マッチャーを構成子パターンで却下」 | 付録 C.2 の核 |
| `TypePM/Metatheory/Progress.lean` | **Progress 前提層(証明済)**:`ListSigOK`/`canonical_list`・`pdMatch_typed`・節/アーム型付けの member 補題・`mapM_eq_some`/`decomposeME_tuple`・環境型付けグルー(`envTyped_of_bindings`/`envTyped_append`/`envTyped_of_matcherV`/`inst_mono`)+ Lem 5.5 本体(sorry) | Lem 5.5, 付録 C.2 |
| `TypePM/Metatheory/Safety.lean` | Reaches((b) の反復装置)・**到達保存・終端代入型付け・マッチャー整合性定理(いずれも (b) を仮定して証明済)・Search↔Reaches 対応(結合再帰子 `Search.rec` で証明済)** | **Thm 5.7**, 付録 C.4 |
| `TypePM/Metatheory/Principal.lean` | **matchOneWay の健全性/完全性(証明済:Lem 5.2 の計算可能性部分が完結)**+主型性スタブ(Algorithm W は Stage 2) | Thm 5.3, Lem D.1–D.3, 付録 B/D |
| `TypePM/Metatheory/Adequacy.lean` | **インタプリタの健全性(証明済:fuel の相互帰納 11 定理)** | — |
| `TypePM/Examples.lean` | §2 の実測例(list 決定的/multiset 非決定的/pair パターン関数/unorderedPair)+ 双対判定・双対検査・T-MATCHALL の導出例。**全て証明済(rfl / 明示導出)** | §2.1, §2.4, 付録 A.1, §4.2/4.4 |

## 機械化上の設計判断(論文からの意図的な差分はここに集約)

1. **変数は文字列名、de Bruijn 化なし**。意味論が環境ベース big-step(項への代入が存在しない)ため、名前で忠実に写せる。型変数は `Nat` 名。
2. **`Pattern τ` は型ではなく判断形式**。型文法に載るのは `Matcher`/`MatcherSlot` のみ(論文でも式が `Pattern` 型を持つことはない)。パターン関数仮引数の双対型 `Pattern (β ▷ τ)` は専用文脈 Φ で持つ。
3. **リストは Σ_D の普通の構成子**(`[]`/`::` は `nil`/`cons`、型は `Ty.data "List" [τ]` の略記 `Ty.listT`)。ユーザ定義型一般を `Ty.data` で扱う。
4. **「fresh 変数」の宣言的読み**:PAT-VAR/PAT-WILD/PAT-VALUE の構造添字は任意の型を許し、PAT-CON/PAT-APP のインスタンス化は「∃ 代入で宣言型に一致」で述べる(W の MGU 選択は主型ステージの関心事)。構成子頭の骨格は PAT-CON の結果インスタンス化で常に強制されるので、双対検査が `something` を構成子パターンで却下する性質は全導出で保たれる。⊑ の向きは論文どおり **θ(τ_p) = τ_m′(マッチャー型は構造添字のインスタンス)**。
5. **matchAll の結果は有限リスト読み**:論文の遅延ストリームの per-element 読み(§3.1 脚注)に対応し、`Search` は SEARCH-DONE/STEP の帰納的関係。
6. **再帰は `Expr.fix`**(論文の「トップレベル定義は再帰的」;`multiset m` の自己参照はこれで書ける。単相再帰)。分解関数本体のライブラリ関数は δ プリミティブ(`append`・連続分割 `splits`)。`match`(複数節)は §3.1 の糖衣なので省略。Bool 値・if は未使用。
7. **Matcher rigidity(§4.6)は宣言的関係では扱わない**(推論アルゴリズムの制限;型安全性の証明義務は WT-ATOM が整合性選言を明示前提に持つ形で自己完結)。Stage 2 の Algorithm W で扱う。
8. **arm exhaustiveness (Def 4.2(1c)) は意味的定式化**(∀ 値 ∃ マッチするアーム)で、値の量化域は浅い形状型付け `VShape`(完全な `ValueTy` と分離して T-MATCHER ↔ 値型付けの循環を切る)。
9. **Progress は停止仮定つき**:MS-MATCHER の premise が式評価 ⇓ を含むため、「簡約列が導出可能」には分解関数の停止(論文 §5 の仮定)が要る。`ms_progress` は大域的停止仮定 `htotal` を引数に持つ。
10. **T-MATCHER の前提はスコーレム化**(`ClauseTy`/`ArmsTy`/`ClausesTy`):kernel の nested inductive 制限(∃ の内側に定義中の型を置けない)のため。
11. **値レベルのコアーション規則**:`ValueTy` に `slotV`/`prodSlot`(COERCE-MATCHER-TO-SLOT / COERCE-SLOT-TUPLE の値対応物)を持つ。スロット型で束縛される λ 引数の環境型付けに必要で、Lem C.2 はその反転として証明される。`prodMatcher` は COERCE-TUPLE-MATCHER の値対応物。
12. **シグネチャ整形性** `CtorSigWF`/`SigPWF`/`SigDWF`(Def 4.1 の暗黙条件:結果型は型構成子の全変数適用、引数型の変数は宣言パラメタ内)。結果型のインスタンス一致から引数型のインスタンス一致を導く `instSig_args_agree` が Lem 5.4 の PP 側・PatTy 側の整列を支える。
13. **`VShape` は積マッチャー・スロット値も覆う**(`matcherTuple`/`slotAny`):arm exhaustiveness の量化域が実際の整型値(`vshape_of_valueTy`)を覆うため。
14. **束縛名の相異を Def 4.2 の正式条件に**(`ConsistentClauses.ppBindNodup`/`armBindNodup`):論文の ⋃ᵢ Δᵢ・⋃ᵢ Γᵢ 記法が前提する直和性の明文化。`pdMatch`/`pdMatchList` は dp 外側・v 内側の入れ子照合(証明の `split` 単純化;挙動不変)。

## 機械化が浮かび上がらせた論文の細部(**2026-07-28 論文へ反映済み**、英日両版)

- **MS-MNODE-STEP の一般化**:論文 Fig 3 の規則は内側スタックの先頭が「原子」の場合のみを書いていたが、パターン関数のネスト適用では内側先頭が MNode になる状態が生じる(f の本体内で g q⃗ が展開された直後)。機械化と論文の双方で規則を任意の内側先頭木に一般化(`Semantics.lean` の `mnodeStep`;論文は Fig 3 + §3.3 + 付録 C.2/C.3 の対応箇所を更新)。
- **WT-MNODE の内側入力文脈**:論文 Fig 6 は内側スタックの型付けを ε から始めていたが、本体内で先に束縛された $ 変数を後続の値パターンが参照するには dom_typed(θ_f) から始める必要がある(WT-STATE の外側の扱いと平行)。機械化と論文の双方で後者を採用(`WellTyped.lean`;論文は Fig 6 + Def 5.3 + キャプションを更新。入れ子 MNode の変数パターン出現の数え方の明確化も同時に反映)。
- **(その 3、論文未反映・要設計判断)PPP-VAL の早期評価**:pp の #$y は対応する p 側 #M の M を**節選択時**に評価するが、M の型付け文脈(PAT-VALUE の Δ スレッディング)は p の左側部分パターンの束縛を含み得る。#$y が第 2 引数位置以降に立ち M が左側束縛を参照すると、束縛前の評価になる。標準ライブラリの全節(#$val はトップ、#$pxs は第 1 位置)は安全側。対処候補:(i) #$ 位置を接頭位置に制限、(ii) 該当位置の値パターン式の型付けを原子入力文脈 Δ₀ に制限、(iii) 評価の遅延。`Preservation.lean` のモジュールドキュメント参照。

## 現状(2026-07-28 第 4 版)

- `lake build` 成功(エラー 0)。`sorry` は **3 宣言** = Thm 5.6(a)(b)(Preservation)・Lem 5.5(Progress)。
- 第 4 版で証明完了(Progress.lean の前提層):
  - **`canonical_list`**(`ListSigOK` の下でリスト型の値は `listOfV` で分解でき要素が型付く)・**`pdMatch_typed`**(dp 束縛の型付け;Lem 5.4 の dp 版、(b) でも使用)
  - **環境型付けグルー**:`applyTS_nil`・`inst_mono`・`tyCtxFind_toCtx`・`envTyped_of_bindings`・`bindings_cover`・`envTyped_append`・`envTyped_of_matcherV` — MS-MATCHER の分解関数評価環境 (ρd ++ ρp ++ ρm) の型付けを組み立てる部品が完備
  - `clausesTy_mem`/`armsTy_mem`・`mapM_eq_some`・`decomposeME_tuple`
- 第 3 版で証明完了:
  - **Lem 5.4(PPP 型保存)**:`ppp_core`/`ppp_list`(pp 構造帰納・リスト版相互)。仮定 = Σ_P 整形性・(a)-oracle・pp 束縛名の相異(⋃Δᵢ 直和の暗黙条件)。取り出された次パターン列の PatTys(Δ スレッディング込み)と値パターン束縛の型付けの両方。
  - **Lem C.2(スロット不変量)**:値レベル slot 規則(`slotV`/`prodSlot`)の反転+`matcherOK_of_valueTy`。結論は論文どおりの選言(単一マッチャー条件 ∨ タプル成分ごとのスロット)。
  - **正準形補題層(Canonical.lean)**:`vshape_of_valueTy`・`canonical_prod`・改名/one-way の形状保存・something/積マッチャーの構成子パターンでの却下・`valueTy_unifiable_prod`。
- 証明済み:
  - `oneWay_unique`(Lem 5.2 一意性)+ `matchOneWay_sound`/`matchOneWay_complete`(Lem 5.2 の計算可能性部分;acc スレッディング不変量 `MOWInv` による相互帰納)
  - `matcher_polymorphism`(Thm 5.1;+2 マッチャー共有系)
  - `reaches_preservation`・`terminal_subst_typed`・`matcher_consistency`(Thm 5.7;Thm 5.6(b) を仮定した合成)
  - **適切性(Adequacy 11 定理)**:`evalF_sound`/`stepF_sound`/`searchF_sound` ほか、fuel の相互構造帰納。実行例 4 本は関係的意味論 ⇓ の導出の存在まで保証(Examples 末尾の系)
  - **`search_mem_reaches`**:相互帰納族の結合再帰子 `Search.rec`(5 motive、他 4 つを自明化)で証明。**Thm 5.6 の「結合導出木の高さ帰納法」を機械化する道具立てが機能することの実証**
  - Examples 全部:実行 4 本(`rfl`)+ 関係的持ち上げ 4 本 + 双対判定導出・双対検査の受理/却下・T-MATCHALL 完全導出
- 適切性証明のために `stepF`/`ppmF` の分岐を意味的ガード(`piHit`/`pappHit`/`ppShapeOK`)へリファクタ(挙動は整型プログラム上不変;`split` を単純化するための実装形)。
- multiset の ++ 節と #$val 節は実行例に不要なので省略(整合性述語の実例化は Stage 1 の項目)。

## ロードマップ

- **Stage 1(コア型安全性、付録 C;残る sorry 3 の解消)**:
  - Lem 5.5(Progress):前提層(Canonical.lean + Progress.lean 上部)は**全て済**。残り = shapeOK からの PPM 全域性(停止仮定つき、pp 構造帰納)・節/アームの先頭一致選択の存在帰納(catch-all の存在から一致節が必ずある)・decodeTuple の形状補題(prodK の場合分け+`canonical_prod`/`canonical_list`)・papp の Σ_F アリティ(`SigFWF.arity`)・組み立て(木の構造帰納、Φ を一般化した状態整型で;WTState の Φ=[] 固定を内側スタック用に一般化)。
  - Thm 5.6(a)(b):`Search.rec` 型の結合再帰子(5 motive)への一括適用。`search_mem_reaches` で同ルートは実証済み。必要な補助:HM 代入・弱化補題(TyCtx 操作)、環境拡張と EnvTyped の整合、MS-MATCHER ケースの θp∘U 追跡(Lem 5.4 は済)。
  - list/multiset 整合性(Def 4.2)の実例検証。
- **Stage 2(主型性、付録 B/D)**:rigidity 付き Robinson 単一化 → Algorithm W(matchAll の Step 1–6・スロット処理 3a/3a′/3b)→ Lem D.1–D.3 → Thm 5.3。
- **Stage 3(拡張)**:loop パターン・型クラス(付録 F の辞書渡し)・値引数つきパターン関数など、論文 §7 の open directions に対応する範囲の検討。
