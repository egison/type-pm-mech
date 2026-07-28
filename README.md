# type-pm-mech — type-pm-paper の機械化証明

[`../type-pm-paper/`](../type-pm-paper/)(λ_PM:非自由データ型上のアドホック多相・非線形・バックトラック付きパターンマッチの計算体系と型システム)のメタ理論を Lean 4 で機械化するプロジェクト。定義(構文・操作的意味論・型システム・整型マッチング状態)は完成してビルドが通り、論文 §2/付録 A.1 の実測例は fuel 付きインタプリタ上で `rfl` により機械検証済み(適切性定理を経て関係的意味論 ⇓ の導出の存在まで保証)。メタ理論は論文の補題・定理と 1 対 1 対応で配置し、**Thm 5.1(マッチャー多相性)・Lem 5.2(one-way 一意性+アルゴリズムの健全性/完全性)・Lem 5.4(PPP 型保存)・Lem C.2(スロット不変量)・Lem 5.5(Matching State Progress)・Thm 5.6(a)(式評価の型付け;oracle 分解)・Thm 5.7(マッチャー整合性定理、(b) を仮定した合成)・インタプリタ適切性・Search↔Reaches 対応は証明済み**。残る `sorry` は **1**(Thm 5.6(b))。

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
| `TypePM/Metatheory/Preservation.lean` | **PPP 型保存(証明済:pp 構造帰納+リスト版相互、(a)-oracle 仮定つき)・matcher-value slot invariant(証明済:oracle 不要の核 `slot_value_inv`+wrapper)** | **Lem 5.4, Lem C.2**, 付録 C |
| `TypePM/Metatheory/TypeSafety.lean` | **Thm 5.6(a)(証明済:`Eval.rec` 5 motive、oracle = (b)・HM 一般化・初期状態整型)**:環境拡張補題群・値レベル強制追随(`valueTy_coerce2/3`)・`mkListV_typed`/`primEval_typed_*`・ctor 強制不可能性+Thm 5.6(b)(sorry) | **Thm 5.6**, §5.4, 付録 C |
| `TypePM/Metatheory/Canonical.lean` | **正準形補題層(証明済)**:VShape⊇ValueTy・積型正準形・改名/one-way の形状保存・「構造前提が something/積マッチャーを構成子パターンで却下」 | 付録 C.2 の核 |
| `TypePM/Metatheory/Progress.lean` | **Lem 5.5(Matching State Progress)証明済**:前提層(`ListSigOK`/`canonical_list`・`pdMatch_typed`・member 補題・環境型付けグルー)+代入合成 `applyTS_comp_pointwise`/`instSig_applyTS`・**VShape 代入安定性 `vshape_applyTS`**・PPM 全域性 `ppm_total`/抽出長 `ppm_length`・改名反転・節/アーム歩き(`clause_walk`/`arms_walk`)・`WTTree.rec` 結合再帰子による本体 | Lem 5.5, 付録 C.2 |
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
15. **値パターンスコープ条件はパターン・マッチャー対の条件 = WT-ATOM の premise**(`VPScoped`):Def 4.2 のマッチャー単独条件にはしない(細部その 3)。捕捉された式は原子入力文脈で型付くことを要求する。
16. **T-SOME/ValueTy.something の添字は裸変数に固定**(`Matcher (.var a)`):設計判断 4 の「fresh の任意インスタンス読み」を**マッチャー側には適用しない**。任意 τ に緩めると `(c p⃗, something, v)`・`((p⃗), something, v)` の行き詰まり原子が WT-ATOM を満たしてしまい Lem 5.5 が反証される(付録 C.2 の「構造前提が裸変数マッチャーを排除」は something の内在型が変数であることに依存)。論文は元々 Fig 4 T-SOME「α fresh」・§5.3「something : Matcher α」でこの通りであり、機械化を論文に合わせて修正した(2026-07-28)。パターン側(PAT-VAR/WILD/VALUE の構造添字任意)は従来どおり。
17. **arm exhaustiveness (Def 4.2(1c)) は代入インスタンス閉包で量化**(`armExh : ∀ U v, VShape SD v (τ.applyTS U) → …`):多相マッチャー(`Matcher [a]` など)を実型で使う site の値は τ 自体の VShape を持たない(VShape は変数型を結論できない)ため、τ 固定の量化では Progress で発火しない。ML 流の Σ_D 網羅性検査はインスタンス一様なので論文の検査と一致する。発火は `vshape_applyTS`(VShape の代入安定性)+単一化子経由(`armExh_instance`)。
18. **Lem 5.5 の oracle 形**:`ms_progress` は停止仮定 `htotal` に加え、`ppp_core` と同じ ∀Γ' 形の (a)-oracle `heval` を取る(分解関数の像がリスト・k 組であることに使用;環境型付けの供給なしで形だけ取り出せるのがこの形の利点)。結合帰納法での oracle 供給(HM 代入補題+vp-scoped 経由の精密化が要る)は Thm 5.6 の課題としてロードマップに記載。
19. **Thm 5.6(a) の oracle 形と let 一般化の rigidity 制限**:`type_safety_a` は `Eval.rec`(5 motive、他判断は自明 motive;matchAll の探索は `search_mem_reaches`+`reaches_preservation` で処理するので Search motive も不要)で証明し、(b) `hb`・HM 一般化補題 `hgen`・matchAll 初期状態整型 `hinit` を oracle に取る。**hgen は宣言的システムの全導出に対しては偽**:bare-hole のみのマッチャー(`Matcher a` でのみ整合)を let で一般化し `Matcher [Int]` にインスタンス化する導出が宣言的には書けてしまい、EnvTyped のスキーム全インスタンス義務が満たせない(実システムは matcher 型引数の rigidity(§4.6;実測では `Matcher a` 引数の単一化が拒否される)がこの経路を塞ぐ)。よって hgen は「rigidity を尊重する導出」への制限つき一般化補題として Stage 2 で放電する。λ 抽象は本体をインスタンスごとに再型付けするので宣言的にも安全(リークは let のスキーム化だけ)。強制(3 コアーション)の hty 場合分けは、強制の結論型が matcher/slot に限られ premise が prod/matcher で非強制規則に到達することから、入れ子 `cases` 深さ ≤ 2 で有限に処理できる(coe2 → coe1 が最長)。

## 機械化が浮かび上がらせた論文の細部(**2026-07-28 論文へ反映済み**、英日両版)

- **MS-MNODE-STEP の一般化**:論文 Fig 3 の規則は内側スタックの先頭が「原子」の場合のみを書いていたが、パターン関数のネスト適用では内側先頭が MNode になる状態が生じる(f の本体内で g q⃗ が展開された直後)。機械化と論文の双方で規則を任意の内側先頭木に一般化(`Semantics.lean` の `mnodeStep`;論文は Fig 3 + §3.3 + 付録 C.2/C.3 の対応箇所を更新)。
- **WT-MNODE の内側入力文脈**:論文 Fig 6 は内側スタックの型付けを ε から始めていたが、本体内で先に束縛された $ 変数を後続の値パターンが参照するには dom_typed(θ_f) から始める必要がある(WT-STATE の外側の扱いと平行)。機械化と論文の双方で後者を採用(`WellTyped.lean`;論文は Fig 6 + Def 5.3 + キャプションを更新。入れ子 MNode の変数パターン出現の数え方の明確化も同時に反映)。
- **(その 4、2026-07-28、論文・実装・機械化へ反映済み)bare-hole 節の順序条件と節規則の適用対象 — 散文・証明が前提していた規律の形式化**:順序(catch-all 最後)自体は論文が既に前提として明記していた(付録 C.3 の catch-all ケースは「by clause order」を根拠に使い、Def 4.2(2) の説明文は「他の節が残したパターンを扱う」、Def 4.2(4) は精密化節が一般節より「先に選ばれる」と述べる)。差分は、定理が量化する**形式述語としての** Def 4.2(2) が「∈ cls(存在)」しか要求しておらず「by clause order」がどの条項にも対応していなかったこと、および**実装が検査していなかった**こと(逆順マッチャーが型検査を通過し実行時 something エラー — 実機再現済みの実害)。(i) **順序**:catch-all(bare-hole 節)は「他の節が残したパターンを扱う」(Def 4.2(2))が、節は先頭から試され PPP-HOLE は任意のパターンに一致するので、bare-hole 節が Coverage の一般形節より**前**にあると構成子パターンを捕まえて `(c p⃗, something, v)` に到達し行き詰まる(現行 Def 4.2 は ∈ だけを要求するのでこの逆順マッチャーも「整合」— (b) の反例)。標準ライブラリの慣習(catch-all 最後)を条件化する必要がある:「各 bare-hole 節の前に、Coverage が要求する全一般形節(積型なら一般タプル節)が現れる」。(ii) **節規則の適用対象**:MS-MATCHER 系規則に p の側条件がなく、`(x::xs) & $y` のような and パターンも catch-all に捕まり(MS-AND との非決定的重なり)、部分パターンの構成子が something に到達しうる。実装(Egison)は and/or/パターン関数適用/~x を**節照合の前に**構文主導で処理しており、規則側に「p は節適用形(構成子/タプル/変数/ワイルドカード/値パターン)」の側条件を付けて一致させるべき。**反映済み(2026-07-28)**:機械化 = `Pattern.isClauseForm` 側条件(MAtom 3 規則+`matomF` ガード+Adequacy 配管)+`ConsistentClauses.holeAfterGenerals`;論文 = Fig 2 側条件・§3.3・Def 4.2(2) 順序文・(1c) インスタンス注記・付録 C.3・付録 J(en 65p/ja 63p ビルド済);実装 = 逆順(catch-all 後の到達不能節)を型エラー化(Infer.hs、minitest/009)。lib/sample の全 36 マッチャーが順序条件を満たすことを全数調査で確認し、逆順マッチャーが「型検査通過→実行時 something エラー」になる反例も実機で再現してから条件化した。なお 1(a) の構造的許容性(穴の構造成分=標的の骨格改名)が「something を分解可能標的の穴に置く」誤りを既に静的排除していることも機械化で確認した(PP-Con の refresh がその機構;bare-hole 節だけが構造検査空虚で、だからこそ (i) の順序条件が要る)。
- **(その 3、2026-07-28 最終設計:原子環境での先行評価+intercept-ok)PPP-VAL の捕捉評価**:pp の #$y に捕捉された p 側 #M の M は、**節選択時に原子の環境(MS-REDUCE の ρ∪θ)で先に**評価される — これを公式の意味論として採用。従って**原子より前の束縛は使える**(実測:`($p :: _, $ls ++ #p :: $rs)` でタプル第 1 成分のピボット p を第 2 成分の `sortedList` ピボット節が参照して成功、`egison/mini-test/125`)が、**同じ原子内の左の穴の束縛は使えない**(実測:`$ys ++ #ys` は無音の `[]`;未束縛参照がシンボル化)。当初案の接頭条件 (i) は `sortedList` のピボット節 `$ ++ #$px :: $` や `assocMultiset` の `($, #$n) :: $` を殺すため撤回。この条件は**パターン単独でもマッチャー単独でも静的に決められない**(同じ #e が取り出し経路では左束縛を見られる — pair の #pat;捕捉深さはマッチャーの pp 形状に依存)ので、**パターン・マッチャー対の条件 = 値パターンスコープ条件、WT-ATOM の premise `vp-scoped`**(機械化 `capturedExprs`/`VPScoped`)として定式化。論文 = Def 4.2(4) 書き換え+Fig 6 WT-ATOM に premise+Def 5.3+付録 J(en/ja ビルド済)。実装 = 意味論は元からこの通り(thunk が原子環境を捕捉);**マッチャーの節形状が静的に既知の site(リテラル・そのタプル・トップレベル定義の適用)では型エラーとして静的検査を実装**、不明(スロット引数)な site は付録 J に開示のとおり検査対象外。

## 現状(2026-07-28 第 10 版)

- `lake build` 成功(エラー 0)。`sorry` は **1 宣言** = `type_safety_b_at`(Φ 一般化形;`type_safety_b` はその Φ=[] 特殊化の**清潔な系**になった)。
- 第 10 版:**Φ 一般化と Step 結合再帰子への移行が完了し、MS-MNODE-STEP が「occs 保存」1 点に還元**:
  - `WTStateAt`(Φ 一般化)+`WTState = WTStateAt … []`(abbrev;既存の (a)/Safety は無変更でコンパイル)。規則別保存補題 9 本を Φ 一般化。
  - `type_safety_b_at` を `Step.rec`(motive_4)で再構成:**内側再帰の帰納法の仮定が使える形**になり、MS-MNODE-STEP ケースは「内側状態の WTStateAt(mnode premise から構成)→ IH → 外側 mnode の再構成」まで組み上がった。残る義務はちょうど 1 つ:`stackEmbedOccs s''.S = rem.map fst`(内側 1 ステップが ~x 出現列を保存すること)。
  - 残 sorry 分岐(再掲+occs):MS-MATCHER 系 3・PATFUN-ENTER・MNODE-VARPAT・occs 保存。
- **occs 保存の開発計画(確定)**:`stackEmbedOccs` の append 補題・`ppm_occs`(PPM 抽出は出現列を保存)・`matom_occs`(全 MAtom 規則;or は noEmbedInOr が必要)・`step_occs`(Step.rec でもう一周;patfunEnter ケースは linearity+params の Nodup(PatFunWF へ追加要)+zip-resolve 整列補題)・noOr の維持(`stackNoOr` を WT-MNODE の premise に追加+部分パターン閉性)。

## 現状(2026-07-28 第 9 版)

- `lake build` 成功(エラー 0)。`sorry` は **1 宣言** = Thm 5.6(b)(骨組み配線済み)。
- 第 9 版:**and/or 原子を成分分解形の規則に再構成し、(b) 本体の骨組みを配線**:
  - **`WTTree.atomAnd`/`atomOr`** 新設(atomTuple と同旨:MS-AND/MS-OR の継続そのものを premise に持つ;子の vp 条件が threaded な入力で子の WT-ATOM に宿るので、and/or については vp 弱化補題が不要になった)。`atomScalarOK` は pand/por も除外。Lem 5.5 は新 2 ケース(自明)追加+旧スカラー枝は矛盾で閉じる。
  - **`preserve_and`・`preserve_or_left`/`preserve_or_right`** を証明(premise がちょうど後続原子の木なので自明に近い)。
  - **`type_safety_b` の本体を規則別に配線**:14 分岐(MAtom 11+Step 3)のうち **9 分岐が証明済み補題で閉じた**(SOME-WC/VAR/VAL-EQ/VAL-NEQ・AND・OR×2・TUPLE・PROD-SOME・MNODE-DONE)。残る sorry 分岐 = MS-MATCHER 系 3(後続 vp の transport [b-4]+役割別 τt 取り直しの補題化 [b-5.5])・MS-PATFUN-ENTER / MS-MNODE-VARPAT([b-3] 双対スキームのインスタンス化=添字再フレッシュ化つき代入補題)・MS-MNODE-STEP(WTState の Φ 一般化+Step.rec への移行+接尾辞不変量の維持補題(MAtom の occs 保存、noEmbedInOr の部分パターン閉性))。

## 現状(2026-07-28 第 8 版)

- `lake build` 成功(エラー 0)。`sorry` は **1 宣言** = Thm 5.6(b)。
- 第 8 版:(b) の**易ケース群を規則別補題として証明**+分業の確定:
  - **`atomScalarOK`**:スカラー WT-ATOM に「タプルパターン×積マッチャー値は除く」側条件を追加(それらは `atomTuple` 側で型付ける分業を確定;Thm 5.7 `matcher_consistency` は同仮定を取る形に。Lem 5.5 のタプル×積スカラー枝は矛盾で閉じ、atomTuple 枝が progress を担う)。
  - **VPScoped のタプル成分再帰を「運搬形」として復活**(pand/por/ptuple×tuple を構造的に潜り、すべて入力 Δ₀ 基準で運ぶ;後続原子の threaded 入力への橋渡しは vp 弱化補題([b-4]、束縛名×捕捉式自由変数の非衝突を側条件)の仕事、と役割を明確化)。
  - **証明済みの (b) 規則別補題**:`preserve_mnodeDone`(v7)+`preserve_someWC`・`preserve_someValEq`(NEQ は継続空で義務なし)・`preserve_someVar`(τt 固定の成果:束縛=宣言型が直接成立)・`preserve_prodSome`(パターン構造添字と something 添字を同じ fresh 変数に取り直す)・`preserve_tuple`(atomTuple 型付けなら継続=成分原子列そのもの、`wtStack_append` で接続)。
  - 補助層:`wtStack_append`・fresh 変数供給(`freshFor`/`freshFor_not_mem`/`applyTS_single_not_mem`/`unifiable_var_fresh`/`renamesTo_var_refl`/`oneWay_var_refl`)。
- (b) の残ケース:MS-AND/OR(vp 弱化待ち)・MS-MATCHER 系 3 規則(本丸;[b-5.5] の役割別取り直し)・MS-PATFUN-ENTER/MS-MNODE-VARPAT([b-3] 双対スキームインスタンス化+vp)・MS-MNODE-STEP(接尾辞不変量の維持補題)・本体組み立てと結合帰納([b-5])。

## 現状(2026-07-28 第 7 版)

- `lake build` 成功(エラー 0)。`sorry` は **1 宣言** = Thm 5.6(b)。
- 第 7 版:(b) へ向けた**不変量の再設計 3 点**(全体ビルド緑のまま):
  - **WT-ATOM の値型を τt に固定**(`ValueTy v τt`;旧 `ValueTy v τ`+`Unifiable τt τ` の支配的単一化子読みを廃止)。初期原子は site で τ = τt が成立し、MS-MATCHER の抽出値の型付けを「節型付けの τt インスタンス側」で取れば等号のまま伝播する(ClausesTy の宣言的 ts 自由度+スロット強制の再単一化が、論文の「θp∘U で代入」を導出の再選択として肩代わりする)。これで (b) の SubstTyped 再建(束縛=宣言型)が直接通る(MS-SOME-VAR で v : τt がそのまま束縛型付けになる)。Progress/Safety は機械的に追随(MS-TUPLE ケースはむしろ簡単化)。
  - **VPScoped のタプル再帰を撤去**:タプル原子は `atomTuple` が成分原子列として型付けるので、成分の vp 条件は各成分原子の WT-ATOM が threaded 入力で持つ(旧版の同一 Δ₀ 検査は単調でなく (b) の再建で使えない)。
  - **VPScoped に and/or 再帰を追加**:MS-AND/MS-OR は子を同じ m と対にするので、子の捕捉条件を親が持つ必要がある(capturedExprs は pand/por を潜らないため旧定義では消失していた)。子 p₂ の入力は実際には Δ₁(p₁ の束縛後)なので、(b) では Δ₀→Δ₁ の vp 弱化(捕捉式の Γ 参照が p₁ の束縛名と衝突しない freshness 側条件つき)が要る — [b-4] の残項目。実装の静的検査は元々 and/or の子へ再帰しており整合。
- 第 7 版で証明:`preserve_mnodeDone`((b) の MS-MNODE-DONE ケース;接尾辞前提から rem = [] を導き PatTys nil で Δ 素通し)。

## 現状(2026-07-28 第 6 版)

- `lake build` 成功(エラー 0)。`sorry` は **1 宣言** = Thm 5.6(b)(TypeSafety.lean)。
- 第 6 版で証明完了:**Thm 5.6(a)(式評価の型付け)** — oracle 分解(設計判断 19)。
  - 新ファイル `Metatheory/TypeSafety.lean`:`Eval.rec` の 5 motive 適用で全 12 Eval ケースを処理(強制層は入れ子 `cases` ≤ 2 段+値レベル追随 `valueTy_coerce2/3`)。
  - 新補題:`envTyped_of_parts`/`envTyped_dom`/`envTyped_inst`/`envTyped_cons_scheme`/`envTyped_cons`/`envTyped_of_substTyped`・`mkListV_typed`・`primEval_typed_append`/`primEval_typed_splits`・`ctor_not_prod`/`ctor_not_matcher`。
  - EV-MATCHALL:e_t/e_m の IH+`hinit`(oracle)で初期 WT 状態を作り、`search_mem_reaches` → `reaches_preservation`(hb)→ `terminal_subst_typed` で各解 θ の `SubstTyped` を得て、`envTyped_append` の下で本体 IH、`mkListV_typed` で結果型。
  - Lem C.2 を oracle 不要の核 `slot_value_inv` + wrapper に分離(Preservation.lean)。
  - **WT-ATOM-TUPLE**(`WTTree.atomTuple`)を追加:タプル原子の成分分解形(成分原子列の WTStack スレッディング)。COERCE-SLOT-TUPLE 由来 site の witness 合成問題(成分の改名・代入が変数を共有しうる)と [b-4] の vp-threaded 伝播の両方を解く追加規則(既存証明は無傷;`wtTree_progress` に自明ケース追加)。
- 第 5 版で証明完了:**Lem 5.5(Matching State Progress)全体**。
  - 前提修正 2 件:T-SOME/ValueTy.something の裸変数固定(設計判断 16;これなしでは反証可能だった)・armExh のインスタンス閉包(設計判断 17)。既存証明・Examples への影響ゼロ(全用例が元々変数添字を使用)。
  - 新補題:`applyTS_comp_pointwise`/`instSig_applyTS`(代入合成)・`vshape_applyTS`(VShape の代入安定性)・`armExh_instance`・`renamesTo_data_inv`/`renamesTo_prod_inv`・`valueTy_something_var`/`valueTy_tuple_matcher_inv`/`valueTy_matcherV_consistent`/`valueTy_matcherV_clausesTy`・`eval_tuple_inv`・`prodK_of_len_ne_one`・`ppm_total`(PPM の全域性、停止仮定つき)・`ppm_length`(抽出長=穴対数;型付け非依存)・`generalPP_shape`/`tupleGeneral_shape`/`catchall_witness`・`find?_key_of_mem`。
  - 本体:節/アーム歩き(`clause_walk`/`arms_walk`;MS-MATCHER の評価前提は `htotal`+∀Γ' 形 (a)-oracle で構成)→ `matcherV_progress` → `wtTree_progress`(`WTTree.rec` 結合再帰子、木 motive+スタック motive;mnode は varpat/done/内側再帰、embed 原子は接尾辞前提から Π ヒットを導出)→ `ms_progress`(トップは Φ=[] で embed 排除)。
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

- **Stage 1(コア型安全性、付録 C;残る sorry 1 = Thm 5.6(b) の解消と oracle の放電)**。前段の定義修正から:
  - **[b-1] 節規則の適用対象条件(細部その 4(ii))— 済(2026-07-28)**:MAtom の matcher 3 規則に `p.isClauseForm = true` を追加、`matomF` の matcherV 行に同ガード、Adequacy 配管、walk 側は `rfl` 供給。ビルド緑。
  - **[b-2] bare-hole 節の順序条件(細部その 4(i))— 済(2026-07-28)**:`ConsistentClauses.holeAfterGenerals`(各 bare-hole 節の手前の `take i` に Coverage の全一般形節+積型の一般タプル節)。(b) では pctor/ptuple の選択節が必ず非 bare-hole になり、後続原子の構造前提を 1(a) の構造的許容性(refresh = 標的骨格)+ instSig_args_agree 系の合成で再建する。
  - **[b-3] HM 代入補題**(論文の「HM substitution lemma at θp∘U」):HasTy/PatTy/ClauseTy 系の相互帰納。matcher 添字の rigidity(§4.6)との整合に注意(T-MATCHER の整合性 premise は τ のインスタンス化で保たれない — coverage が空虚→非空虚に変わる例(Matcher a の bare-hole-only マッチャー)があるので、補題は「代入が matcher 添字位置に触れない」制約つきで立てる)。armExh は既にインスタンス閉包(設計判断 17)なのでこの成分は代入で自明に保たれる。
  - **[b-4] 後続原子の `VPScoped` 伝播**:捕捉式の型付けは threaded Δ でなく**原子入力 Δ** が要るため、MS-TUPLE の成分原子には threaded 入力での VPScoped が要る。現行の `VPScopedList`(全成分を同じ Δ₀ で検査)は shadowing で単調でないので、WT-ATOM のタプル場合を成分ごとの threaded 判断に再構成する(WTAtom を (p,m) 対に構文主導化するのが有力)。あわせて (a) の EV-MATCHALL ケースには site の意味的 vp 仮定(静的検査が既知形状 site で放電;不透明 site は付録 J の開示どおり保証外)を oracle として渡す。`ppp_core` の ∀Γ' oracle の放電も vp-scoped 経由(捕捉式は Δ₀ 型付け+θ:Δ₀ で EnvTyped が立つ)に精密化する。
  - **[b-5] 本体**:(b) を Step/MAtom motive の結合帰納で証明((a) は済:oracle hb を (b) 本体が、(b) は (a) を oracle に取る相互は、最終的に 5 motive 一括帰納で置換して閉じる)。MS-MATCHER ケースは Lem 5.4(済)+ pdMatch_typed(済)+ [b-2] の構造再建 + [b-3]。
  - **[b-5.5] 再建の規律(第 7 版で確立;2026-07-28 精密化)**:不変量は τt 一本(WT-ATOM 改定済)。MS-MATCHER の後続原子の再建で τt インスタンスに取り直すのは**役割別に一部だけ**:(i) 抽出パターン側 = 選択節の **PPTy を τt で**(スロット検査を含まないので常に可能;Lem 5.4 の interface と一致)、(ii) 値側 = 選択アームの **PDTy+本体 HasTy を τt インスタンスで**取り直して (a)-oracle から vN : τt-側の型を得る、(iii) 次マッチャー成分は**内在型のまま**(構造前提は抽出パターンの構造添字を変数に取り直して通す;something が要素マッチャーとして働くのはこの扱い)。**節全体(スロット検査 1a 込み)の τt 再型付けは不可能**(something 成分は Int 標的の穴の構造検査 β′ ⊑ Int に落ちる)なので、旧案の「ClausesTy Γm τt cls を WT-ATOM に運ぶ」は過剰で誤り — 運ぶべきは (i)(ii) 相当(選択節の pp+アームの τt-インスタンス型付け)のみ。**精密化候補の決着(2026-07-28 実機確認)**:アーム本体が節のインスタンス化変数依存のマッチャーリテラルを含む例(inner-matcher-body.egi:cons アーム内で `matcher | $ as something …` を作り matchAll する)は**実行時安全で型検査も通る**(実測 `[([1,2],[[3]])]`)。素朴な θp∘U 代入(リテラルの添字 a を [Int] へ点wise 置換)は Coverage 空虚→要求の遷移で存在しないが、**リテラルの添字を fresh 変数に取り直して site の標的前提 c ~ [Int] を再導出すれば代入後の導出は存在する**。よって Def 4.2(1b) の閉包強化は不要の見込みで、[b-3] の代入補題を「マッチャーリテラルの添字は再フレッシュ化して移す」形で立てるのが正解(機械化の「τt での取り直し」路線はこれを内包)。C.3 の該当文への注記は (b) 完成時に検討。
  - **[b-6] oracle の放電**:`hgen` — **rigidity のインスタンス化条件が論文 §4.6 の正式規則になった(2026-07-28、ユーザー決定「実装のとおりの規則にする」):「スキーム変数のうち出現がすべて Matcher 添字内のものは変数にしかインスタンス化できない」**(実装の単一化器 `unifyG`:`TMatcher t1 ~ TMatcher t2` は t1 ≡ t2 のときのみ成功、の宣言的対応物;実装はさらに厳しく Matcher 型仮引数を一律拒否 — useM 実測)。機械化側の放電 = `Scheme.Inst` をこの条件で制限した `Inst_rigid` を定義し、hgen をその下で証明([b-3] の添字再フレッシュ化つき代入補題と同じ機構)(設計判断 19)・`hinit`(初期状態整型 = vp-scoped 静的条件+`atomTuple` 組み立て+スロット witness の改名分離 = HasTy 改名補題)・Lem 5.4/5.5 の ∀Γ' 形 (a)-oracle の vp-scoped 経由への精密化。
  - list/multiset 整合性(Def 4.2)の実例検証([b-2] の順序条件を満たすことの確認込み)。
  - 論文反映:細部その 4 の (i)(ii) を Def 4.2(2)・Fig 2・§3.3/付録 C.2 に明文化+1c のインスタンス読みの注記(en/ja 同期)。
- **Stage 2(主型性、付録 B/D)**:rigidity 付き Robinson 単一化 → Algorithm W(matchAll の Step 1–6・スロット処理 3a/3a′/3b)→ Lem D.1–D.3 → Thm 5.3。
- **Stage 3(拡張)**:loop パターン・型クラス(付録 F の辞書渡し)・値引数つきパターン関数など、論文 §7 の open directions に対応する範囲の検討。
