# type-pm-mech 固有ルール

`type-pm-mech` は，`Matcher κ τ` と `MatcherSlot κ τ` を持つ非 CAS Egison core を
Lean 4 で機械化するプロジェクトである．親ディレクトリ `../CLAUDE.md` の規則，特に
commit／push はその都度の明示指示がある場合に限るという規則にも従う．

## 文書の役割分担

- `README.md` — 最上位目標・設計原理・ロードマップ（大局）
- `docs/details.md` — モジュール単位の詳細仕様・証明状況・回帰一覧（詳細）
- `tex/main.tex` — 形式仕様
- この CLAUDE.md — 作業規律のみ

意味に触れる変更の前に README の該当節と `docs/details.md` の該当節を読む．変更後は
四者（Lean・tex・README・docs/details.md）の記述を同期し，過去の進捗日誌・解決済み
問題メモ・旧 calculus の説明をこれらの文書に残さない．大局と詳細を混ぜない：README に
モジュール内部の機構説明を書かず，docs/details.md に目標・原理の再定義を書かない．

## ビルド

- Lean toolchain は `lean-toolchain` で固定する．外部依存はなく Mathlib も使わない．
- 全体検証はリポジトリ直下で `lake build` を実行する．`TypePM.lean` は現行 public
  surface の全モジュールを import するので，変更後は個別 target だけでなく必ず
  `lake build` を通す．
- 形式仕様 `tex/main.tex` は `tex/` で `make` を実行して検証し，
  `tex/type-pm-mech.pdf` を生成する．`main.pdf` は作らない．

## 証明の品質

- `sorry`，`admit`，`axiom` を使わない．型付け導出そのものを field に持つ oracle や，
  任意の capability 輸送を許す blanket premise で穴を隠さない．
- 具体 signature の `signature_wf` は `by decide` で discharge し，`native_decide` を
  新たに導入しない．
- `docs/details.md` の回帰一覧にある executable regression とその正負境界を維持する．
  正例／負例のどちらかを削る変更は，対応する設計判断ごと見直す．

## 設計規律

以下は破ってはならない不変量である．各項の詳細と根拠は `docs/details.md`．

### calculus と宣言体系

- 現行 calculus は `TypePM/` の二 sort・二 index 版だけである．旧一添字 calculus，
  抽象 `RuntimeSpec`／`CoreSpecWF`，それらに相対的な旧安全性証明を復活させない．
- 宣言的 `HasTy` は意図的に広い**動的安全性の包絡**として維持する．狭めない．
  受理完全性の前提にも使わない（`WideAnnotationFree` は恒久的に反証済みであり，
  完成目標でも open goal でもない）．
- source matcher literal は actual clause evidence，`ShapeCap`，`CatchAllLast`，
  data-arm exhaustiveness，binder 線形性，`CoverageOK` をすべて要求する．coverage を
  欠く literal を追加 mode で受理する経路を作らない．
- value-flow scheme の宣言的 instance（context lookup と pattern-function lookup）では
  capability binder を capability variable へだけ写し，producer capability を consumer
  demand に合わせて構造化する経路を追加しない（variable-only 条件）．constructor／
  primitive signature の `Inst` は通常の binder-supported structural instance であり
  対象外．binder image の相異性と ambient freshness は W の強い allocation witness に
  だけ要求する．
- recursion は singleton direct-self の単相 `fix` だけを core に含める．alias，mutual
  recursion，高階 origin は fail closed とする．

### coercion（slot-demand 原則）

- coercion 挿入は demand-directed を根本原則とし，**demand の唯一の形は expected head
  が `MatcherSlot` であること**とする．checking は式を先に synthesize し，その cut で
  prevailing 適用後の expected head を観測して branch を決定する．非恒等 coercion の
  終点は常に slot（`matcherToSlot`／`productMatcher; matcherToSlot`／`slotTuple` の
  三形）であり，Matcher 終点の coercion を demand 経路（selector・将来の `DDTyping`）に
  追加しない．matcher-expected 位置は raw `Matcher` の通常単一化だけを許す．
- 「通常単一化の失敗」を coercion の負前提にしない．failed attempt の rollback，fuel
  切れ，guard 拒否を coercion の根拠に持ち込まない．branch 選択は visible な head から
  決定し，選択後の solve が失敗すればその check は失敗する．
- 各 solve は syntax，signature，fresh state と現在の constraint だけから決まり，
  coercion を成立させるために λ domain や未解決 metavariable の構造を推測する
  no-guess 違反を許さない．λ domain は fresh metavariable とし，任意の `MatcherSlot`
  domain を先に選べる宣言的 λ 規則で `DDTyping` を代用しない．
- **raw visibility**（cut 時点で selector に必要な head が raw source に見えるか）と
  **capability freeze**（producer image に許される substitution／export）は demand とは
  別軸であり，fragment 受理完全性で別々に扱う．capability-origin ledger は coercion
  demand に別証人を要求する仕組みではない．
- `nestedCapProgram`（と swapped 版）の拒否は意図された挙動であり変えない．全 `HasTy`
  導出が demand-free coercion に依存するという inversion は未証明なので主張しない．

### inference と validator

- 公開 entry point `infer` は停止する raw 走査 `inferRaw` と有限な fail-closed terminal
  validator の合成である．公開 `infer` が成功したとき，成功等式だけから
  `infer_success_sound` が concrete `HasTy` を与える状態を維持する．
- `InferenceInputWF` を soundness の前提に戻さない．`WBridgeWF` は validator が内部で
  構成する証明書であり，呼び出し側の追加前提に戻さない．terminal validator の
  completeness は主張しない．
- principality はそのままの形では機械化反例（`no_principal_type`）により反証済みで
  あり，principal-type theorem を無証明で復活させない．存在定理（∀ typing ∃θ plan）を
  先に立て，canonical boundary を定義してから条件付き一意性を扱う．proof-indexed な
  derivation property や `ElaborableHasTy := ∃ CoreTyping` のような循環的定義で
  代用しない．
- `DDTyping` は未定義・未証明である．judgment と定理を定義・証明する前に成立済みとは
  主張しない．

### 動的安全性

- 動的安全性は concrete `HasTy`／`ValueTy`／matching-state judgments 上で述べる．
  抽象 spec に相対化しない．
- primitive-pattern pattern は depth-first・左から右に走査し，一度 hole を通過した後の
  value-pattern-pattern を禁止する（`PPatCoreOrder`）．この順序条件から値パターン
  capture admissibility を導出し，公開 preservation の前提には戻さない．局所的な
  埋込み評価の `StepReady` だけは progress 定理の明示前提としてよい．
- 動的定理の唯一の global 条件 `FrozenSigWF` は仮定に戻さず，実行可能 checker
  `frozenSigWFCheck`＋`frozenSigWFCheck_sound` で確立する．checker は保守的・
  fail closed を維持する．
