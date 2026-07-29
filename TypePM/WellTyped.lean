import TypePM.Typing

/-!
# 値の型付けと整型マッチング状態 (論文 §5.3・付録 C Fig 6)

* `ValueTy` — 値の型付け v : τ(§5.3「Value typing」;closure/matcher 値は
  捕獲環境を型付ける Γ の存在で述べる)
* `MatcherOK` — WT-ATOM のマッチャー選言
  (something ∨ Σ_P 整合 ∨ その積マッチャー)
* `SubstTyped` — 型付き代入(§5.3「Typed substitutions」)
* `WTTree` / `WTStack` — WT-ATOM / WT-MNODE / WT-STACK-NIL / WT-STACK-CONS
* `WTState` — WT-STATE(⊢ s : Δ_goal ok)

paper との差分(README 設計判断):WT-MNODE の内側スタックの入力文脈は
論文の ε ではなく dom_typed(θf) とする(本体内で先に束縛された変数を
後続の値パターンが参照できるために必要;機械化で見つかった精密化)。
-/

namespace TypePM

/-! ## 値の型付け -/

inductive ValueTy (SD : SigD) (SP : SigP) (SF : SigF) : Value → Ty → Prop where
  | lit {n} : ValueTy SD SP SF (.lit n) .int
  | ctor {C sig ts vs} :
      List.find? (fun pr => pr.1 == C) SD = some (C, sig) →
      vs.length = sig.args.length →
      (∀ pr ∈ vs.zip (sig.args.map (Ty.instSig ts)), ValueTy SD SP SF pr.1 pr.2) →
      ValueTy SD SP SF (.ctor C vs) (Ty.instSig ts sig.res)
  | tuple {vs τs} :
      vs.length = τs.length →
      (∀ pr ∈ vs.zip τs, ValueTy SD SP SF pr.1 pr.2) →
      ValueTy SD SP SF (.tuple vs) (.prod τs)
  | closure {self ρ x e τ₁ τ₂} (Γ : TyCtx) :
      -- Γ が ρ を型付ける(∃ を避けた 2 前提形;nested inductive 制限のため)
      (∀ y v, Env.find? ρ y = some v → ∃ σ, TyCtx.find? Γ y = some σ) →
      (∀ y v σ τ', Env.find? ρ y = some v → TyCtx.find? Γ y = some σ →
        σ.Inst τ' → ValueTy SD SP SF v τ') →
      (self = none → HasTy SD SP SF ((x, .mono τ₁) :: Γ) e τ₂) →
      (∀ f, self = some f →
        HasTy SD SP SF ((x, .mono τ₁) :: (f, .mono (.fn τ₁ τ₂)) :: Γ) e τ₂) →
      ValueTy SD SP SF (.closure self ρ x e) (.fn τ₁ τ₂)
  | matcherV {ρm cls τ} (Γm : TyCtx) :
      (∀ y v, Env.find? ρm y = some v → ∃ σ, TyCtx.find? Γm y = some σ) →
      (∀ y v σ τ', Env.find? ρm y = some v → TyCtx.find? Γm y = some σ →
        σ.Inst τ' → ValueTy SD SP SF v τ') →
      HasTy SD SP SF Γm (.matcher cls) (.matcher τ) →
      ValueTy SD SP SF (.matcherV ρm cls) (.matcher τ)
  | something {a} :                -- T-SOME の評価像(内在型は必ず Matcher (裸変数);
      -- 論文 §5.3「something : Matcher α by T-SOME」。これが WT-ATOM の構造前提による
      -- 構成子/タプルパターンでの something 却下(付録 C.2)を全導出で保つ)
      ValueTy SD SP SF .something (.matcher (.var a))
  | prodMatcher {ms τs} :          -- COERCE-TUPLE-MATCHER の値レベル対応物
      ms.length = τs.length →      -- (積マッチャー (m₁,…,m_k) : Matcher (τ₁ × ⋯ × τ_k))
      (∀ pr ∈ ms.zip τs, ValueTy SD SP SF pr.1 (.matcher pr.2)) →
      ValueTy SD SP SF (.tuple ms) (.matcher (.prod τs))
  | slotV {m τm τm' τp τt} :       -- COERCE-MATCHER-TO-SLOT の値レベル対応物
      ValueTy SD SP SF m (.matcher τm) →   -- (スロット型で束縛される λ 引数の
      RenamesTo τm τm' →                   --  環境型付けに必要;Lem C.2 の内実)
      OneWay τp τm' →
      Unifiable τm τt →
      ValueTy SD SP SF m (.slot τp τt)
  | prodSlot {ms} {prs : List (Ty × Ty)} : -- COERCE-SLOT-TUPLE の値レベル対応物
      ms.length = prs.length →
      (∀ pr ∈ ms.zip prs, ValueTy SD SP SF pr.1 (.slot pr.2.1 pr.2.2)) →
      ValueTy SD SP SF (.tuple ms)
        (.slot (.prod (prs.map (·.1))) (.prod (prs.map (·.2))))

/-- Γ が ρ を型付ける(判断の外で使う再利用形) -/
def EnvTyped (SD : SigD) (SP : SigP) (SF : SigF) (Γ : TyCtx) (ρ : Env) : Prop :=
  ∀ y v, Env.find? ρ y = some v →
    ∃ σ, TyCtx.find? Γ y = some σ ∧ ∀ τ', σ.Inst τ' → ValueTy SD SP SF v τ'

/-! ## WT-ATOM のマッチャー選言 -/

/-- m = something ∨ m は Σ_P 整合 ∨ m はそれらの積マッチャー(Def 5.3 の選言) -/
inductive MatcherOK (SD : SigD) (SP : SigP) : Value → Prop where
  | something : MatcherOK SD SP .something
  | consistent {ρm cls τ} :
      ConsistentClauses SD SP cls τ →
      MatcherOK SD SP (.matcherV ρm cls)
  | prod {ms} :
      (∀ m ∈ ms, MatcherOK SD SP m) →
      MatcherOK SD SP (.tuple ms)

/-! ## 型付き代入 (§5.3) -/

/-- Δ が θ を型付ける:dom が(束縛順で)一致し、各束縛が宣言型を持つ。
    θ は先頭が新しいので dom は逆順で対応する。 -/
def SubstTyped (SD : SigD) (SP : SigP) (SF : SigF) (Δ : BindCtx) (θ : Subst) : Prop :=
  Δ.map (·.1) = (θ.map (·.1)).reverse ∧
  ∀ pr ∈ Δ, ∃ v, Env.find? θ pr.1 = some v ∧ ValueTy SD SP SF v pr.2

/-! ## 値パターンスコープ条件 (Def 4.2(4)・WT-ATOM の vp-scoped 前提)

#$y に捕捉された値パターンの式は原子の環境で(=先に)評価されるので、
原子の入力文脈 Δ₀ で型付かなければならない(原子より前の束縛は使えるが、
同じ原子内の左の穴の束縛は使えない)。

定義は pand/por/ptuple×tuple を構造的に潜り、matcherV 先頭対で
捕捉条件を述べる(すべて**入力 Δ₀ 基準**の運搬形)。実際の後続原子は
threaded な入力を持つので、(b) での使用時は vp 弱化補題
(束縛名と捕捉式の自由変数の非衝突を側条件とする;README [b-4])で
Δ₀ から threaded 入力へ橋渡しする。タプル原子自体の型付けは
WT-ATOM-TUPLE(成分原子列、threaded)が担う。 -/

mutual
def VPScoped (SD : SigD) (SP : SigP) (SF : SigF)
    (Γ : TyCtx) (Δ₀ : BindCtx) : Pattern → Value → Prop
  | .pand p₁ p₂, m => VPScoped SD SP SF Γ Δ₀ p₁ m ∧ VPScoped SD SP SF Γ Δ₀ p₂ m
  | .por p₁ p₂, m => VPScoped SD SP SF Γ Δ₀ p₁ m ∧ VPScoped SD SP SF Γ Δ₀ p₂ m
  | .ptuple ps, .tuple ms =>
      -- 成分条件の運搬(いずれも原子入力 Δ₀ で述べる)。実際の成分原子は
      -- threaded な入力を持つので、使用時は vp 弱化([b-4])で橋渡しする。
      VPScopedList SD SP SF Γ Δ₀ ps ms
  | p, .matcherV _ cls =>
      ∀ cl ∈ cls, ∀ M ∈ capturedExprs cl.1 p,
        ∃ τe, HasTy SD SP SF (BindCtx.toCtx Δ₀ ++ Γ) M τe
  | _, _ => True

def VPScopedList (SD : SigD) (SP : SigP) (SF : SigF)
    (Γ : TyCtx) (Δ₀ : BindCtx) : List Pattern → List Value → Prop
  | p :: ps, m :: ms =>
      VPScoped SD SP SF Γ Δ₀ p m ∧ VPScopedList SD SP SF Γ Δ₀ ps ms
  | _, _ => True
end

/-- スカラー WT-ATOM の適用対象:タプルパターン×積マッチャー値の原子は
    WT-ATOM-TUPLE(成分分解形)の側で型付ける。成分ごとの vp 条件を
    threaded な入力文脈で持てるのは分解形だけなので、(b) の再建は
    この分業を前提にする。 -/
def atomScalarOK : Pattern → Value → Bool
  | .ptuple _, .tuple _ => false
  | .pand _ _, _ => false
  | .por _ _, _ => false
  | _, _ => true

/-- rem の各対が固定文脈 Φf で自分の双対に解決される(位置対応;
    List.Forall₂ の自前版) -/
def RemInPhi (Φf : PatParamCtx) : PiEnv → List (Ty × Ty) → Prop
  | [], [] => True
  | pr :: rem, d :: duals =>
      List.find? (fun x => x.1 == pr.1) Φf = some (pr.1, d) ∧
      RemInPhi Φf rem duals
  | _, _ => False

/-! ## 整型マッチング木・スタック (Fig 6) -/

mutual
inductive WTTree (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → PatParamCtx → BindCtx → Tree → BindCtx → Prop where
  | atom {Γ Φ Δ Δ' p m v τp τt τm τm'} :               -- WT-ATOM
      atomScalarOK p m = true →                         -- タプル×積は atomTuple 側
      PatTy SD SP SF Γ Φ Δ p τp τt Δ' →
      ValueTy SD SP SF m (.matcher τm) →                -- m の内在型
      RenamesTo τm τm' →                                -- τm' = fresh_rename(τm)
      OneWay τp τm' →                                   -- 構造前提 τm' ⊑ τp
      StructReaches τp τt →                             -- 到達不変量(§4.2 fresh-leaf)
      Unifiable τm τt →                                 -- 標的前提 τm ~ τt
      MatcherOK SD SP m →                               -- マッチャー選言
      ValueTy SD SP SF v τt →                           -- v はパターン標的型そのもの
      -- (旧版は v : τ と Unifiable τt τ の「支配的単一化子」読みだった。
      --  初期原子で τ = τt が成り立ち、抽出値の型付けを節型付けの
      --  τt インスタンス側で取れば等号のまま伝播するので、(b) の
      --  SubstTyped 再建(束縛 = 宣言型)のために τt へ一本化した。
      --  vp-scoped(値パターンスコープ条件、Def 4.2(4))は WT-ATOM の
      --  premise ではなく stackNoOr と同様の並行不変量として扱う:
      --  (b) の内部配管はこれを読まず、消費箇所は Lem 5.4/5.5 の
      --  ∀Γ' oracle の放電([b-6])のみなので、そこで transport する。
      --  論文 Fig 6 の premise 表示は「並行条件の連言」として読む。)
      WTTree SD SP SF Γ Φ Δ (.atom ⟨p, m, v⟩) Δ'
  | atomAnd {Γ Φ Δ Δmid Δ' p₁ p₂ m v} :                 -- WT-ATOM-AND
      -- and 原子の成分分解形:MS-AND の継続そのもの(左→右スレッディング)。
      -- 子の vp 条件を threaded な入力で持つための追加規則(atomTuple と同旨)。
      WTTree SD SP SF Γ Φ Δ (.atom ⟨p₁, m, v⟩) Δmid →
      WTTree SD SP SF Γ Φ Δmid (.atom ⟨p₂, m, v⟩) Δ' →
      WTTree SD SP SF Γ Φ Δ (.atom ⟨.pand p₁ p₂, m, v⟩) Δ'
  | atomOr {Γ Φ Δ Δ' p₁ p₂ m v} :                       -- WT-ATOM-OR
      -- or 原子:両分枝とも同じ入力・同じ出力(PAT-OR と同じ形)。
      WTTree SD SP SF Γ Φ Δ (.atom ⟨p₁, m, v⟩) Δ' →
      WTTree SD SP SF Γ Φ Δ (.atom ⟨p₂, m, v⟩) Δ' →
      WTTree SD SP SF Γ Φ Δ (.atom ⟨.por p₁ p₂, m, v⟩) Δ'
  | atomSlot {Γ Φ Δ Δ' p ms v τp τt σ} :                -- WT-ATOM-SLOT
      -- 積スロット値(COERCE-SLOT-TUPLE 由来のタプルマッチャー)を成分合成せず
      -- **スロット型のまま**担ぐ変種(Lem C.2 の「積の witness は成分の直和」を
      -- 規則レベルで保持)。成分の改名/代入は変数を共有しうるので単一 τm への
      -- 合成は一般に不可能(atomTuple の注記と同じ理由)。p が ptuple の場合は
      -- atomTuple 側(atomScalarOK が排除)。σ は標的の改名(PP-Con refresh 由来)。
      atomScalarOK p (.tuple ms) = true →
      PatTy SD SP SF Γ Φ Δ p τp τt Δ' →
      StructReaches τp τt →
      ValueTy SD SP SF (.tuple ms) (.slot σ τt) →
      RenamesTo τt σ →
      ValueTy SD SP SF v τt →
      WTTree SD SP SF Γ Φ Δ (.atom ⟨p, .tuple ms, v⟩) Δ'
  | atomTuple {Γ Φ Δ Δ' ps ms vs} :                     -- WT-ATOM-TUPLE
      -- タプル原子の成分分解形:成分原子の列を WTStack で左→右にスレッディング。
      -- (i) COERCE-SLOT-TUPLE 由来の site(成分ごとのスロット witness を
      --     単一の τm に合成できない — 成分の改名/代入が変数を共有しうる)と
      -- (ii) 後続 vp-scoped の threaded 伝播([b-4])のための追加規則。
      -- MS-TUPLE の継続はちょうどこの成分原子列になる。
      ps.length = ms.length →
      ms.length = vs.length →
      WTStack SD SP SF Γ Φ Δ
        ((ps.zip (ms.zip vs)).map fun x => .atom ⟨x.1, x.2.1, x.2.2⟩) Δ' →
      WTTree SD SP SF Γ Φ Δ (.atom ⟨.ptuple ps, .tuple ms, .tuple vs⟩) Δ'
  | mnode {Γ Φ Δ Δ' S' ρf θf piE} (rem : PiEnv) (duals : List (Ty × Ty))
      (Γf : TyCtx) (Δθf : BindCtx) (Δfin : BindCtx)
      (Φf : PatParamCtx) :  -- WT-MNODE
      -- 接尾辞前提:S' に残る ~x 出現は piE の接尾辞(宣言順・各 1 回)
      (∃ j, rem = piE.drop j) →
      -- 仮引数名の相異(PatFunWF.paramsNodup 由来;MS-MNODE-VARPAT の
      -- find? が rem 先頭のエントリを返すことの保証)
      (piE.map (·.1)).Nodup →
      stackEmbedOccs S' = rem.map (·.1) →
      -- q-premise 列:残り引数パターンを外側文脈で双対型付け(Δ を Δ' へ継ぐ)
      PatTys SD SP SF Γ Φ Δ (rem.map (·.2)) duals Δ' →
      -- 残り仮引数の双対対は固定の内側文脈 Φf で解決される
      -- (Φf は展開時の全仮引数双対文脈;rem が縮んでも Φf は不変なので、
      --  VARPAT の再建で内側スタックの Φ 転送が不要になる)
      RemInPhi Φf rem duals →
      -- Φf の各双対対の到達不変量(PATFUN-ENTER 時に実引数双対から確立;
      -- MS-MNODE-VARPAT が ~y を Π(y) に差し替えた原子の hreach に供給)
      (∀ pr ∈ Φf, StructReaches pr.2.1 pr.2.2) →
      -- Γf が ρf を型付ける
      (∀ y v, Env.find? ρf y = some v → ∃ σ, TyCtx.find? Γf y = some σ) →
      (∀ y v σ τ', Env.find? ρf y = some v → TyCtx.find? Γf y = some σ →
        σ.Inst τ' → ValueTy SD SP SF v τ') →
      -- θf の型付け(スコープ内に閉じる)
      SubstTyped SD SP SF Δθf θf →
      -- 内側スタックの整型:入力文脈は dom_typed θf(論文は ε;README 参照)
      WTStack SD SP SF Γf Φf Δθf S' Δfin →
      WTTree SD SP SF Γ Φ Δ (.mnode S' ρf θf piE) Δ'

inductive WTStack (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → PatParamCtx → BindCtx → List Tree → BindCtx → Prop where
  | nil {Γ Φ Δ} :                                       -- WT-STACK-NIL
      WTStack SD SP SF Γ Φ Δ [] Δ
  | cons {Γ Φ Δ₀ Δ₁ Δ' t S} :                           -- WT-STACK-CONS
      WTTree SD SP SF Γ Φ Δ₀ t Δ₁ →
      WTStack SD SP SF Γ Φ Δ₁ S Δ' →
      WTStack SD SP SF Γ Φ Δ₀ (t :: S) Δ'
end

/-! ## マッチャー選言の導出補題 -/

theorem exists_mem_zip_left {α β} : ∀ {as : List α} {bs : List β},
    as.length = bs.length → ∀ {a}, a ∈ as → ∃ b, (a, b) ∈ as.zip bs
  | [], [], _, _, ha => nomatch ha
  | [], _ :: _, hlen, _, _ => nomatch hlen
  | _ :: _, [], hlen, _, _ => nomatch hlen
  | a' :: as, b :: bs, hlen, a, ha => by
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨b, by simp [List.zip_cons_cons]⟩
      · obtain ⟨b', hz⟩ := exists_mem_zip_left (by simpa using hlen) ha
        exact ⟨b', by simp [List.zip_cons_cons, hz]⟩

/-- マッチャー型を持つ値は WT-ATOM のマッチャー選言に入る
    (something / Σ_P 整合(T-MATCHER の整合性前提から)/ それらの積)。
    Σ_D 整形性はデータ構成子の結果型がマッチャー型でないことに使う。 -/
theorem matcherOK_of_valueTy {SD : SigD} {SP : SigP} {SF : SigF}
    (hwfD : SigDWF SD) :
    ∀ {m : Value} {τ : Ty}, ValueTy SD SP SF m τ →
    ∀ τm, τ = .matcher τm → MatcherOK SD SP m := by
  intro m τ h
  induction h with
  | lit => intro τm heq; cases heq
  | ctor hfind hlen hall ih =>
      intro τm heq
      exfalso
      rename_i C sig ts vs
      obtain ⟨⟨n, hres⟩, -⟩ := hwfD _ (List.mem_of_find?_eq_some hfind)
      rw [hres] at heq
      simp [Ty.instSig, Ty.applyTS] at heq
  | tuple hlen hall ih => intro τm heq; cases heq
  | closure Γ hdom hty hnone hsome => intro τm heq; cases heq
  | matcherV Γm hdom htyρ hty =>
      intro τm heq
      cases hty with
      | matcherE hclauses hcons => exact MatcherOK.consistent hcons
      | coerceTupleMatcher hpre => cases hpre
  | something => intro τm heq; exact MatcherOK.something
  | prodMatcher hlen hall ih =>
      intro τm heq
      refine MatcherOK.prod ?_
      intro m' hm'
      obtain ⟨τ', hz⟩ := exists_mem_zip_left hlen hm'
      exact ih (m', τ') hz τ' rfl
  | slotV hm hren how huni ih => intro τm heq; cases heq
  | prodSlot hlen hall ih => intro τm heq; cases heq

/-! ## 整型マッチング状態 (WT-STATE) -/

/-- ⊢ s : Δ_goal ok の Φ 一般化形。内側スタックの状態(MS-MNODE-STEP の
    再帰)は Φ = 仮引数双対文脈で整型なので、(b) の帰納はこの形で回す。 -/
def WTStateAt (SD : SigD) (SP : SigP) (SF : SigF)
    (Γ : TyCtx) (Φ : PatParamCtx) (s : MState) (Δgoal : BindCtx) : Prop :=
  EnvTyped SD SP SF Γ s.ρ ∧
  ∃ Δ₀, SubstTyped SD SP SF Δ₀ s.θ ∧ WTStack SD SP SF Γ Φ Δ₀ s.S Δgoal

/-- ⊢ s : Δ_goal ok:Γ は囲む match の型環境(トップレベルは Φ = [])。 -/
abbrev WTState (SD : SigD) (SP : SigP) (SF : SigF)
    (Γ : TyCtx) (s : MState) (Δgoal : BindCtx) : Prop :=
  WTStateAt SD SP SF Γ [] s Δgoal

end TypePM
