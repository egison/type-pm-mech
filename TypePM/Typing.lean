import TypePM.Semantics

/-!
# λ_PM の型システム (論文 §4, Fig 4;付録 A Fig 5 の PP/PD 判定;Def 4.1/4.2)

* `PPTy` / `PDTy` — primitive-pattern pattern / primitive data pattern の型判定
* `ConsistentClauses` — マッチャー整合性 (Definition 4.2) のうち
  型付けに依存しない条件(Coverage・catch-all・arm exhaustiveness)。
  arm exhaustiveness (1c) は意味的に述べる(∀ 値 ∃ マッチするアーム)。
* `HasTy` / `PatTy` / `PatTys` — 式の型判定・パターンの双対判定(相互帰納)。
  - 双対判定 `PatTy Γ Φ Δ p τp τt Δ'` は
    Γ;Δ ⊢ p : Pattern (τp ▷ τt) ; Δ'(Φ はパターン関数仮引数の双対型文脈)。
  - 「fresh 変数」は宣言的読み(任意のインスタンス化;
    最汎性は Algorithm W = 主型ステージの関心事)。README 設計判断参照。
* `PatFunWF` — PATFUN-DEF(記録された双対スキームの実現+線形性)

Matcher rigidity (§4.6) は推論アルゴリズムの制限であり宣言的関係では扱わない
(README 設計判断;主型ステージで扱う)。
-/

namespace TypePM

/-! ## 文脈 -/

/-- 式の型環境 Γ -/
abbrev TyCtx := List (String × Scheme)

/-- パターン関数仮引数の双対型文脈 Φ(x : Pattern (β ▷ τ) を分離して保持) -/
abbrev PatParamCtx := List (String × (Ty × Ty))

/-- パターン変数文脈 Δ(左→右に伸びる) -/
abbrev BindCtx := List (String × Ty)

def TyCtx.find? (Γ : TyCtx) (x : String) : Option Scheme :=
  (List.find? (fun pr => pr.1 == x) Γ).map (·.2)

/-- Δ を単相スキームとして Γ に載せる -/
def BindCtx.toCtx (Δ : BindCtx) : TyCtx :=
  Δ.map fun pr => (pr.1, Scheme.mono pr.2)

def Scheme.ftv (σ : Scheme) : List TyVar :=
  σ.body.ftv.filter (fun a => !(σ.binders.contains a))

def ftvCtx (Γ : TyCtx) : List TyVar :=
  (Γ.map fun pr => pr.2.ftv).flatten

/-! ## 補助定義 -/

/-- k 項積型(1 項は型そのもの、0 項は空積;Def 4.2(1b)) -/
def prodK : List Ty → Ty
  | [τ] => τ
  | τs  => .prod τs

/-- 一般形 c $ ⋯ $ (Def 4.2(1)) -/
def generalPP (c : String) (k : Nat) : PPat :=
  .ctor c (List.replicate k .hole)

/-- 型構成子(head former)の一致(Coverage で「τ の頭型構成子のパターン構成子」を選ぶ) -/
def Ty.headMatches : Ty → Ty → Bool
  | .data n _,  .data n' _  => n == n'
  | .prod ts,   .prod ts'   => ts.length == ts'.length
  | .int,       .int        => true
  | .bool,      .bool       => true
  | _,          _           => false

/-- 次マッチャー式の構文的タプル分解(T-MATCHER:m_i = (m_i^1, …, m_i^k))。
    k = 1 は式そのもの、その他はタプル式。 -/
def decomposeME (M : Expr) (k : Nat) : Option (List Expr) :=
  if k == 1 then some [M]
  else match M with
    | .tuple es => if es.length == k then some es else none
    | _         => none

/-! ## 値の形(arm exhaustiveness の量化域)

Def 4.2(1c) は「型 τ の任意の値がいずれかのアームにマッチ」。
その量化域として、値の型付けの浅い(構成子レベルの)近似 `VShape` を使う
(完全な値型付け `ValueTy` は `WellTyped.lean`;循環を避けるための分離。README)。 -/

inductive VShape (SD : SigD) : Value → Ty → Prop where
  | lit {n} : VShape SD (.lit n) .int
  | ctor {C sig ts vs} :
      List.find? (fun pr => pr.1 == C) SD = some (C, sig) →
      vs.length = sig.args.length →
      (∀ pr ∈ vs.zip (sig.args.map (Ty.instSig ts)), VShape SD pr.1 pr.2) →
      VShape SD (.ctor C vs) (Ty.instSig ts sig.res)
  | tuple {vs τs} :
      vs.length = τs.length →
      (∀ pr ∈ vs.zip τs, VShape SD pr.1 pr.2) →
      VShape SD (.tuple vs) (.prod τs)
  | closure {self ρ x e τ₁ τ₂} : VShape SD (.closure self ρ x e) (.fn τ₁ τ₂)
  | matcherV {ρm cls τ} : VShape SD (.matcherV ρm cls) (.matcher τ)
  | something {τ} : VShape SD .something (.matcher τ)
  | matcherTuple {vs τ} : VShape SD (.tuple vs) (.matcher τ)   -- 積マッチャー
  | slotAny {v τp τt} : VShape SD v (.slot τp τt)              -- スロット型の値

/-! ## PP / PD 判定 (付録 A Fig 5) -/

mutual
/-- ⊢ pp : PPPattern τ ⇝ 対の列 ; Δ(各対は(構造 ▷ 標的))。
    PP-Con/PP-Tuple の「同じ頭・新しい葉」premise は、
    結論の各対の構造成分を標的成分の改名として与える形で表す。 -/
inductive PPTy (SP : SigP) : PPat → Ty → List (Ty × Ty) → BindCtx → Prop where
  | hole {τ a} :                                       -- PP-Hole($ の構造添字は裸変数)
      PPTy SP .hole τ [(.var a, τ)] []
  | wild {τ} :                                         -- PP-Wild
      PPTy SP .wild τ [] []
  | pval {y τ} :                                       -- PP-Val
      PPTy SP (.pval y) τ [] [(y, τ)]
  | ctor {c sig ts pps pairs pairs' Δ} :               -- PP-Con
      List.find? (fun pr => pr.1 == c) SP = some (c, sig) →
      PPTys SP pps (sig.args.map (Ty.instSig ts)) pairs Δ →
      pairs.length = pairs'.length →
      (∀ pr ∈ pairs.zip pairs',
        pr.1.2 = pr.2.2 ∧ FreshLike pr.1.2 pr.2.1) →   -- 構造成分 := 標的の fresh 改名
      PPTy SP (.ctor c pps) (Ty.instSig ts sig.res) pairs' Δ
  | tuple {pps τs pairs pairs' Δ} :                    -- PP-Tuple
      PPTys SP pps τs pairs Δ →
      pairs.length = pairs'.length →
      (∀ pr ∈ pairs.zip pairs',
        pr.1.2 = pr.2.2 ∧ FreshLike pr.1.2 pr.2.1) →
      PPTy SP (.tuple pps) (.prod τs) pairs' Δ

inductive PPTys (SP : SigP) : List PPat → List Ty → List (Ty × Ty) → BindCtx → Prop where
  | nil : PPTys SP [] [] [] []
  | cons {pp τ pairs Δ pps τs pairss Δs} :
      PPTy SP pp τ pairs Δ →
      PPTys SP pps τs pairss Δs →
      PPTys SP (pp :: pps) (τ :: τs) (pairs ++ pairss) (Δ ++ Δs)
end

mutual
/-- ⊢ dp : PDPattern τ ⇝ Γ -/
inductive PDTy (SD : SigD) : DPat → Ty → List (String × Ty) → Prop where
  | var {z τ} : PDTy SD (.var z) τ [(z, τ)]            -- PD-Var
  | wild {τ} : PDTy SD .wild τ []                      -- PD-Wild
  | ctor {C sig ts dps Γs} :                           -- PD-Con
      List.find? (fun pr => pr.1 == C) SD = some (C, sig) →
      PDTys SD dps (sig.args.map (Ty.instSig ts)) Γs →
      PDTy SD (.ctor C dps) (Ty.instSig ts sig.res) Γs
  | tuple {dps τs Γs} :                                -- PD-Tuple
      PDTys SD dps τs Γs →
      PDTy SD (.tuple dps) (.prod τs) Γs

inductive PDTys (SD : SigD) : List DPat → List Ty → List (String × Ty) → Prop where
  | nil : PDTys SD [] [] []
  | cons {dp τ Γ dps τs Γs} :
      PDTy SD dp τ Γ →
      PDTys SD dps τs Γs →
      PDTys SD (dp :: dps) (τ :: τs) (Γ ++ Γs)
end

/-! ## マッチャー整合性 (Definition 4.2、型付け非依存部分) -/

/-- Def 4.2 のうち (1c) arm exhaustiveness・(2) catch-all・(3) Coverage。
    (1a)(1b) の型付け条件は `HasTy.matcherE` の premise が担う。 -/
structure ConsistentClauses (SD : SigD) (SP : SigP)
    (cls : List Clause) (τ : Ty) : Prop where
  /-- (3) Coverage:τ の頭型構成子の全パターン構成子に一般形節がある -/
  coverage : ∀ pr ∈ SP, Ty.headMatches pr.2.res τ →
    ∃ M arms, (generalPP pr.1 pr.2.args.length, M, arms) ∈ cls
  /-- (3) 積型の Coverage:一般タプル節 ($, …, $) がある -/
  coverageProd : ∀ τs, τ = Ty.prod τs →
    ∃ M arms, (PPat.tuple (List.replicate τs.length .hole), M, arms) ∈ cls
  /-- (2) catch-all 節 ($ as M with $tgt → N) がある -/
  catchall : ∃ M x N, (PPat.hole, M, [(DPat.var x, N)]) ∈ cls
  /-- (1c) arm exhaustiveness:各節のアームは τ の全値を覆う(意味的定式化) -/
  armExh : ∀ cl ∈ cls, ∀ v, VShape SD v τ →
    ∃ arm ∈ cl.2.2, (pdMatch arm.1 v).isSome
  /-- 節の pp 値パターン束縛名は相異(⋃ᵢ Δᵢ が直和;Def 4.2 の暗黙条件) -/
  ppBindNodup : ∀ cl ∈ cls, ∀ {τ' : Ty} {pairs : List (Ty × Ty)} {Δ : BindCtx},
    PPTy SP cl.1 τ' pairs Δ → (Δ.map (·.1)).Nodup
  /-- アームの dp 束縛名は相異(⋃ᵢ Γᵢ が直和;同上) -/
  armBindNodup : ∀ cl ∈ cls, ∀ arm ∈ cl.2.2,
    ∀ {τ' : Ty} {Γij : List (String × Ty)},
    PDTy SD arm.1 τ' Γij → (Γij.map (·.1)).Nodup
  -- 値パターンパターンの捕捉(#$y が穴の後ろに立つ節、例:sortedList の
  -- ピボット節)自体は許される。捕捉された式は原子の環境で先に評価される
  -- ため、その型付け条件(原子入力文脈で型付くこと=値パターンスコープ条件)
  -- は使用点ごとの条件であり、WT-ATOM の vp-scoped 前提(WellTyped.lean)が担う。

/-! ## 式・パターンの型判定 (Fig 4) -/

mutual
/-- 式の型判定 Γ ⊢ e : τ -/
inductive HasTy (SD : SigD) (SP : SigP) (SF : SigF) : TyCtx → Expr → Ty → Prop where
  | var {Γ x σ τ} :
      TyCtx.find? Γ x = some σ →
      σ.Inst τ →
      HasTy SD SP SF Γ (.var x) τ
  | lam {Γ x e τ₁ τ₂} :
      HasTy SD SP SF ((x, .mono τ₁) :: Γ) e τ₂ →
      HasTy SD SP SF Γ (.lam x e) (.fn τ₁ τ₂)
  | fixE {Γ f x e τ₁ τ₂} :        -- トップレベル再帰(§3.1;単相再帰)
      HasTy SD SP SF ((x, .mono τ₁) :: (f, .mono (.fn τ₁ τ₂)) :: Γ) e τ₂ →
      HasTy SD SP SF Γ (.fix f x e) (.fn τ₁ τ₂)
  | app {Γ e₁ e₂ τ₁ τ₂} :
      HasTy SD SP SF Γ e₁ (.fn τ₁ τ₂) →
      HasTy SD SP SF Γ e₂ τ₁ →
      HasTy SD SP SF Γ (.app e₁ e₂) τ₂
  | lit {Γ n} :
      HasTy SD SP SF Γ (.lit n) .int
  | tuple {Γ es τs} :
      es.length = τs.length →
      (∀ pr ∈ es.zip τs, HasTy SD SP SF Γ pr.1 pr.2) →
      HasTy SD SP SF Γ (.tuple es) (.prod τs)
  | ctor {Γ c es sig ts} :
      List.find? (fun pr => pr.1 == c) SD = some (c, sig) →
      es.length = sig.args.length →
      (∀ pr ∈ es.zip (sig.args.map (Ty.instSig ts)), HasTy SD SP SF Γ pr.1 pr.2) →
      HasTy SD SP SF Γ (.ctor c es) (Ty.instSig ts sig.res)
  | primAppend {Γ e₁ e₂ τ} :
      HasTy SD SP SF Γ e₁ (Ty.listT τ) →
      HasTy SD SP SF Γ e₂ (Ty.listT τ) →
      HasTy SD SP SF Γ (.prim .append [e₁, e₂]) (Ty.listT τ)
  | primSplits {Γ e τ} :
      HasTy SD SP SF Γ e (Ty.listT τ) →
      HasTy SD SP SF Γ (.prim .splits [e])
        (Ty.listT (.prod [Ty.listT τ, Ty.listT τ]))
  | letE {Γ x e₁ e₂ τ₁ τ L} :     -- EV-LET に対応する let 一般化(HM)
      HasTy SD SP SF Γ e₁ τ₁ →
      (∀ a ∈ L, a ∉ ftvCtx Γ) →
      HasTy SD SP SF ((x, ⟨L, τ₁⟩) :: Γ) e₂ τ →
      HasTy SD SP SF Γ (.letE x e₁ e₂) τ
  | something {Γ τ} :             -- T-SOME(α fresh の宣言的読み = 任意の τ)
      HasTy SD SP SF Γ .something (.matcher τ)
  | matchAll {Γ e_t e_m p body τ_t τ_p Δ τ_r} :        -- T-MATCHALL
      HasTy SD SP SF Γ e_t τ_t →
      PatTy SD SP SF Γ [] [] p τ_p τ_t Δ →
      HasTy SD SP SF Γ e_m (.slot τ_p τ_t) →
      HasTy SD SP SF (BindCtx.toCtx Δ ++ Γ) body τ_r →
      HasTy SD SP SF Γ (.matchAll e_t e_m p body) (Ty.listT τ_r)
  | matcherE {Γ cls τ} :          -- T-MATCHER
      ClausesTy SD SP SF Γ τ cls →
      ConsistentClauses SD SP cls τ →
      HasTy SD SP SF Γ (.matcher cls) (.matcher τ)
  | coerceMatcherToSlot {Γ e τm τm' τp τt} :           -- COERCE-MATCHER-TO-SLOT(双対検査)
      HasTy SD SP SF Γ e (.matcher τm) →
      RenamesTo τm τm' →                               -- τm' = fresh_rename(τm)
      OneWay τp τm' →                                  -- 構造:τm' ⊑ τp
      Unifiable τm τt →                                -- 標的:τm ~ τt
      HasTy SD SP SF Γ e (.slot τp τt)
  | coerceTupleMatcher {Γ e τs} :                      -- COERCE-TUPLE-MATCHER
      HasTy SD SP SF Γ e (.prod (τs.map Ty.matcher)) →
      HasTy SD SP SF Γ e (.matcher (.prod τs))
  | coerceSlotTuple {Γ e} {prs : List (Ty × Ty)} :     -- COERCE-SLOT-TUPLE
      HasTy SD SP SF Γ e (.prod (prs.map fun pr => Ty.slot pr.1 pr.2)) →
      HasTy SD SP SF Γ e (.slot (.prod (prs.map (·.1))) (.prod (prs.map (·.2))))

/-- パターンの双対判定 Γ;Δ ⊢ p : Pattern (τp ▷ τt) ; Δ'(Φ は仮引数文脈) -/
inductive PatTy (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → PatParamCtx → BindCtx → Pattern → Ty → Ty → BindCtx → Prop where
  | pvar {Γ Φ Δ x τp β} :                              -- PAT-VAR
      (∀ pr ∈ Δ, pr.1 ≠ x) →
      PatTy SD SP SF Γ Φ Δ (.pvar x) τp β (Δ ++ [(x, β)])
  | wild {Γ Φ Δ τp β} :                                -- PAT-WILD
      PatTy SD SP SF Γ Φ Δ .wild τp β Δ
  | pval {Γ Φ Δ e τp τe} :                             -- PAT-VALUE
      HasTy SD SP SF (BindCtx.toCtx Δ ++ Γ) e τe →
      PatTy SD SP SF Γ Φ Δ (.pval e) τp τe Δ
  | embed {Γ Φ Δ x pr} :                               -- PAT-EMBED
      List.find? (fun q => q.1 == x) Φ = some (x, pr) →
      PatTy SD SP SF Γ Φ Δ (.embed x) pr.1 pr.2 Δ
  | pctor {Γ Φ Δ c sig ss ts ps duals Δ'} :            -- PAT-CON
      List.find? (fun pr => pr.1 == c) SP = some (c, sig) →
      PatTys SD SP SF Γ Φ Δ ps duals Δ' →
      duals.map (·.1) = sig.args.map (Ty.instSig ss) →   -- 構造側インスタンス化
      duals.map (·.2) = sig.args.map (Ty.instSig ts) →   -- 標的側インスタンス化(独立)
      PatTy SD SP SF Γ Φ Δ (.pctor c ps)
        (Ty.instSig ss sig.res) (Ty.instSig ts sig.res) Δ'
  | pand {Γ Φ Δ p₁ p₂ τp τt Δ₁ Δ₂} :                   -- PAT-AND
      PatTy SD SP SF Γ Φ Δ p₁ τp τt Δ₁ →
      PatTy SD SP SF Γ Φ Δ₁ p₂ τp τt Δ₂ →
      PatTy SD SP SF Γ Φ Δ (.pand p₁ p₂) τp τt Δ₂
  | por {Γ Φ Δ p₁ p₂ τp τt Δ'} :                       -- PAT-OR
      PatTy SD SP SF Γ Φ Δ p₁ τp τt Δ' →
      PatTy SD SP SF Γ Φ Δ p₂ τp τt Δ' →
      PatTy SD SP SF Γ Φ Δ (.por p₁ p₂) τp τt Δ'
  | papp {Γ Φ Δ f sig ss ts qs duals Δ'} :             -- PAT-APP(双対スキームの独立インスタンス化)
      List.find? (fun pr => pr.1 == f) SF = some (f, sig) →
      PatTys SD SP SF Γ Φ Δ qs duals Δ' →
      duals.map (·.1) = sig.argDuals.map (fun pr => Ty.instSig ss pr.1) →
      duals.map (·.2) = sig.argDuals.map (fun pr => Ty.instSig ts pr.2) →
      PatTy SD SP SF Γ Φ Δ (.papp f qs)
        (Ty.instSig ss sig.resDual.1) (Ty.instSig ts sig.resDual.2) Δ'
  | ptuple {Γ Φ Δ ps duals Δ'} :                       -- PAT-TUPLE
      PatTys SD SP SF Γ Φ Δ ps duals Δ' →
      PatTy SD SP SF Γ Φ Δ (.ptuple ps)
        (.prod (duals.map (·.1))) (.prod (duals.map (·.2))) Δ'

/-- パターン列の左→右 Δ スレッディング -/
inductive PatTys (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → PatParamCtx → BindCtx → List Pattern → List (Ty × Ty) → BindCtx → Prop where
  | nil {Γ Φ Δ} : PatTys SD SP SF Γ Φ Δ [] [] Δ
  | cons {Γ Φ Δ Δ₁ Δ' p ps pr duals} :
      PatTy SD SP SF Γ Φ Δ p pr.1 pr.2 Δ₁ →
      PatTys SD SP SF Γ Φ Δ₁ ps duals Δ' →
      PatTys SD SP SF Γ Φ Δ (p :: ps) (pr :: duals) Δ'

/-- T-MATCHER の 1 節分の型付け(Def 4.2(1a)(1b)(4)):
    pp 判定・次マッチャーのスロット型・アーム本体の型。
    (∃ を構成子引数にスコーレム化した形;kernel の nested inductive 制限のため。) -/
inductive ClauseTy (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → Ty → Clause → Prop where
  | mk {Γ τ pp M arms pairs Δi Ms} :
      PPTy SP pp τ pairs Δi →
      decomposeME M pairs.length = some Ms →
      (∀ pr ∈ Ms.zip pairs,
        HasTy SD SP SF Γ pr.1 (.slot pr.2.1 pr.2.2)) →        -- (1a) 各穴のスロット
      ArmsTy SD SP SF Γ τ Δi (Ty.listT (prodK (pairs.map (·.2)))) arms →
      ClauseTy SD SP SF Γ τ (pp, M, arms)

/-- 節のアーム列の型付け:各アーム dp → N について
    dp の束縛 Γij のもとで N : [(標的型の積)](Def 4.2(1b))。 -/
inductive ArmsTy (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → Ty → BindCtx → Ty → List (DPat × Expr) → Prop where
  | nil {Γ τ Δi τres} : ArmsTy SD SP SF Γ τ Δi τres []
  | cons {Γ τ Δi τres dp N arms Γij} :
      PDTy SD dp τ Γij →
      HasTy SD SP SF (BindCtx.toCtx Γij ++ BindCtx.toCtx Δi ++ Γ) N τres →
      ArmsTy SD SP SF Γ τ Δi τres arms →
      ArmsTy SD SP SF Γ τ Δi τres ((dp, N) :: arms)

/-- マッチャー節列の型付け -/
inductive ClausesTy (SD : SigD) (SP : SigP) (SF : SigF) :
    TyCtx → Ty → List Clause → Prop where
  | nil {Γ τ} : ClausesTy SD SP SF Γ τ []
  | cons {Γ τ cl cls} :
      ClauseTy SD SP SF Γ τ cl →
      ClausesTy SD SP SF Γ τ cls →
      ClausesTy SD SP SF Γ τ (cl :: cls)
end

/-! ## パターン関数定義の整型性 (PATFUN-DEF) -/

/-- PATFUN-DEF:Σ_F に記録された双対スキームが本体導出で実現され、
    線形性側条件(各 ~xᵢ が宣言順にちょうど 1 回、or 選択肢の外)を満たす。 -/
structure PatFunWF (SD : SigD) (SP : SigP) (SF : SigF) (Γ : TyCtx)
    (sig : PatFunSig) : Prop where
  arity     : sig.params.length = sig.argDuals.length
  linearity : sig.body.embedVars = sig.params
  noOr      : sig.body.noEmbedInOr = true
  bodyTyped : ∃ Δ',
    PatTy SD SP SF Γ (sig.params.zip sig.argDuals) [] sig.body
      sig.resDual.1 sig.resDual.2 Δ'

/-- Σ_F 全体の整型性 -/
def SigFWF (SD : SigD) (SP : SigP) (SF : SigF) (Γ : TyCtx) : Prop :=
  ∀ pr ∈ SF, PatFunWF SD SP SF Γ pr.2

/-! ## 構成子シグネチャの整形性(Def 4.1/宣言の暗黙条件)

宣言 `inductive pattern T α₁ ⋯ αₙ := c τ⃗ | …` / `data T α⃗ := C τ⃗ | …` から
得られるシグネチャは、結果型が型構成子の全変数適用 `T α₁ ⋯ αₙ` で、
引数型の自由変数は宣言パラメタに含まれる。メタ理論はこの形を使う
(例:結果型のインスタンス化が引数型のインスタンス化を一意に決める)。 -/

def CtorSigWF (sig : CtorSig) : Prop :=
  (∃ n, sig.res = .data n ((List.range sig.nparams).map .var)) ∧
  ∀ a ∈ ftvList sig.args, a < sig.nparams

def SigPWF (SP : SigP) : Prop := ∀ pr ∈ SP, CtorSigWF pr.2
def SigDWF (SD : SigD) : Prop := ∀ pr ∈ SD, CtorSigWF pr.2

/-- 整形シグネチャでは、結果型のインスタンス化の一致が
    引数型のインスタンス化の一致を導く(Lem 5.4 の PP 側と PatTy 側の整列に使用)。 -/
theorem instSig_args_agree {sig : CtorSig} (hwf : CtorSigWF sig)
    {ts ts' : List Ty}
    (hres : Ty.instSig ts sig.res = Ty.instSig ts' sig.res) :
    ∀ τa ∈ sig.args, Ty.instSig ts τa = Ty.instSig ts' τa := by
  obtain ⟨⟨n, hres_eq⟩, hargs⟩ := hwf
  intro τa hτa
  -- 結果型の等式から、パラメタ変数 i < nparams 上で両代入が一致する
  have hvar : ∀ i < sig.nparams,
      Ty.instSig ts (.var i) = Ty.instSig ts' (.var i) := by
    intro i hi
    rw [hres_eq] at hres
    simp only [Ty.instSig, Ty.applyTS, applyTSList] at hres
    have := congrArg (fun t => match t with
      | Ty.data _ ts => ts
      | _ => []) hres
    simp only at this
    have hmap :
        (((List.range sig.nparams).map Ty.var).map
          (Ty.applyTS ((List.range ts.length).zip ts))) =
        (((List.range sig.nparams).map Ty.var).map
          (Ty.applyTS ((List.range ts'.length).zip ts'))) := by
      have h1 : ∀ (θ : TySubst) (l : List Ty),
          applyTSList θ l = l.map (Ty.applyTS θ) := by
        intro θ l
        induction l with
        | nil => rfl
        | cons t l ih => simp [applyTSList, ih]
      rw [← h1, ← h1]
      exact this
    have := List.map_inj_left.mp
      (by simpa [List.map_map] using hmap) i (List.mem_range.mpr hi)
    simpa [Ty.instSig] using this
  -- 引数型の自由変数はすべてパラメタなので合同性で結論
  simp only [Ty.instSig]
  exact applyTS_congr τa fun a ha => by
    have := hvar a (hargs a (by
      have : a ∈ Ty.ftv τa := ha
      exact mem_ftvList_of_mem hτa this))
    simpa [Ty.instSig, Ty.applyTS] using this

end TypePM
