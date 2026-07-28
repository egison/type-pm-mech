/-!
# λ_PM の構文 (論文 §3.1, Fig 1)

型 τ・式 e・パターン p・primitive-pattern pattern pp・primitive data pattern dp・
値 v・マッチング原子/木/スタック/状態、および宣言環境 Σ_D / Σ_P / Σ_F。

設計判断(README も参照):
* 変数は文字列名。意味論は環境ベースの big-step で項への代入が無いため、
  de Bruijn 化は不要(type-tensor-mech と異なる点)。
* 型変数は `Nat` 名。
* `Pattern τ` は型ではなく判断形式として扱う(式が `Pattern` 型を持つことはない)。
  型文法に載るのは `Matcher τ` と `MatcherSlot τp τt` のみ。
* リスト型 `[τ]` は名前付き型構成子 `Ty.data "List" [τ]` の略記
  (`[]`/`::` は Σ_D の普通のデータ構成子)。
* 再帰(論文の「トップレベル定義は再帰的」)は `Expr.fix` で表す。
  自己参照マッチャー `multiset` はこれで書ける。
* 分解関数の本体で使うライブラリ関数(`++`、連続分割の列挙)は
  プリミティブ `PrimOp` として与える(論文では任意の式;ここでは δ 規則)。
-/

namespace TypePM

/-- 型変数名 -/
abbrev TyVar := Nat

/-- 型 τ (Fig 1)。`data n ts` は名前付き型構成子(`List`、`Tile` など)。 -/
inductive Ty where
  | var     : TyVar → Ty
  | int     : Ty
  | bool    : Ty
  | data    : String → List Ty → Ty
  | prod    : List Ty → Ty
  | fn      : Ty → Ty → Ty
  | matcher : Ty → Ty
  | slot    : Ty → Ty → Ty      -- MatcherSlot τp τt
deriving Repr

/-- リスト型 [τ] の略記 -/
def Ty.listT (τ : Ty) : Ty := Ty.data "List" [τ]

/-- 型スキーム σ = ∀ binders. body (let 一般化から生じる) -/
structure Scheme where
  binders : List TyVar
  body    : Ty
deriving Repr

/-- 単相スキーム -/
def Scheme.mono (τ : Ty) : Scheme := ⟨[], τ⟩

/-- primitive-pattern pattern pp (Fig 1)。`pval y` は #$y。 -/
inductive PPat where
  | hole  : PPat                       -- $
  | wild  : PPat                       -- _
  | pval  : String → PPat              -- #$y
  | ctor  : String → List PPat → PPat
  | tuple : List PPat → PPat
deriving Repr

/-- primitive data pattern dp (Fig 1) -/
inductive DPat where
  | var   : String → DPat              -- $z
  | wild  : DPat                       -- _
  | ctor  : String → List DPat → DPat
  | tuple : List DPat → DPat
deriving Repr

/-- 分解関数本体用のプリミティブ(README 設計判断 6) -/
inductive PrimOp where
  | append   -- [a] → [a] → [a]
  | splits   -- [a] → [([a] × [a])]  連続分割の列挙(list の ++ 節)
deriving Repr

mutual
/-- 式 e (Fig 1)。`match` は `matchAll` への糖衣(§3.1)のため省く。 -/
inductive Expr where
  | var       : String → Expr
  | lam       : String → Expr → Expr
  | fix       : String → String → Expr → Expr   -- 再帰関数 fix f x. e
  | app       : Expr → Expr → Expr
  | lit       : Int → Expr
  | tuple     : List Expr → Expr
  | ctor      : String → List Expr → Expr       -- C e₁ ⋯ e_k ([]/:: を含む)
  | prim      : PrimOp → List Expr → Expr
  | letE      : String → Expr → Expr → Expr
  | something : Expr
  | matcher   : List (PPat × Expr × List (DPat × Expr)) → Expr
  | matchAll  : Expr → Expr → Pattern → Expr → Expr  -- matchAll e_t as e_m with p → e

/-- パターン p (Fig 1)。`embed x` は変数パターン ~x(パターン関数本体中)。 -/
inductive Pattern where
  | pvar   : String → Pattern                -- $x
  | wild   : Pattern                         -- _
  | pval   : Expr → Pattern                  -- #e
  | embed  : String → Pattern                -- ~x
  | pctor  : String → List Pattern → Pattern -- c p₁ ⋯ p_k
  | pand   : Pattern → Pattern → Pattern     -- p₁ & p₂
  | por    : Pattern → Pattern → Pattern     -- p₁ | p₂
  | papp   : String → List Pattern → Pattern -- f p₁ ⋯ p_k
  | ptuple : List Pattern → Pattern          -- (p₁, …, p_k)
end

/-- マッチャー節 (pp, M, [(dp, N)]) -/
abbrev Clause := PPat × Expr × List (DPat × Expr)

/-- 値 v (Fig 1)。closure の第 1 成分は再帰用の自己名(`Expr.fix` 由来)。 -/
inductive Value where
  | lit       : Int → Value
  | ctor      : String → List Value → Value
  | tuple     : List Value → Value
  | closure   : Option String → List (String × Value) → String → Expr → Value
  | matcherV  : List (String × Value) → List Clause → Value
  | something : Value

mutual
/-- pp が p と形状一致する範囲で、#$y 位置に捕捉される p 側値パターンの
    式を左→右で集める(PPP-VAL の評価対象)。
    Def 4.2(4):捕捉された式は**原子の環境で先に**評価されるので、
    原子より前の束縛は使えるが、同じ原子内の左の穴の束縛は使えない
    (機械化の発見その 3;WT-ATOM の vp-scoped 前提 = 値パターンスコープ条件)。 -/
def capturedExprs : PPat → Pattern → List Expr
  | .pval _, .pval M => [M]
  | .ctor _ pps, .pctor _ ps => capturedExprsList pps ps
  | .tuple pps, .ptuple ps => capturedExprsList pps ps
  | _, _ => []

def capturedExprsList : List PPat → List Pattern → List Expr
  | pp :: pps, p :: ps => capturedExprs pp p ++ capturedExprsList pps ps
  | _, _ => []
end

/-- 実行時環境 ρ / 中間束縛の代入 θ(どちらも先頭が新しい) -/
abbrev Env := List (String × Value)
abbrev Subst := List (String × Value)

def Env.find? (ρ : Env) (x : String) : Option Value :=
  (List.find? (fun p => p.1 == x) ρ).map (·.2)

/-- マッチング原子 p ~_m v -/
structure Atom where
  p : Pattern
  m : Value
  v : Value

/-- パターン環境 Π : ~xᵢ ↦ qᵢ(宣言順を保持) -/
abbrev PiEnv := List (String × Pattern)

/-- マッチング木 t = 原子 | MNode(S, ρ_f, θ_f, Π) -/
inductive Tree where
  | atom  : Atom → Tree
  | mnode : List Tree → Env → Subst → PiEnv → Tree

/-- マッチング状態 s = (S, ρ, θ) -/
structure MState where
  S : List Tree
  ρ : Env
  θ : Subst

/-- データ構成子/パターン構成子のシグネチャ。
    型変数 0..nparams-1 が束縛変数(インスタンス化は `Ty.instSig`)。 -/
structure CtorSig where
  nparams : Nat
  args    : List Ty
  res     : Ty
deriving Repr

/-- パターン関数のシグネチャ(記録された双対スキーム、§4.3)。
    `argDuals` は (πᵢ, τᵢ)、`resDual` は (τ_p^f, τ)。 -/
structure PatFunSig where
  nparams  : Nat
  params   : List String
  argDuals : List (Ty × Ty)
  resDual  : Ty × Ty
  body     : Pattern

abbrev SigD := List (String × CtorSig)
abbrev SigP := List (String × CtorSig)
abbrev SigF := List (String × PatFunSig)

/-! ## リスト値のヘルパ -/

/-- Lean のリストから λ_PM のリスト値へ -/
def mkListV : List Value → Value
  | []      => .ctor "nil" []
  | v :: vs => .ctor "cons" [v, mkListV vs]

/-- λ_PM のリスト値から Lean のリストへ -/
def listOfV : Value → Option (List Value)
  | .ctor "nil" []        => some []
  | .ctor "cons" [v, vs]  => (listOfV vs).map (v :: ·)
  | _                     => none

/-- k 成分タプルへの分解。k = 1 のとき値そのもの、その他はタプル値(§4.5 の 1(b))。 -/
def decodeTuple (k : Nat) (v : Value) : Option (List Value) :=
  if k == 1 then some [v]
  else match v with
    | .tuple vs => if vs.length == k then some vs else none
    | _         => none

/-! ## パターンの変数出現(束縛契約と MNode 接尾辞不変量に使用) -/

mutual
/-- ~x 出現の左→右リスト(MNode 接尾辞不変量・線形性検査に使用) -/
def Pattern.embedVars : Pattern → List String
  | .pvar _    => []
  | .wild      => []
  | .pval _    => []
  | .embed x   => [x]
  | .pctor _ ps => embedVarsList ps
  | .pand p₁ p₂ => p₁.embedVars ++ p₂.embedVars
  | .por p₁ p₂  => p₁.embedVars ++ p₂.embedVars
  | .papp _ ps  => embedVarsList ps
  | .ptuple ps  => embedVarsList ps

def embedVarsList : List Pattern → List String
  | []      => []
  | p :: ps => p.embedVars ++ embedVarsList ps
end

mutual
/-- $x 出現の左→右リスト(binds の名前部分、§3.2) -/
def Pattern.patVars : Pattern → List String
  | .pvar x    => [x]
  | .wild      => []
  | .pval _    => []
  | .embed _   => []
  | .pctor _ ps => patVarsList ps
  | .pand p₁ p₂ => p₁.patVars ++ p₂.patVars
  | .por p₁ _   => p₁.patVars          -- binds(p₁|p₂) = binds(p₁) (§3.2)
  | .papp _ ps  => patVarsList ps
  | .ptuple ps  => patVarsList ps

def patVarsList : List Pattern → List String
  | []      => []
  | p :: ps => p.patVars ++ patVarsList ps
end

mutual
/-- or 選択肢の内側に ~x が現れない(PATFUN-DEF 線形性の側条件) -/
def Pattern.noEmbedInOr : Pattern → Bool
  | .pvar _    => true
  | .wild      => true
  | .pval _    => true
  | .embed _   => true
  | .pctor _ ps => noEmbedInOrList ps
  | .pand p₁ p₂ => p₁.noEmbedInOr && p₂.noEmbedInOr
  | .por p₁ p₂  => p₁.embedVars.isEmpty && p₂.embedVars.isEmpty
                   && p₁.noEmbedInOr && p₂.noEmbedInOr
  | .papp _ ps  => noEmbedInOrList ps
  | .ptuple ps  => noEmbedInOrList ps

def noEmbedInOrList : List Pattern → Bool
  | []      => true
  | p :: ps => p.noEmbedInOr && noEmbedInOrList ps
end

/-!
マッチング木スタックの ~x 出現(左→右)。
MNode 内部の ~y は自分の Π で解決されるが、その解決先 q = Π(y) は
MS-MNODE-VARPAT で外側のスタックに押し出されるため、
q の中の ~x 出現は外側の列に寄与する。
-/
mutual
def treeEmbedOccs : Tree → List String
  | .atom a => a.p.embedVars
  | .mnode S _ _ piE =>
      (stackEmbedOccs S).flatMap fun y =>
        match List.find? (fun p => p.1 == y) piE with
        | some (_, q) => q.embedVars
        | none        => [y]

def stackEmbedOccs : List Tree → List String
  | []     => []
  | t :: S => treeEmbedOccs t ++ stackEmbedOccs S
end

/-!
スタック中の全パターン(と Π の実引数パターン)が `noEmbedInOr` であること。
~x 出現列が or 分岐で失われない(= WT-MNODE の接尾辞不変量が 1 ステップで
保存される)ための線形性側条件のスタック版。
-/
mutual
def treeNoOr : Tree → Bool
  | .atom a => a.p.noEmbedInOr
  | .mnode S _ _ piE =>
      stackNoOr S && piE.all (fun pr => pr.2.noEmbedInOr)

def stackNoOr : List Tree → Bool
  | []     => true
  | t :: S => treeNoOr t && stackNoOr S
end

end TypePM
