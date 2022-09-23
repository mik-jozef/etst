open Classical

def Set (T : Type) := T → Prop

instance: Membership T (Set T) where
  mem := fun (t: T) (s: Set T) => s t

-- Does not work... Cannot use sets as types with this.
--instance: Coe (Set T) Type where
--  coe s := { t: T // t ∈ s }


-- TODO delete? Semantically, there is a difference, but
-- character-count-wise, it's not simpler than the function
-- type. TODO do I even use it?
-- 
-- def Family {D: Type} (T: Type) := D → T

namespace Set
  -- Should the implication be turned into an equivalence?
  def isFinite (s: Set T): Prop := ∃ l: List T, ∀ t: T, t ∈ s → t ∈ l
  
  def union {D: Type} {T: Type}: (D → Set T) → Set T :=
    fun (family: D → Set T) (t: T) => ∃ d: D, family d t
end Set

def FinSet (T: Type) := { s: Set T // Set.isFinite s }



def Signature := (Op: Type) × (Op → Nat)

def sigOp (Op: Type) := { s: Signature // s.fst = Op }
def arity {Op: Type} (op: Op) (s: sigOp Op): Nat :=
  s.val.snd op


inductive NatOp
  | zero
  | succ
  | plus

def natAr: NatOp → Nat
  | NatOp.zero => 0
  | NatOp.succ => 1
  | NatOp.plus => 2

def natSig: Signature := ⟨NatOp, natAr⟩


inductive PairOp where
  | zero
  | pair

def pairAr: PairOp → Nat
  | PairOp.zero => 0
  | PairOp.pair => 2

def pairSig: Signature := ⟨PairOp, pairAr⟩



def Variable := Nat
def VarSet := Set Variable
def FinVarSet := FinSet Variable

def varAdd (Var: VarSet) (x: Variable): VarSet :=
  fun z => Var z ∨ z = x

mutual
  inductive VectExpr (s: Signature): (Var: VarSet) → Nat → Type
    | nil: VectExpr s Var 0
    | cons: Expr s Var → {n: Nat} → VectExpr s Var (n+1)
  
  inductive Expr (s: Signature): (Var: VarSet) → Type
    | var: { x: Variable // Var x } → Expr s Var
    | opApp:
        (op: s.fst) →
        VectExpr s Var (arity op ⟨s, rfl⟩) →
        Expr s Var
    | un: Expr s Var → Expr s Var → Expr s Var
    | ir: Expr s Var → Expr s Var → Expr s Var
    | cpl: Expr s Var → Expr s Var
    | Un: (x: Variable) → Expr s (varAdd Var x) → Expr s Var
    | Ir: (x: Variable) → Expr s (varAdd Var x) → Expr s Var
end

def FamExpr (s: Signature) (Var: VarSet) := { x: Variable // Var x } → Expr s Var

namespace FamExpr
  def isFinite (_: FamExpr s Var): Prop := Set.isFinite Var
  
  noncomputable def union
    {s: Signature}
    --{D: Type}
    {V: /-D-/ Nat → VarSet}
    {fin: ∀ n: Nat, Set.isFinite (V n)}
    -- I suppose an arbitrary domain cannot work constructively, because
    -- given a variable x, `union` does not known under which index `d: D`
    -- to look to find the corresponding expression. Am I right?
    -- Also, how would I implement this function classically?
    --(family: (d: D) → FamExpr s (V d))
    (family: (n: Nat) → FamExpr s (V n))
  : FamExpr s (Set.union V)
  :=
    fun x: { x: Variable // x ∈ Set.union V } =>
      find x 0
    where
      find (x: Nat) (n: Nat): /-Expr s (Set.union V)-/ Nat :=
        if V n x then 0 else 0
end FamExpr

def DefList (s: Signature) (Var: VarSet) := { fe: FamExpr s //  }

































-- How to conditionally call `foo x` if `foo` is defined on `x: Nat`?
def foo (_: { n: Nat // n = 3 }) := 42

--noncomputable def t (x: Nat) (): Nat := if x ∈ foo then foo x else 0

noncomputable def t (x: Nat) (s: Set Nat): Nat := if x ∈ s then 1 else 0


-- How to implement this?
--uncomputable def finSetNatToList (s: Set Nat) (fin: isFinite s): { l: List Nat // ∀ n: Nat, n ∈ l ↔ n ∈ s } :=
  --let ex : ∃ l: List Nat, ∀ n: Nat, n ∈ s → n ∈ l := fin;
  --let ⟨l, p⟩ := ex; -- Lol no. Cannot extract data from Prop.
  --0 asdf
  



