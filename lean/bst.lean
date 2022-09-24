/-
  Code style: prefer no tactics.
-/

open Classical

noncomputable def choiceEx {P: T → Prop} (ex: ∃ t: T, P t): { t: T // P t } :=
  let nonempty: Nonempty { t: T // P t } :=
    match ex with
    | ⟨t, prop⟩ => ⟨t, prop⟩
  choice nonempty



-- # Chapter 0: Sets and other basic definitions
-- =============================================

-- The square less-equal relation: `x ⊑ y`.
class SqLE (α : Type u) where
  le : α → α → Prop

-- The square less-equal relation: `x ⊏ y`.
class SqLT (α : Type u) where
  lt : α → α → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt


class PartialOrder (T: Type) extends LE T, LT T where
  refl (t: T): t ≤ t
  antisymm (a b: T): a ≤ b  →  b ≤ a  →  a = b
  trans (a b c: T): a ≤ b  →  b ≤ c  →  a ≤ c
  
  lt (a b: T) := a ≤ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a < b  ↔  a ≤ b ∧ ¬ a = b

-- Can I combine PartialOrder with PartialOrderSq into one definition?
class PartialOrderSq (T: Type) extends SqLE T, SqLT T where
  refl (t: T): t ⊑ t
  antisymm (a b: T): a ⊑ b  →  b ⊑ a  →  a = b
  trans (a b c: T): a ⊑ b  →  b ⊑ c  →  a ⊑ c
  
  lt (a b: T) := a ⊑ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a ⊏ b  ↔  a ⊑ b ∧ ¬ a = b


def Set (T : Type) := T → Prop

instance: Membership T (Set T) where
  mem := fun (t: T) (s: Set T) => s t

instance: Coe (Set T) Type where
  coe s := { t: T // t ∈ s }


theorem Set.ext {a b : Set D} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


instance: LE (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

instance: PartialOrder (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  refl (_: Set D) := fun _: D => id
  
  antisymm (a b: Set D) :=
    fun (ab: a ≤ b) (ba: ∀ d: D, d ∈ b → d ∈ a) =>
      let abElem: ∀ d: D, d ∈ a ↔ d ∈ b := fun (s: D) => Iff.intro (ab s) (ba s);
      Set.ext abElem
  
  trans (a b c: Set D) := fun (ab: a ≤ b) (bc: b ≤ c) =>
    -- In general, do I prefer long and incremental and explicit proofs,
    -- or terse and unreadable monsters? I think I prefer the former.
    --
    -- fun (d: D) =>
    --   let abi: d ∈ a → d ∈ b := ab s
    --   let bci: d ∈ b → d ∈ c := bc s
    --   fun (sa: d ∈ a) => bci (abi sa)
    fun (d: D) (sa: d ∈ a) => (bc d) ((ab d) sa)
  
  ltIffLeNotEq _ _ := Iff.intro id id

namespace Set
  def isFinite (s: Set D): Prop := ∃ l: List D, ∀ t: D, t ∈ s → t ∈ l
  
  def isSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  def union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d
  
  theorem unionIsWider
    (family: Index → Set D)
    (i: Index)
  :
    isSubset (family i) (union family)
  :=
    fun (d: D) (dfi: d ∈ family i) => ⟨i, dfi⟩
  
  def binaryUnion (a b: Set D): Set D := fun d: D => a d ∨ b d
  def binaryIntersection (a b: Set D): Set D := fun d: D => a d ∧ b d
end Set

infix:50 " ⊆ " => Set.isSubset
infix:60 " ∪ " => Set.binaryUnion
infix:60 " ∩ " => Set.binaryIntersection



-- # Chapter 1: Well-founded collections
-- =====================================

structure Set3 (D: Type) where
  defMem: Set D
  posMem: Set D
  defLePos: defMem ≤ posMem

protected def Set3.eq:
  (a b: Set3 D) →
  a.defMem = b.defMem →
  a.posMem = b.posMem
→
  a = b
-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1747
| ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl


instance: LE (Set3 D) where
  le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  a.posMem ≤ b.posMem

instance: SqLE (Set3 D) where
  le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  b.posMem ≤ a.posMem


instance: PartialOrder (Set3 D) where
  refl (a: Set3 D) :=
    And.intro (PartialOrder.refl (a.defMem)) (PartialOrder.refl (a.posMem))
  
  antisymm (a b: Set3 D) (ab: a ≤ b) (ba: b ≤ a) :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.antisymm a.defMem b.defMem ab.left ba.left;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.antisymm a.posMem b.posMem ab.right ba.right;
    Set3.eq a b defEq posEq
  
  trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) :=
    And.intro
      (PartialOrder.trans a.defMem b.defMem c.defMem ab.left bc.left)
      (PartialOrder.trans a.posMem b.posMem c.posMem ab.right bc.right)
  
  ltIffLeNotEq _ _ := Iff.intro id id


instance: PartialOrderSq (Set3 D) where
  refl (a: Set3 D) :=
    And.intro (PartialOrder.refl (a.defMem)) (PartialOrder.refl (a.posMem))
  
  antisymm (a b: Set3 D) (ab: a ⊑ b) (ba: b ⊑ a) :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.antisymm a.defMem b.defMem ab.left ba.left;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.antisymm a.posMem b.posMem ba.right ab.right;
    Set3.eq a b defEq posEq
  
  trans (a b c: Set3 D) (ab: a ⊑ b) (bc: b ⊑ c) :=
    And.intro
      (PartialOrder.trans a.defMem b.defMem c.defMem ab.left bc.left)
      (PartialOrder.trans c.posMem b.posMem a.posMem bc.right ab.right)
  
  ltIffLeNotEq _ _ := Iff.intro id id


-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
def Signature := (Op: Type) × (Op → Type)
def Op (s: Signature) := s.fst

def SigOp (Op: Type) := { s: Signature // s.fst = Op }
def arity {Op: Type} (op: Op) (s: SigOp Op): Type := s.val.snd (cast s.property.symm op)


inductive ArityZero
inductive ArityOne
| zth
inductive ArityTwo
| zth
| fst

inductive NatOp
  | zero
  | succ
  | plus

def natAr: NatOp → Type
  | NatOp.zero => ArityZero
  | NatOp.succ => ArityOne
  | NatOp.plus => ArityTwo

def natSig: Signature := ⟨NatOp, natAr⟩


inductive PairOp where
  | zero
  | pair

def pairAr: PairOp → Type
  | PairOp.zero => ArityZero
  | PairOp.pair => ArityTwo

def pairSig: Signature := ⟨PairOp, pairAr⟩



def Variable := Nat
-- Why tf is "reducible" even required? Lean, this is so fucking retarded.
@[reducible] def VarSet := Set Variable

def addVar (Var: VarSet) (x: Variable): VarSet :=
  fun z => Var z ∨ z = x

def addVarMono (Var: VarSet) (x: Variable): Var ⊆ addVar Var x :=
  fun (v: Variable) (vVar: v ∈ Var) => Or.inl vVar

def addVarId (Var: VarSet) (x: Variable) (xInVar: x ∈ Var): addVar Var x = Var :=
  Set.ext fun v: Variable =>
    Iff.intro
      (fun vInAddVar => Or.elim vInAddVar id (fun vx => vx ▸ xInVar))
      ((addVarMono Var x) v)
  

def addVarIsWider
  (Var: VarSet)
  (WiderVar: VarSet)
  (isWider: Var ⊆ WiderVar)
  (x: Variable)
:
  addVar Var x ⊆ addVar WiderVar x
:=
  fun (v: Variable) (avx: v ∈ addVar Var x) =>
    Or.elim avx
      (fun vVar: Var v => Or.inl (isWider v vVar))
      (fun vx: v = x => Or.inr vx)


inductive Expr (s: Signature): (Var: VarSet) → Type
  | var: { x: Variable // Var x } → Expr s Var
  | opApp:
      (op: s.fst) →
      (arity op ⟨s, _⟩ → Expr s Var) →
      Expr s Var
  | un: Expr s Var → Expr s Var → Expr s Var
  | ir: Expr s Var → Expr s Var → Expr s Var
  | cpl: Expr s Var → Expr s Var
  | Un: (x: Variable) → Expr s (addVar Var x) → Expr s Var
  | Ir: (x: Variable) → Expr s (addVar Var x) → Expr s Var


-- This is horrendous. Please tell me I just suck at Lean
-- and there is a much better way of doing this.
def widenExpr
  (expr: Expr s Var)
  (WiderVar: VarSet)
  (isWider: Var ⊆ WiderVar)
:
  Expr s WiderVar
:=
  match expr with
  | Expr.var ⟨x, xInVar⟩ => Expr.var ⟨x, isWider x xInVar⟩
  | Expr.opApp op exprs => Expr.opApp op (fun ar => widenExpr (exprs ar) WiderVar isWider)
  | Expr.un a b => Expr.un (widenExpr a WiderVar isWider) (widenExpr b WiderVar isWider)
  | Expr.ir a b => Expr.ir (widenExpr a WiderVar isWider) (widenExpr b WiderVar isWider)
  | Expr.cpl a => Expr.cpl (widenExpr a WiderVar isWider)
  | Expr.Un x body =>
      Expr.Un x (widenExpr body (addVar WiderVar x) (addVarIsWider Var WiderVar isWider x))
  | Expr.Ir x body =>
      Expr.Ir x (widenExpr body (addVar WiderVar x) (addVarIsWider Var WiderVar isWider x))

-- Why does this not hold by definitional equality? Why can't I just use rfl?
-- Oh the answer is recursion, right? TODO make *your* proof assistant handle it.
-- Oh, the answer probably is that I need funext *and* recursion...
-- Also I am sure there's like a three-line tactic for this.
theorem widenExprEq
  (expr: Expr s Var)
:
  expr = widenExpr expr Var (fun _ => id)
:=
  match expr with
  | Expr.var _ => rfl
  | Expr.opApp op exprs => -- Yay for readability!
      let exprsEq: exprs = (fun ar => widenExpr (exprs ar) Var _) :=
        funext fun ar => widenExprEq (exprs ar)
      
      show Expr.opApp op exprs = Expr.opApp op (fun ar => widenExpr (exprs ar) Var _) from
        exprsEq ▸ rfl
  
  | Expr.un a b =>
      show Expr.un a b = Expr.un (widenExpr a Var _) (widenExpr b Var _) from
        (widenExprEq a) ▸ (widenExprEq b) ▸ rfl
  
  | Expr.ir a b =>
      show Expr.ir a b = Expr.ir (widenExpr a Var _) (widenExpr b Var _) from
        (widenExprEq a) ▸ (widenExprEq b) ▸ rfl
  
  | Expr.cpl a => show Expr.cpl a = Expr.cpl (widenExpr a Var _) from (widenExprEq a) ▸ rfl
  
  | Expr.Un x body =>
      show Expr.Un x body = Expr.Un x (widenExpr body (addVar Var x) _) from
        (widenExprEq body) ▸ rfl
  
  | Expr.Ir x body =>
      show Expr.Ir x body = Expr.Ir x (widenExpr body (addVar Var x) _) from
        (widenExprEq body) ▸ rfl

-- Coe.coe, why u no work?
-- Family of sxpressions.
def FamExpr (s: Signature) (Var: VarSet) := { x: Variable // Var x } → Expr s Var

namespace FamExpr
  def isFinite (_: FamExpr s Var): Prop := Set.isFinite Var
  
  structure Fam (s: Signature) (Index: Type) (V: Index → VarSet) where
    family: (i: Index) → FamExpr s (V i)
    exprsCompatible
      (i j: Index)
      (v: Variable)
      (vVi: v ∈ V i)
      (vVj: v ∈ V j)
    :
      widenExpr (family i ⟨v, vVi⟩) (Set.union V) (Set.unionIsWider V i) =
      widenExpr (family j ⟨v, vVj⟩) (Set.union V) (Set.unionIsWider V j)
  
  noncomputable def union (family: Fam s Index V): FamExpr s (Set.union V) :=
    fun vProp: ↑(Set.union V) =>
      match vProp with
      | ⟨v, vVar⟩ =>
        let exSomeI: ∃i: Index, v ∈ V i := vVar;
        let iProp: { i: Index // v ∈ V i} := choiceEx exSomeI;
        match iProp with
        | ⟨i, prop⟩ =>
          widenExpr (family.family i ⟨v, prop⟩) (Set.union V) (Set.unionIsWider V i)
  
  theorem unionIsWider
    (family: Fam s Index V)
    (i: Index)
    (v: ↑(Set.union V))
    (vVi: v.val ∈ V i)
  :
    union family v = widenExpr (family.family i ⟨v, vVi⟩) (Set.union V) (Set.unionIsWider V i)
  :=
    let exSomeI: ∃ (someI: Index), v.val ∈ V someI := v.property
    let someI := choiceEx exSomeI
    family.exprsCompatible i someI v.val _ _ ▸ rfl
  
  def Set.union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d
end FamExpr

structure DefList (s: Signature) (Var: VarSet) where
  famExpr: FamExpr s Var
  unFin: ∃
    (fam: FamExpr.Fam s Index V)
    (varFam: Var = Set.union V),
      famExpr = varFam ▸ (FamExpr.union fam)  ∧
      ∀ i: Index, Set.isFinite (V i)



structure Algebra (s: Signature) where
  D: Type
  I: (op: Op s) → (arity op ⟨s, rfl⟩) → D





























  



