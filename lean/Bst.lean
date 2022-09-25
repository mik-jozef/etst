/-
  # (Towards a) Boolean Set Theory in a Three-valued Logic: formalized in Lean 4
  ==============================================================================
  
  This is a formalized version of the document of the same name.
  I recommend reading this document alongside/after the other one.
  You can find more at https://github.com/mik-jozef/bst.
  
  Code style: prefer no tactics.
-/

import PartialOrder

open Classical



/-
  ## Chapter 0: Introduction
  ==============================================
  
  The chapters in this document follow the structure of the other
  document. There is no math in the Introduction chapter of the
  other document, but in Lean, I still need to define some basics,
  so I'll put that here.
-/

noncomputable def choiceEx {P: T → Prop} (ex: ∃ t: T, P t): { t: T // P t } :=
  let nonempty: Nonempty { t: T // P t } :=
    match ex with
    | ⟨t, prop⟩ => ⟨t, prop⟩
  choice nonempty


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
  def empty {D: Type}: Set D := fun _ => False  
  def full  {D: Type}: Set D := fun _ => True
  
  def isFinite (s: Set D): Prop := ∃ l: List D, ∀ t: D, t ∈ s → t ∈ l
  
  def isSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  def union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d
  
  theorem union.isWider
    (family: Index → Set D)
    (i: Index)
  :
    isSubset (family i) (union family)
  :=
    fun (d: D) (dfi: d ∈ family i) => ⟨i, dfi⟩
  
  def binaryUnion (a b: Set D): Set D := fun d: D => a d ∨ b d
  def binaryIntersection (a b: Set D): Set D := fun d: D => a d ∧ b d
  def complement (a: Set D): Set D := fun d: D => ¬ a d
end Set

infix:50 " ⊆ " => Set.isSubset
infix:60 " ∪ " => Set.binaryUnion
infix:60 " ∩ " => Set.binaryIntersection
prefix:100 "~ " => Set.complement



-- ## Chapter 1: Well-founded collections
-- ======================================

structure Set3 (D: Type) where
  defMem: Set D
  posMem: Set D
  defLePos: defMem ≤ posMem

namespace Set3
  protected def eq:
    (a b: Set3 D) →
    a.defMem = b.defMem →
    a.posMem = b.posMem
  →
    a = b
  -- Thanks to answerers of https://proofassistants.stackexchange.com/q/1747
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
  
  def empty {D: Type}: Set3 D := ⟨Set.empty, Set.empty, PartialOrder.refl _⟩
  
  def undetermined {D: Type}: Set3 D := ⟨Set.empty, Set.full, fun _ => False.elim⟩
end Set3


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
-- TODO perhaps change to a structure?
def Signature := (Op: Type) × (Op → Type)
def Op (s: Signature) := s.fst

def SigOp (Op: Type) := { s: Signature // s.fst = Op }
def arity {Op: Type} (op: Op) (s: SigOp Op): Type := s.val.snd (cast s.property.symm op)

inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst


def Variable := Nat
-- Why tf is "reducible" even required? Lean, this is stupid.
@[reducible] def VarSet := Set Variable

def addVar (Var: VarSet) (x: Variable): VarSet :=
  fun z => Var z ∨ z = x

namespace addVar
  theorem monotonic (Var: VarSet) (x: Variable): Var ⊆ addVar Var x :=
    fun (v: Variable) (vVar: v ∈ Var) => Or.inl vVar
  
  theorem xInVarIsId
    (Var: VarSet)
    (x: Variable)
    (xInVar: x ∈ Var)
  :
    addVar Var x = Var
  :=
    Set.ext fun v: Variable =>
      Iff.intro
        (fun vInAddVar => Or.elim vInAddVar id (fun vx => vx ▸ xInVar))
        ((monotonic Var x) v)  
  
  theorem isWider
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
end addVar


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


namespace Expr
  -- This is horrendous. Please tell me I just suck at Lean
  -- and there is a much better way of doing this.
  def widen
    (expr: Expr s Var)
    (WiderVar: VarSet)
    (isWider: Var ⊆ WiderVar)
  :
    Expr s WiderVar
  :=
    match expr with
    | Expr.var ⟨x, xInVar⟩ => Expr.var ⟨x, isWider x xInVar⟩
    | Expr.opApp op exprs => Expr.opApp op (fun ar => widen (exprs ar) WiderVar isWider)
    | Expr.un a b => Expr.un (widen a WiderVar isWider) (widen b WiderVar isWider)
    | Expr.ir a b => Expr.ir (widen a WiderVar isWider) (widen b WiderVar isWider)
    | Expr.cpl a => Expr.cpl (widen a WiderVar isWider)
    | Expr.Un x body =>
        Expr.Un x (widen body (addVar WiderVar x) (addVar.isWider Var WiderVar isWider x))
    | Expr.Ir x body =>
        Expr.Ir x (widen body (addVar WiderVar x) (addVar.isWider Var WiderVar isWider x))
  
  -- Why does this not hold by definitional equality? Why can't I just use rfl?
  -- Oh the answer is recursion, right? TODO make *your* proof assistant handle it.
  -- Oh, the answer probably is that I need funext *and* recursion...
  -- Also I am sure there's like a three-line tactic for this.
  theorem widen.eq
    (expr: Expr s Var)
  :
    expr = widen expr Var (fun _ => id)
  :=
    match expr with
    | Expr.var _ => rfl
    | Expr.opApp op exprs => -- Yay for readability! /s
        let exprsEq: exprs = (fun ar => widen (exprs ar) Var _) :=
          funext fun ar => widen.eq (exprs ar)
        
        show Expr.opApp op exprs = Expr.opApp op (fun ar => widen (exprs ar) Var _) from
          exprsEq ▸ rfl
    
    | Expr.un a b =>
        show Expr.un a b = Expr.un (widen a Var _) (widen b Var _) from
          (widen.eq a) ▸ (widen.eq b) ▸ rfl
    
    | Expr.ir a b =>
        show Expr.ir a b = Expr.ir (widen a Var _) (widen b Var _) from
          (widen.eq a) ▸ (widen.eq b) ▸ rfl
    
    | Expr.cpl a => show Expr.cpl a = Expr.cpl (widen a Var _) from (widen.eq a) ▸ rfl
    
    | Expr.Un x body =>
        show Expr.Un x body = Expr.Un x (widen body (addVar Var x) _) from
          (widen.eq body) ▸ rfl
    
    | Expr.Ir x body =>
        show Expr.Ir x body = Expr.Ir x (widen body (addVar Var x) _) from
          (widen.eq body) ▸ rfl
  
  
  @[reducible] def Fam (s: Signature) (Var: VarSet) := ↑Var → Expr s Var
  
  namespace Fam
    def isFinite (_: Expr.Fam s Var): Prop := Set.isFinite Var
    
    -- Family of families of expressions.
    structure Fam (s: Signature) (Index: Type) (V: Index → VarSet) where
      family: (i: Index) → Expr.Fam s (V i)
      exprsCompatible
        (i j: Index)
        (v: Variable)
        (vVi: v ∈ V i)
        (vVj: v ∈ V j)
      :
        Expr.widen (family i ⟨v, vVi⟩) (Set.union V) (Set.union.isWider V i) =
        Expr.widen (family j ⟨v, vVj⟩) (Set.union V) (Set.union.isWider V j)
    
    noncomputable def union (family: Fam s Index V): Expr.Fam s (Set.union V) :=
      fun vProp: ↑(Set.union V) =>
        match vProp with
        | ⟨v, vVar⟩ =>
          let exSomeI: ∃ i: Index, v ∈ V i := vVar;
          let iProp: { i: Index // v ∈ V i} := choiceEx exSomeI;
          match iProp with
          | ⟨i, prop⟩ =>
              Expr.widen
                (family.family i ⟨v, prop⟩)
                (Set.union V)
                (Set.union.isWider V i)
    
    theorem unionIsWider
      (family: Fam s Index V)
      (i: Index)
      (v: ↑(Set.union V))
      (vVi: v.val ∈ V i)
    :
      union family v =
        Expr.widen
          (family.family i ⟨v, vVi⟩)
          (Set.union V)
          (Set.union.isWider V i)
    :=
      let exSomeI: ∃ (someI: Index), v.val ∈ V someI := v.property
      let someI := choiceEx exSomeI
      family.exprsCompatible i someI v.val _ _ ▸ rfl
    
    def Set.union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
      fun (d: D) => ∃ i: Index, family i d
  end Fam
end Expr

structure DefList (s: Signature) (Var: VarSet) where
  fam: Expr.Fam s Var
  unFin: ∃
    (famFam: Expr.Fam.Fam s Index V)
    (varEq: Var = Set.union V),
      fam = varEq ▸ (Expr.Fam.union famFam)  ∧
      ∀ i: Index, Set.isFinite (V i)



-- ## Chapter 2: Semantics of WFC
-- ==============================

/-
  For our purposes, algebras act on sets of elements,
  monotonically.
  The other document refers to algebras as 'structures',
  because of these differences. I've not yet decided
  which name I want to keep.
-/
structure Algebra (s: Signature) (D: Type) where
  I: (op: Op s) → (arity op ⟨s, rfl⟩ → Set D) → Set D
  isMonotonic
    (op: Op s)
    (args0 args1: arity op ⟨s, rfl⟩ → Set D)
    (le: ∀ arg: arity op ⟨s, rfl⟩, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1




@[reducible] def Valuation (Var: VarSet) (D: Type) := ↑Var → Set3 D

namespace Valuation
  def empty: Valuation Var D := fun _ => Set3.empty
  
  def undetermined: Valuation Var D := fun _ => Set3.undetermined
end Valuation

instance: PartialOrder (Valuation Var D) where
  le a b := ∀ v: ↑Var, a v ≤ b v
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v => PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltIffLeNotEq := fun _ _ => Iff.intro id id

instance: PartialOrderSq (Valuation Var D) where
  le a b := ∀ v: ↑Var, a v ≤ b v
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v => PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltIffLeNotEq := fun _ _ => Iff.intro id id


def I (alg: Algebra s D) (b c: Valuation Var D): (Expr s Var) → Set3 D
| Expr.var a => c a
| Expr.opApp op exprs =>
    let defArgs := fun arg => (I alg b c (exprs arg)).defMem
    let posArgs := fun arg => (I alg b c (exprs arg)).posMem
    ⟨
      alg.I op defArgs,
      alg.I op posArgs,
      
      alg.isMonotonic
        op
        defArgs
        posArgs
        fun arg => (I alg b c (exprs arg)).defLePos
    ⟩
| Expr.un e0 e1 =>
    let iE0 := I alg b c e0
    let iE1 := I alg b c e1
    ⟨
      iE0.defMem ∪ iE1.defMem,
      iE0.posMem ∪ iE1.posMem,
      
      fun d dDef =>
        Or.elim (dDef: d ∈ iE0.defMem ∨ d ∈ iE1.defMem)
          (fun dIE0 => Or.inl (iE0.defLePos d dIE0))
          (fun dIE1 => Or.inr (iE1.defLePos d dIE1))
    ⟩
| Expr.ir e0 e1 =>
    let iE0 := I alg b c e0
    let iE1 := I alg b c e1
    ⟨
      iE0.defMem ∩ iE1.defMem,
      iE0.posMem ∩ iE1.posMem,
      
      fun d dDef =>
        And.intro (iE0.defLePos d dDef.left) (iE1.defLePos d dDef.right)
    ⟩
| Expr.cpl e =>
    let ie := (I alg b b e)
    ⟨
      ~ ie.posMem,
      ~ ie.defMem,
      
      fun d dInNPos =>
        show d ∉ ie.defMem from fun dInDef => dInNPos (ie.defLePos d dInDef)
    ⟩
| Expr.Un x body => sorry
| Expr.Ir x body => sorry






-- ## Chapter 4: Example WFCs
-- ==========================


inductive NatOp
  | zero
  | succ
  | plus

@[reducible] def natAr: NatOp → Type
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



namespace natAlg
  def I: (op: NatOp) → (args: natAr op → Set Nat) → Set Nat
  | NatOp.zero => fun _ n => n = 0
  | NatOp.succ => fun args n => ∃ a: ↑(args ArityOne.zth), n = a + 1
  | NatOp.plus => fun args n =>
      ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), n = a + b
  
  theorem monotonic
    (op: NatOp)
    (args0 args1: natAr op → Set Nat)
    (le: ∀ arg: natAr op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | NatOp.zero => PartialOrder.refl _
      | NatOp.succ =>
          fun (n: Nat) (nInArgs0) =>
            let exArgs0: ∃ a: ↑(args0 ArityOne.zth), n = a + 1 := nInArgs0
            
            let exArgs1: ∃ a: ↑(args1 ArityOne.zth), n = a + 1 :=
              exArgs0.elim fun a nASucc =>
                ⟨⟨a.val, le ArityOne.zth _ a.property⟩, nASucc⟩
            
            show n ∈ I NatOp.succ args1 from exArgs1
      | NatOp.plus =>
          fun (n: Nat) (nInArgs0) =>
            let exArgs0:
              ∃ (a: ↑(args0 ArityTwo.zth)) (b: ↑(args0 ArityTwo.fst)),
                n = a + b := nInArgs0
            
            let exArgs1:
              ∃ (a: ↑(args1 ArityTwo.zth)) (b: ↑(args1 ArityTwo.fst)), n = a + b
            :=
              exArgs0.elim fun a bEx =>
                bEx.elim fun b nab => ⟨
                  ⟨a.val, le ArityTwo.zth _ a.property⟩,
                  ⟨⟨b.val, le ArityTwo.fst _ b.property⟩, nab⟩
                ⟩
            
            show n ∈ I NatOp.plus args1 from exArgs1
end natAlg

def natAlg: Algebra natSig Nat := ⟨natAlg.I, natAlg.monotonic⟩


inductive Pair where
  | zero: Pair -- Zero is considered an improper pair
  | pair (a b: Pair): Pair

namespace pairAlg
  def I: (op: PairOp) → (args: pairAr op → Set Pair) → Set Pair
    | PairOp.zero => fun _ p => p = Pair.zero
    | PairOp.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), p = Pair.pair a b
  
  theorem monotonic
    (op: PairOp)
    (args0 args1: pairAr op → Set Pair)
    (le: ∀ arg: pairAr op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | PairOp.zero => PartialOrder.refl _
      | PairOp.pair =>
          fun _ pInArgs0 =>
            pInArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth _ a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst _ b.property⟩, nab⟩
              ⟩
end pairAlg

def pairAlg: Algebra pairSig Pair := ⟨pairAlg.I, pairAlg.monotonic⟩


inductive MPair.Ret
  | isZero
  | isPair
  | isNull

structure MPair where
  f: List ArityTwo → MPair.Ret
  rootNotNull: f [] ≠ MPair.Ret.isNull
  pairHasMem (s: List ArityTwo) (i: ArityTwo):
    f s = MPair.Ret.isPair ↔ f (s ++ [i]) ≠ MPair.Ret.isNull

namespace MPair
  @[reducible] def zeroF: List ArityTwo → MPair.Ret :=
    fun list: List ArityTwo =>
      match list with
      | List.nil => MPair.Ret.isZero
      | _ :: _ => MPair.Ret.isNull
  
  def zero: MPair := ⟨
    zeroF,
    by simp,
    -- AAAAAAAAAAAaaaAAAAAAAAAAa ..... Why does such a simple thing
    -- have to be so complicated?
    fun (s: List ArityTwo) (i: ArityTwo) =>
      let eqL: zeroF s ≠ MPair.Ret.isPair :=
        match s with
        | [] => by simp
        | hd :: rest =>
          let isNull: zeroF (hd :: rest) = MPair.Ret.isNull := rfl
          isNull ▸ by simp
      let eqR: zeroF (s ++ [i]) = MPair.Ret.isNull :=
        match list: s ++ [i] with
        | [] =>
          let nope: s ++ [i] ≠ [] := by cases s <;> simp
          False.elim (nope list)
        | hd :: rest => rfl
      Iff.intro
        (fun ff => False.elim (eqL ff))
        (fun ff => False.elim (ff eqR))
  ⟩
  
  @[reducible] def pairF (a b: MPair): List ArityTwo → MPair.Ret
    | [] => MPair.Ret.isPair
    | ArityTwo.zth :: rest => a.f rest
    | ArityTwo.fst :: rest => b.f rest
  
  def pair (a b: MPair): MPair := ⟨
    pairF a b,
    let eq: pairF a b [] = MPair.Ret.isPair := rfl;
    by rw [eq] simp, -- How can I do this without tactics?
    fun s i => Iff.intro (
        fun isP => match s, i with
          | [], ArityTwo.zth => a.rootNotNull
          | [], ArityTwo.fst => b.rootNotNull
          | ArityTwo.zth :: rest, i => (a.pairHasMem rest i).mp isP
          | ArityTwo.fst :: rest, i => (b.pairHasMem rest i).mp isP
      ) (
        fun isNotNull => match s with
          | [] => rfl
          | ArityTwo.zth :: rest => (a.pairHasMem rest i).mpr isNotNull
          | ArityTwo.fst :: rest => (b.pairHasMem rest i).mpr isNotNull
      )
  ⟩
end MPair

namespace mpairAlg
  def I: (op: PairOp) → (args: pairAr op → Set MPair) → Set MPair
    | PairOp.zero => fun _ p => p = MPair.zero
    | PairOp.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), p = MPair.pair a b
  
  theorem monotonic
    (op: PairOp)
    (args0 args1: pairAr op → Set MPair)
    (le: ∀ arg: pairAr op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | PairOp.zero => PartialOrder.refl _
      | PairOp.pair =>
          fun _ pInArgs0 =>
            pInArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth _ a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst _ b.property⟩, nab⟩
              ⟩
end mpairAlg

def mpairAlg: Algebra pairSig MPair := ⟨mpairAlg.I, mpairAlg.monotonic⟩
