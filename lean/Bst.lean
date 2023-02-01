/-
  # (Towards a) Boolean Set Theory in a Three-valued Logic: formalized in Lean 4
  ==============================================================================
  
  This is a formalized version of a LaTeX document of the same name.
  I recommend reading this (.lean) document alongside/after the other
  one. You can find more at https://github.com/mik-jozef/bst.
-/

import Ordinal
import PartialOrder
import Set
import Fixpoint

open Classical



/-
  ## Chapter 0: Introduction
  ==============================================
  
  The chapters in this document follow the structure of the other
  document. There is no math in the Introduction chapter of the
  other document, so this chapter is empty.
-/



-- ## Chapter 1: Well-founded collections
-- ======================================

structure Set3 (D: Type) where
  defMem: Set D -- The definitive members
  posMem: Set D -- The possible members
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
  
  def just {D: Type} (d: D): Set3 D := ⟨Set.just d, Set.just d, PartialOrder.refl _⟩
end Set3


instance: LE (Set3 D) where
  le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  a.posMem ≤ b.posMem

instance: SqLE (Set3 D) where
  le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  b.posMem ≤ a.posMem


instance Set3.ord.standard (D: Type): PartialOrderSt (Set3 D) where
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
  
  ltToLeNeq := id
  leNeqToLt := id

def Set3.ord.standard.sup (s: Set (Set3 D)): Supremum s :=
  let sup := {
    defMem := fun d => ∃s: ↑s, d ∈ s.val.defMem
    posMem := fun d => ∃s: ↑s, d ∈ s.val.posMem
    defLePos :=
      fun d dDef =>
        let s := choiceEx dDef
        ⟨s, s.val.val.defLePos d s.property⟩
  }
  ⟨
    sup,
    And.intro
      (fun s =>
        And.intro
          -- Why tf is this unfolding required???
          (fun d dMem => by unfold defMem; exact ⟨s, dMem⟩)
          (fun d dMem => by unfold posMem; exact ⟨s, dMem⟩))
      fun ub ubIsUB =>
        And.intro
          (fun d dMemSupWtf =>
            -- WHAT THE ACTUAL FLYING why is `by exact` necessary here???
            let dMemSup: ∃s: ↑s, d ∈ s.val.defMem := by exact dMemSupWtf;
            let s := choiceEx dMemSup
            let sLeUb: s.val.val .≤ ub := ubIsUB s
            let dInS: d ∈ s.val.val.defMem := s.property
            sLeUb.left d dInS)
          (fun d dMemSupWtf =>
            let dMemSup: ∃s: ↑s, d ∈ s.val.posMem := by exact dMemSupWtf;
            let s := choiceEx dMemSup
            let sLeUb: s.val.val .≤ ub := ubIsUB s
            let dInS: d ∈ s.val.val.posMem := s.property
            sLeUb.right d dInS)
  ⟩


instance Set3.ord.approximation (D: Type): PartialOrderSq (Set3 D) where
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
  
  ltToLeNeq := id
  leNeqToLt := id

def Set3.ord.approximation.sup (ch: Chain (Set3 D)): Supremum ch.val :=
  let sup: Set3 D := {
    defMem := fun d => ∃s: ↑ch.val, d ∈ s.val.defMem
    posMem := fun d => ∀s: ↑ch.val, d ∈ s.val.posMem
    defLePos :=
      fun d dDef s =>
        let sOfD := choiceEx dDef
        let sSOfDComparable := ch.property s sOfD
        
        sSOfDComparable.elim
          (fun sLt =>
            let dSOfDPos: d ∈ sOfD.val.val.posMem :=
              sOfD.val.val.defLePos d sOfD.property
            sLt.right d dSOfDPos)
          (fun sGt =>
            let dSDef: d ∈ s.val.defMem :=
              sGt.left d sOfD.property
            s.val.defLePos d dSDef)
  }
  ⟨
    sup,
    And.intro
      (fun s =>
        And.intro
          (fun d dMem => ⟨s, dMem⟩)
          (fun d dMemSup => dMemSup s))
      fun ub ubIsUB =>
        And.intro
          (fun d dMemSupWtf =>
            -- WHAT THE ACTUAL FLYING why is `by exact` necessary here???
            let dMemSup: ∃s: ↑ch.val, d ∈ s.val.defMem := by exact dMemSupWtf;
            let s := choiceEx dMemSup
            let sLeUb: s.val.val .≤ ub := ubIsUB s
            let dInS: d ∈ s.val.val.defMem := s.property
            sLeUb.left d dInS)
          (fun d dMemUBWtf =>
            let dMemSup: ∃s: ↑ch.val, d ∈ s.val.posMem := by exact dMemUBWtf;
            let s := choiceEx dMemSup
            let sLeUb: s.val.val .≤ ub := ubIsUB s
            let dInS: d ∈ s.val.val.posMem := s.property
            sorry /-sLeUb.right d dInS-/)
  ⟩


-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
structure Signature where
  Op: Type
  arity: Op → Type

inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst


@[reducible] def Variable := Nat

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
      (op: s.Op) →
      (s.arity op → Expr s Var) →
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
    | Expr.opApp op exprs =>
        let exprsEq: exprs = (fun arg => widen (exprs arg) Var _) :=
          funext fun ar => widen.eq (exprs ar)
        
        show Expr.opApp op exprs = Expr.opApp op (fun arg => widen (exprs arg) Var _) from
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
  
  
  @[reducible] def Family (s: Signature) (Var: VarSet) := ↑Var → Expr s Var
  
  namespace Family
    def isFinite (_: Expr.Family s Var): Prop := Set.isFinite Var
    
    -- Family of families of expressions.
    structure FamFam (s: Signature) (Index: Type) (V: Index → VarSet) where
      family: (i: Index) → Expr.Family s (V i)
      exprsCompatible
        (i j: Index)
        (v: Variable)
        (vVi: v ∈ V i)
        (vVj: v ∈ V j)
      :
        Expr.widen (family i ⟨v, vVi⟩) (Set.union V) (Set.union.isWider V i) =
        Expr.widen (family j ⟨v, vVj⟩) (Set.union V) (Set.union.isWider V j)
    
    noncomputable def union (family: FamFam s Index V):
      Expr.Family s (Set.union V)
    :=
      fun vProp: ↑(Set.union V) =>
        let exSomeI: ∃ i: Index, vProp.val ∈ V i := vProp.property;
        let i: { i: Index // vProp.val ∈ V i} := choiceEx exSomeI;
        
        Expr.widen
          (family.family i.val ⟨vProp.val, i.property⟩)
          (Set.union V)
          (Set.union.isWider V i.val)
    
    theorem union.isWider
      (family: FamFam s Index V)
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
    
    -- TODO delete? not needed?
    -- def Set.union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    --   fun (d: D) => ∃ i: Index, family i d
  end Family
end Expr

structure DefList (s: Signature) (Var: VarSet) where
  fam: Expr.Family s Var
  unFin:
    ∃
      (famFam: Expr.Family.FamFam s Index V)
      (varEq: Var = Set.union V)
    ,
      fam = varEq ▸ (Expr.Family.union famFam) ∧
        ∀ i: Index, Set.isFinite (V i)



-- ## Chapter 2: Semantics of WFC
-- ==============================

/-
  For our purposes, algebras act on sets of elements,
  monotonically.
  
  The other document refers to algebras as 'structures'
  because of these differences. I've not yet decided
  which name I want to keep.
-/
structure Algebra (s: Signature) where
  D: Type
  I: (op: s.Op) → (s.arity op → Set D) → Set D
  isMonotonic
    (op: s.Op)
    (args0 args1: s.arity op → Set D)
    (le: ∀ arg: s.arity op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1


@[reducible] def Valuation (Var: VarSet) (D: Type) := ↑Var → Set3 D

namespace Valuation
  def empty: Valuation Var D := fun _ => Set3.empty
  
  def undetermined: Valuation Var D := fun _ => Set3.undetermined
end Valuation

instance Valuation.ord.standard (Var: VarSet) (D: Type)
:
  PartialOrderSt (Valuation Var D)
where
  le a b := ∀ v: ↑Var, a v .≤ b v
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v => PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltToLeNeq := id
  leNeqToLt := id

instance Valuation.ord.approximation (Var: VarSet) (D: Type)
:
  PartialOrderSq (Valuation Var D)
where
  le a b := ∀ v: ↑Var, a v .≤ b v
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v => PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltToLeNeq := id
  leNeqToLt := id


def Valuation.ord.standard.sup
  (ch: @Chain (Valuation Var D) (Valuation.ord.standard Var D).toPartialOrder)
:
  Supremum ch.val
:= ⟨
  sorry,
  sorry
⟩

def Valuation.ord.standard.isChainComplete (Var: VarSet) (D: Type)
:
  chainComplete (Valuation.ord.standard Var D).toPartialOrder
:=
  fun ch => sorry

def Valuation.ord.approximation.isChainComplete (Var: VarSet) (D: Type)
:
  chainComplete (Valuation.ord.approximation Var D).toPartialOrder
:=
  sorry


noncomputable def updateValuation
  (val: Valuation Var D)
  (x: Variable)
  (d: D)
:
  Valuation (addVar Var x) D
:=
  fun v: ↑(addVar Var x) =>
    if vx: v = x then
      Set3.just d
    else
      let vxVal: v.val ∈ Var ∨ v = x := v.property
      let vVar: v.val ∈ Var := vxVal.elim id fun nope => False.elim (vx nope)
      
      val ⟨v.val, vVar⟩


def I (alg: Algebra s) (b c: Valuation Var alg.D): (Expr s Var) → Set3 alg.D
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
| Expr.Un x body =>
    let iBody (iX: alg.D): Set3 alg.D :=
      (I alg (updateValuation b x iX) (updateValuation c x iX) body)
    
    ⟨
      fun d => ∃ iX: alg.D, d ∈ (iBody iX).defMem,
      fun d => ∃ iX: alg.D, d ∈ (iBody iX).posMem,
      
      fun d dDef => dDef.elim fun iX iXDef => ⟨iX, (iBody iX).defLePos d iXDef⟩
    ⟩
| Expr.Ir x body =>
    let iBody (iX: alg.D): Set3 alg.D :=
      (I alg (updateValuation b x iX) (updateValuation c x iX) body)
    
    ⟨
      fun d => ∃ iX: alg.D, d ∈ (iBody iX).defMem,
      fun d => ∃ iX: alg.D, d ∈ (iBody iX).posMem,
      
      fun d dDef => dDef.elim fun iX iXDef => ⟨iX, (iBody iX).defLePos d iXDef⟩
    ⟩

-- Interpretation defined
def DefList.I
  (alg: Algebra s)
  (b c: Valuation Var alg.D)
  (dl: DefList s Var)
:
  Valuation Var alg.D
:=
  fun x =>
    _root_.I alg b c (dl.fam x)


def OpC {alg: Algebra s} (dl: DefList s Var) (b: Valuation Var alg.D):
  Valuation Var alg.D → Valuation Var alg.D
:=
  fun c => DefList.I alg b c dl

noncomputable def C
  {alg: Algebra s}
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
:
  Valuation Var alg.D
:=
  if (n.isLimit) then
    lfp n fun x => sorry
  else
    sorry


def OpB {alg: Algebra s} (dl: DefList s Var):
  Valuation Var alg.D → Valuation Var alg.D
:=
  fun c => DefListI alg b c dl





-- ## Chapter 4: Tracking undeterminedness
-- =======================================

-- TODO
--
-- :tumbleweed:


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

def natAlg: Algebra natSig := ⟨Nat, natAlg.I, natAlg.monotonic⟩


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

def pairAlg: Algebra pairSig := ⟨Pair, pairAlg.I, pairAlg.monotonic⟩


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

def mpairAlg: Algebra pairSig := ⟨MPair, mpairAlg.I, mpairAlg.monotonic⟩
