/-
  Appendix 1: The salgebra of natural numbers
  
  Here we define the salgebra of natural numbers with zero, successor,
  addition and multiplication. We show that this salgebra is equivalent
  to the salgebra of pairs under a simple representation of pairs as
  natural numbers.
  
  TODO this is unfinished (and unused in the later chapters).
-/

import old.WFC.Ch5_PairSalgebra
import old.Utils.CantorPairing


-- We encode pairs as natural numbers using the Cantor pairing function.
def Pair.toNatCantor: Pair → Nat
| Pair.zero => 0
| Pair.pair a b => Nat.succ (Nat.cantorPair a.toNatCantor b.toNatCantor)

def Pair.ofNatCantor: Nat → Pair
| 0 => ()
| n+1 =>
  have := Nat.cantorZth_le n
  have := Nat.cantorFst_le n
  (
    (Pair.ofNatCantor n.cantorZth),
    (Pair.ofNatCantor n.cantorFst),
  )

def Pair.ofCantor_toCantor_eq:
  (p: Pair) →
  ofNatCantor (toNatCantor p) = p
|
  zero => by unfold toNatCantor ofNatCantor; rfl
| pair a b => by
  unfold ofNatCantor
  apply Pair.eq
  rw [Nat.cantorPair_zth_eq]
  exact ofCantor_toCantor_eq a
  rw [Nat.cantorPair_fst_eq]
  exact ofCantor_toCantor_eq b

def Pair.toSet3Nat
  (s: Set3 Pair)
:
  Set3 Nat
:= {
  defMem := s.defMem.image toNatCantor
  posMem := s.posMem.image toNatCantor
  defLePos := fun _ ⟨p, isDef, eq⟩ => ⟨p, isDef.toPos, eq⟩
}

def Pair.ofSet3Nat
  (s: Set3 Nat)
:
  Set3 Pair
:= {
  defMem := s.defMem.image ofNatCantor
  posMem := s.posMem.image ofNatCantor
  defLePos := fun _ ⟨p, isDef, eq⟩ => ⟨p, isDef.toPos, eq⟩
}

def Pair.ofSetToSetEq
  (s: Set3 Pair)
:
  ofSet3Nat (toSet3Nat s) = s
:=
  Set3.eq
    (funext fun p =>
      Eq.propIntro
        (fun ⟨_, ⟨_, isDef, eqTo⟩, eqOf⟩ =>
          eqOf ▸ eqTo ▸ (ofCantor_toCantor_eq _).symm ▸ isDef)
        (fun isDef =>
          ⟨toNatCantor p, ⟨p, isDef, rfl⟩, ofCantor_toCantor_eq p⟩))
    (funext fun p =>
      Eq.propIntro
        (fun ⟨_, ⟨_, isDef, eqTo⟩, eqOf⟩ =>
          eqOf ▸ eqTo ▸ (ofCantor_toCantor_eq _).symm ▸ isDef)
        (fun isDef =>
          ⟨toNatCantor p, ⟨p, isDef, rfl⟩, ofCantor_toCantor_eq p⟩))


inductive natSignature.Op
| zero
| succ
| add
| mul
| un
| ir
| cond

def natSignature.Params: natSignature.Op → Type
| Op.zero => ArityZero
| Op.succ => ArityOne
| Op.add => ArityTwo
| Op.mul => ArityTwo
| Op.un => ArityTwo
| Op.ir => ArityTwo
| Op.cond => ArityOne

def natSignature: Signature := {
  Op := natSignature.Op,
  Params := natSignature.Params,
}

namespace natSalgebra
  open natSignature

  def evalOp: (op: natSignature.Op) → natSignature.Args op Nat → Set Nat
  | Op.zero, _, p => p = 0
  | Op.succ, args, p => ∃ (n: ↑(args ArityOne.zth)), p = Nat.succ n
  | Op.add, args, p =>
    ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), p = a + b
  | Op.mul, args, p =>
    ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), p = a * b
  | Op.un, args, p => args ArityTwo.zth p ∨ args ArityTwo.fst p
  | Op.ir, args, p => args ArityTwo.zth p ∧ args ArityTwo.fst p
  | Op.cond, args, _ => (args ArityOne.zth).Nonempty
  
  def evalOp.isMonotonic
    (op: natSignature.Op)
    (args0 args1: natSignature.Args op Nat)
    (le: ∀ param: Params op, args0 param ≤ args1 param)
  :
    evalOp op args0 ≤ evalOp op args1
  :=
    match op with
    | Op.zero => Preorder.le_refl _
    | Op.succ =>
      fun _ ⟨arg, eq⟩ => ⟨⟨arg, le ArityOne.zth arg.property⟩, eq⟩
    | Op.add =>
      fun _ ⟨arg0, arg1, eq⟩ => ⟨
        ⟨arg0, le ArityTwo.zth arg0.property⟩,
        ⟨arg1, le ArityTwo.fst arg1.property⟩,
        eq,
      ⟩
    | Op.mul =>
      fun _ ⟨arg0, arg1, eq⟩ => ⟨
        ⟨arg0, le ArityTwo.zth arg0.property⟩,
        ⟨arg1, le ArityTwo.fst arg1.property⟩,
        eq,
      ⟩
    | Op.un =>
      fun _ pInArgs0 =>
        pInArgs0.elim
          (fun pInArgs0 => Or.inl (le ArityTwo.zth pInArgs0))
          (fun pInArgs0 => Or.inr (le ArityTwo.fst pInArgs0))
    | Op.ir =>
      fun _ ⟨inL, inR⟩ => ⟨
        le ArityTwo.zth inL,
        le ArityTwo.fst inR,
      ⟩
    | Op.cond => fun _ ⟨p, inL⟩ => ⟨p, le ArityOne.zth inL⟩
end natSalgebra

def natSalgebra: Salgebra natSignature :=
  ⟨Nat, natSalgebra.evalOp, natSalgebra.evalOp.isMonotonic⟩


def DefList.toPairDefList
  (dl: DefList natSignature)
:
  DefList pairSignature
:= {
  getDef :=
    fun x =>
      sorry
}


def natSalgebra.definableIffPair
  (s: Set3 Nat)
:
  natSalgebra.IsDefinable s
    ↔
  pairSalgebra.IsDefinable (Pair.ofSet3Nat s)
:=
  Iff.intro
    (fun ⟨dl, x, eq⟩ =>
      sorry)
    (fun ⟨dl, x, eq⟩ =>
      sorry)

def pairSalgebra.definableIffNat
  (s: Set3 Pair)
:
  natSalgebra.IsDefinable (Pair.toSet3Nat s)
    ↔
  pairSalgebra.IsDefinable s
:= by
  conv => rhs; rw [←Pair.ofSetToSetEq s]
  exact natSalgebra.definableIffPair (Pair.toSet3Nat s)
