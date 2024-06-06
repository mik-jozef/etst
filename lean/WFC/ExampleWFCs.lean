import WFC.Interpretation
import WFC.Pair


inductive natSignature.Op
  | zero
  | succ
  | plus

def natSignature.Params: Op → Type
  | Op.zero => ArityZero
  | Op.succ => ArityOne
  | Op.plus => ArityTwo

def natSignature: Signature := {
  Op := natSignature.Op,
  Params := natSignature.Params,
}


inductive pairSignature.Op where
| zero
| pair

def pairSignature.Params: Op → Type
| Op.zero => ArityZero
| Op.pair => ArityTwo

def pairSignature: Signature := {
  Op := pairSignature.Op,
  Params := pairSignature.Params,
}



namespace natSalgebra
  open natSignature
  
  def I: (op: Op) → (args: Args natSignature op Nat) → Set Nat
  | Op.zero => fun _ n => n = 0
  | Op.succ => fun args n => ∃ a: ↑(args ArityOne.zth), n = a + 1
  | Op.plus => fun args n =>
      ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), n = a + b
  
  theorem I.isMonotonic
    (op: natSignature.Op)
    (args0 args1: Params op → Set Nat)
    (le: ∀ arg: Params op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | Op.zero => Preorder.le_refl _
      | Op.succ =>
          fun (n: Nat) (nInArgs0) =>
            let exArgs0: ∃ a: ↑(args0 ArityOne.zth), n = a + 1 := nInArgs0
            
            exArgs0.elim fun a nASucc =>
              ⟨⟨a.val, le ArityOne.zth a.property⟩, nASucc⟩
      | Op.plus =>
          fun (n: Nat) (nInArgs0) =>
            let exArgs0:
              ∃ (a: ↑(args0 ArityTwo.zth)) (b: ↑(args0 ArityTwo.fst)),
                n = a + b := nInArgs0
            
            exArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst b.property⟩, nab⟩
              ⟩
end natSalgebra

def natSalgebra: Salgebra natSignature :=
  ⟨Nat, natSalgebra.I, natSalgebra.I.isMonotonic⟩


namespace pairSalgebra
  open pairSignature
  
  def I: (op: Op) → (args: Args pairSignature op Pair) → Set Pair
    | Op.zero => fun _ p => p = Pair.zero
    | Op.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth))
          (b: ↑(args ArityTwo.fst))
        ,
          p = Pair.pair a b
  
  theorem I.isMonotonic
    (op: Op)
    (args0 args1: Args pairSignature op Pair)
    (le: ∀ param: Params op, args0 param ≤ args1 param)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | Op.zero => Preorder.le_refl _
      | Op.pair =>
          fun _ pInArgs0 =>
            pInArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst b.property⟩, nab⟩
              ⟩
end pairSalgebra

def pairSalgebra: Salgebra pairSignature :=
  ⟨Pair, pairSalgebra.I, pairSalgebra.I.isMonotonic⟩


inductive SPair.Ret
| isZero
| isPair
| isNull

/-
  SPair is, intuitively, like Pair above, but spairs
  may have infinite depth, contain themselves, and
  so on. Eg. `s = (s, ())` is a valid spair that
  contains itself and the improper pair.
  
  An spair is coded as a function from tuples of
  indices to what that spair contains under those
  indices, or null if the path is invalid. Invalid
  paths are those that try to access the contents
  of zero.
  
  Later note: this is dumb. I should have made spairs
  equivalence classes of sequences of growing prefixes
  of the infinite thing.
-/
structure SPair where
  f: List ArityTwo → SPair.Ret
  
  rootNotNull: f [] ≠ SPair.Ret.isNull
  pairHasMem (s: List ArityTwo) (i: ArityTwo):
    f s = SPair.Ret.isPair ↔ f (s ++ [i]) ≠ SPair.Ret.isNull

namespace SPair
  def zeroF: List ArityTwo → SPair.Ret
  | List.nil => SPair.Ret.isZero
  | _ :: _ => SPair.Ret.isNull
  
  def zero: SPair := ⟨
    zeroF,
    SPair.Ret.noConfusion,
    -- AAAAAAAAAAAaaaAAAAAAAAAAa ..... Why does such a simple thing
    -- have to be so complicated?
    fun (s: List ArityTwo) (i: ArityTwo) =>
      let eqL: zeroF s ≠ SPair.Ret.isPair :=
        match s with
        | [] => SPair.Ret.noConfusion
        | hd :: rest =>
          let isNull: zeroF (hd :: rest) = SPair.Ret.isNull := rfl
          isNull ▸ SPair.Ret.noConfusion
      
      let eqR: zeroF (s ++ [i]) = SPair.Ret.isNull :=
        match list: s ++ [i] with
        | [] =>
          let nope: s ++ [i] ≠ [] := by cases s <;> simp
          False.elim (nope list)
        | hd :: rest => rfl
      
      Iff.intro
        (fun ff => False.elim (eqL ff))
        (fun ff => False.elim (ff eqR))
  ⟩
  
  def pairF (a b: SPair): List ArityTwo → SPair.Ret
    | [] => SPair.Ret.isPair
    | ArityTwo.zth :: rest => a.f rest
    | ArityTwo.fst :: rest => b.f rest
  
  def pair (a b: SPair): SPair := {
    f := pairF a b,
    
    rootNotNull := SPair.Ret.noConfusion,
    pairHasMem :=
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
  }
end SPair

namespace sPairSalgebra
  open pairSignature
  
  def I: (op: Op) → (args: Args pairSignature op SPair) → Set SPair
    | Op.zero => fun _ p => p = SPair.zero
    | Op.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth))
          (b: ↑(args ArityTwo.fst))
        ,
          p = SPair.pair a b
  
  theorem I.isMonotonic
    (op: Op)
    (args0 args1: Args pairSignature op SPair)
    (le: ∀ param: Params op, args0 param ≤ args1 param)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | Op.zero => Preorder.le_refl _
      | Op.pair =>
          fun _ pInArgs0 =>
            pInArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst b.property⟩, nab⟩
              ⟩
end sPairSalgebra

def sPairSalgebra: Salgebra pairSignature :=
  ⟨SPair, sPairSalgebra.I, sPairSalgebra.I.isMonotonic⟩
