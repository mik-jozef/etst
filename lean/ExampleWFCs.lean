import Arities
import Interpretation

open Classical


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


inductive SPair.Ret
  | isZero
  | isPair
  | isNull

structure SPair where
  f: List ArityTwo → SPair.Ret
  rootNotNull: f [] ≠ SPair.Ret.isNull
  pairHasMem (s: List ArityTwo) (i: ArityTwo):
    f s = SPair.Ret.isPair ↔ f (s ++ [i]) ≠ SPair.Ret.isNull

namespace SPair
  @[reducible] def zeroF: List ArityTwo → SPair.Ret :=
    fun list: List ArityTwo =>
      match list with
      | List.nil => SPair.Ret.isZero
      | _ :: _ => SPair.Ret.isNull
  
  def zero: SPair := ⟨
    zeroF,
    by simp,
    -- AAAAAAAAAAAaaaAAAAAAAAAAa ..... Why does such a simple thing
    -- have to be so complicated?
    fun (s: List ArityTwo) (i: ArityTwo) =>
      let eqL: zeroF s ≠ SPair.Ret.isPair :=
        match s with
        | [] => by simp
        | hd :: rest =>
          let isNull: zeroF (hd :: rest) = SPair.Ret.isNull := rfl
          isNull ▸ by simp
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
  
  @[reducible] def pairF (a b: SPair): List ArityTwo → SPair.Ret
    | [] => SPair.Ret.isPair
    | ArityTwo.zth :: rest => a.f rest
    | ArityTwo.fst :: rest => b.f rest
  
  def pair (a b: SPair): SPair := ⟨
    pairF a b,
    let eq: pairF a b [] = SPair.Ret.isPair := rfl;
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
end SPair

namespace sPairAlg
  def I: (op: PairOp) → (args: pairAr op → Set SPair) → Set SPair
    | PairOp.zero => fun _ p => p = SPair.zero
    | PairOp.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth)) (b: ↑(args ArityTwo.fst)), p = SPair.pair a b
  
  theorem monotonic
    (op: PairOp)
    (args0 args1: pairAr op → Set SPair)
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
end sPairAlg

def sPairAlg: Algebra pairSig :=
  ⟨SPair, sPairAlg.I, sPairAlg.monotonic⟩
