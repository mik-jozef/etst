import Mathlib.Data.Set.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.Heyting.Basic


/-
  Here I attempt to formalize induction and coinduction.
  This is mostly based on the Wikipedia article on coinduction, and
  an example is taken from [0].
  
  0. Kozen, Silva. Practical coinduction. 2017 doi:10.1017/S0960129515000493
     https://www.cs.cornell.edu/~kozen/Papers/Structural.pdf
  
  TODO revisit the description.
  
  TODO how is the principle of corecursion related to corecursive
  functions such as
  
  def Stream'.even:
    Stream' T → Stream' T
  |
    h :: _ :: t => h :: t
  
  def Stream'.natInc:
    Stream' Nat → Stream' Nat
  |
    n :: t => n.succ :: natInc t
  
  def Stream'.natStairs:
    Stream' Nat → Stream' Nat
  |
    n :: t => n.succ :: natInc (natStairs t)
  
  coinductive Stream.Le [PartialOrder T]: Stream' T → Stream' T → Prop
  | Head (lt: a < b) (t0 t1: Stream' T): Le (a :: t0) (b :: t1)
  | Tail (n) (tLe: Le t0 t1): Le (n :: t0) (n :: t1)
  
  def Stream'.le_trans
    {a b c: Stream' Nat}
  :
    Le a b → Le b c → Le a c
  |
    .Head ab _ _, .Head bc _ _ => .Head (ab.trans bc) _ _
  | .Head ab _ _, .Tail _ _ => .Head ab _ _
  | .Tail _ _, .Head bc _ _ => .Head bc _ _
  | .Tail _ ab, .Tail _ bc => .Tail _ (le_trans ab bc)
-/

def OrderHom.cplDual
  [la: BooleanAlgebra A]
  [lb: BooleanAlgebra B]
  (f: A →o B)
:
  A →o B
:= {
  toFun := fun a => (f aᶜ)ᶜ
  monotone' := fun _ _ ab =>
    compl_le_compl (f.monotone (compl_le_compl ab))
}

namespace fpHelpers
  def le_cpl_of_f_le
    [CompleteBooleanAlgebra T]
    (f: T →o T)
    (le: f t ≤ t)
  :
    tᶜ ≤ f.cplDual tᶜ
  :=
    compl_le_compl (by
      conv => lhs; rw [compl_compl t]
      exact le)
  
  def cpl_le_of_le_f
    [CompleteBooleanAlgebra T]
    (f: T →o T)
    (le: t ≤ f t)
  :
    f.cplDual tᶜ ≤ tᶜ
  :=
    compl_le_compl (by
      conv => rhs; rw [compl_compl t]
      exact le)
  
  def le_f_of_cpl_le
    [CompleteBooleanAlgebra T]
    (f: T →o T)
    (le: f.cplDual t ≤ t)
  :
    tᶜ ≤ f tᶜ
  :=
    compl_le_iff_compl_le.mp le
  
  def f_le_of_le_cpl
    [CompleteBooleanAlgebra T]
    (f: T →o T)
    (le: t ≤ f.cplDual t)
  :
    f tᶜ ≤ tᶜ
  :=
    le_compl_iff_le_compl.mp le
  
end fpHelpers

def fixedPoints.lfp_eq_gfp_dual_cpl
  [CompleteBooleanAlgebra T]
  (f: T →o T)
:
  OrderHom.lfp f = (OrderHom.gfp f.cplDual)ᶜ
:=
  le_antisymm
    (le_compl_iff_le_compl.mp
      (sSup_le fun _ tIn =>
        le_compl_iff_le_compl.mp
          (sInf_le (fpHelpers.f_le_of_le_cpl f tIn))))
    (le_sInf fun _ tIn =>
      compl_le_iff_compl_le.mp
        (le_sSup (fpHelpers.le_cpl_of_f_le f tIn)))

def fixedPoints.gfp_eq_lfp_dual_cpl
  [CompleteBooleanAlgebra T]
  (f: T →o T)
:
  OrderHom.gfp f = (OrderHom.lfp f.cplDual)ᶜ
:=
  le_antisymm
    (sSup_le fun _ tIn =>
      le_compl_iff_le_compl.mp
        (sInf_le (fpHelpers.cpl_le_of_le_f f tIn)))
    (compl_le_iff_compl_le.mp
      (le_sInf fun _ tIn =>
        compl_le_iff_compl_le.mp
          (le_sSup (fpHelpers.le_f_of_cpl_le f tIn))))


def principle_of_induction
  [CompleteLattice T]
  (f: T →o T) -- represents an inductive type
  (le: f motive ≤ motive) -- the inductive premise
:
  -- "all elements of `f` satisfy the motive"
  OrderHom.lfp f ≤ motive
:=
  sInf_le le

def principle_of_coinduction
  [CompleteLattice T]
  (f: T →o T) -- represents a coinductive type
  (le: motive ≤ f motive) -- the coinductive premise
:
  -- "all objects satisfying the motive are elements of `f`"
  motive ≤ OrderHom.gfp f
:=
  le_sSup le


/-
  Note: I'm using some Lean slang in here. (Eg. "motive" = the
  predicate to be proven by induction.) Good understanding of Lean
  is a prerequisite here. Also, this is according my understanding,
  I could be wrong here.
  
  An attempt to restate the principle of coinduction in a way slightly
  more similar to Lean's recursors. It is still pretty far off,
  because Lean has native support for inductive types (and therefore
  for induction in Lean, `f` is not an explicit parameter. Instead,
  Lean generates a custom inductive rule for each inductive type in
  the form of a recursor.)
  
  Induction shows that an element of a type satisfies the motive.
  Coinduction shows that an element satisfying the motive belongs
  to the coinductively defined set (that would be a coinductive
  type if Lean had them).
  
  To coinductively show that `motive t → Q t` requires the following:
  0. Define an operator `f` such that `gfp f: T → Prop` equals (or
  at least implies) `Q`.
  1. Prove `convert: gfp f t → B t`
  2. Show that the motive satisfies the coinductive premises.
  
  The steps 0 and 1 would not be necessary if there was native
  support for coinduction in Lean.
-/
def coinduction
  (f: Set T →o Set T)
  (motive: Set T)
  (le: motive ≤ f motive)
  (motiveT: motive t)
:
  OrderHom.gfp f t
:=
  principle_of_coinduction f le motiveT






def Operator T := T → T

structure Pair (A B: Type*) where
  zth: A
  fst: B

def Srem T := Nat → T
def Srem.head (s: Srem T) := s 0
def Srem.tail (s: Srem T) := s ∘ Nat.succ

-- Because Lean does not have coinductive types, we need to define
-- Srem.Lt by defining its complement inductively.
-- (As proven above, a greatest fixed point can be defined as the
-- complement of a least fixed point of the dual operator.)
-- TODO recheck -- should we be defining nlt or nle, and is the
-- definition correct?
inductive Srem.Nle [PartialOrder T]: (a b: Srem T) → Prop
| Head (hgt: b.head < a.head): Srem.Nle a b
| Tail (heq: a.head = b.head) (tnlt: Srem.Nle a.tail b.tail): Srem.Nle a b

def Srem.Lt [PartialOrder T] (a b: Srem T) := ¬ Srem.Nle a b

def Srem.Lt.F
  [PartialOrder T]
:
  Set (Pair (Srem T) (Srem T)) →o Set (Pair (Srem T) (Srem T))
:= {
  toFun :=
    fun pairs pair =>
      pair.zth.head < pair.fst.head ∨
      pairs (Pair.mk pair.zth.tail pair.fst.tail)
  monotone' :=
    fun
    | _s0, _s1, _sLe, _pair, Or.inl headLe =>
      Or.inl headLe
    | _s0, _s1, sLe, _pair, Or.inr tailIn =>
      Or.inr (sLe tailIn)
}


def Srem.LtEq
  {a b: Srem T}
  [PartialOrder T]
:
  Lt a b ↔ Pair.mk a b ∈ OrderHom.gfp Lt.F
:=
  fixedPoints.gfp_eq_lfp_dual_cpl
    (T := Set (Pair (Srem T) (Srem T)))
    Lt.F ▸
  Iff.intro
    (fun ab inLfp => sorry)
    (fun ninLfp ab => sorry)


def Srem.le_trans
  [PartialOrder T]
  {a b c: Srem T}
  (ab: Lt a b)
  (bc: Lt b c)
:
  Lt a c
:=
  LtEq.mpr
    (coinduction
      Lt.F
      (fun pair => Lt pair.zth pair.fst)
      sorry
      sorry)

inductive NatList.Lt: List Nat → List Nat → Prop
| Head (lt: h0 < h1) (t0 t1: List Nat): Lt (h0 :: t0) (h1 :: t1)
| Tail (n) (ltTail: Lt t0 t1): Lt (n :: t0) (n :: t1)


def NatList.lt_trans_str
  {a b c: List Nat}
:
  Lt a b → Lt b c → Lt a c
|
  .Head ab _ _, .Head bc _ _ => .Head (ab.trans bc) _ _
| .Head ab _ _, .Tail _ _ => .Head ab _ _
| .Tail _ _, .Head ab _ _ => .Head ab _ _
| .Tail _ ab, .Tail _ bc => .Tail _ (lt_trans_str ab bc)

#print NatList.lt_trans_str

def NatList.lt_trans_match
  {a b c: List Nat}
  (ab: Lt a b)
  (bc: Lt b c)
:
  Lt a c
:=
  match ab, bc with
  |
    .Head ab _ _, .Head bc _ _ => .Head (ab.trans bc) _ _
  | .Head ab _ _, .Tail _ _ => .Head ab _ _
  | .Tail _ _, .Head ab _ _ => .Head ab _ _
  | .Tail _ ab, .Tail _ bc => .Tail _ (lt_trans_match ab bc)

#print NatList.lt_trans_match

def A := Nat.brecOn

def NatList.lt_trans
  {a b c: List Nat}
  (ab: Lt a b)
  (bc: Lt b c)
:
  Lt a c
:=
  a.rec
    (motive := fun l0 => ∀ l1 l2, sorry)
    sorry
    sorry



-- TODO an implementation of Stream that follows
-- https://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf

-- TODO coinductive reasoning / proof system for ETST subtyping?
-- It will likely be necessary for complements anyway.
