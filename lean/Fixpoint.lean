/-
  General stuff related to fixed points.
-/

import Set
import Ordinal

open Classical


structure Tuple (T: Type) where
  length: Ordinal
  elements: ↑length → T

def TupleLen (T: Type) (length: Ordinal) := { t: Tuple T // t.length = length }

instance: Membership T (Tuple T) where
  mem := fun (t: T) (tuple: Tuple T) => ∃ n: ↑tuple.length, tuple.elements n = t

instance: Coe (Tuple T) Type where
  coe tuple := { t: T // t ∈ tuple }


section ord
  variable [ord: PartialOrder T]
  
  def isMonotonic (op: T → T): Prop := ∀ t0 t1: T, t0 < t1 → op t0 < op t1
  
  def isChain (s: Set T): Prop := ∀ t0 t1: ↑s, ord.le t0 t1 ∨ ord.le t1 t0
  def Chain (T: Type) [ord: PartialOrder T] := { ch: Set T // @isChain T ord ch }


  def isLeast (s: Set T): Set T :=
    fun t: T => t ∈ s ∧ ∀ tt: T, tt ∈ s → t < tt ∨ t = tt
  def Least (s: Set T) := { t: T // isLeast s t }


  def isUpperBound (s: Set T): Set T := fun t: T => ∀ tt: ↑s, tt ≤ t
  def UpperBound (s: Set T) := { t: T // isUpperBound s t }


  def isSupremum (s: Set T) := isLeast (isUpperBound s)
  def Supremum (s: Set T) := Least (isUpperBound s)

  def chainComplete (_: PartialOrder T): Prop :=
    ∀ ch: Chain T, ∃ t: T, isSupremum ch.val t

  noncomputable def sup
    (cc: chainComplete ord)
    (ch: Chain T)
  :
    Supremum ch.val
  :=
    choiceEx (cc ch)


  def Lfp (op: T → T) := Least (fun t => t = op t)

  noncomputable def lfpStage
    (cc: chainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    T
  :=
    if h: (n.isLimit) then
      let isLesserStage: Set T :=
        fun tt => ∃ nn: ↑n,
          have: nn < n := nn.property
          lfpStage cc op opMono nn = tt
      
      let chain: Chain T := ⟨
        isLesserStage,
        fun t0 t1 =>
          let t0N := choiceEx (t0.property)
          let t1N := choiceEx (t1.property)
          sorry
      ⟩
      
      (sup cc chain).val
    else
      have: Ordinal.pred.nLimit n h < n := Ordinal.pred.nLimit.lt n h
      op (lfpStage cc op opMono (Ordinal.pred.nLimit n h))
    
    termination_by lfpStage n => n

  def lfp (cc: chainComplete ord) (op: T → T):
    Least (fun t => t = op t)
  :=
    sorry
end ord
