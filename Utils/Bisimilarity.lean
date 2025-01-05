/-
  This file defines bisimilarity for state transition systems.
-/

import Mathlib.Logic.Relation


def Relation.converse
  (Relation: T → T → Prop)
:
  T → T → Prop
:=
  fun a b => Relation b a

def Relation.converseTransGenFlip
  {T: Type*}
  {Relation: T → T → Prop}
  {a b: T}
  (ab: converse (TransGen Relation) a b)
:
  TransGen (converse Relation) a b
:=
  TransGen.head_induction_on
    ab
    (fun aaRel => TransGen.single aaRel)
    (fun acRel _ acConvRelTrans =>
      TransGen.tail acConvRelTrans acRel)

def Relation.transGenConverseFlip
  {T: Type*}
  {Relation: T → T → Prop}
  {a b: T}
  (ab: TransGen (converse Relation) a b)
:
  converse (TransGen Relation) a b
:=
  TransGen.head_induction_on
    ab
    (fun abRelConv => TransGen.single abRelConv)
    (fun acRelConv _ cbRelConvTrans =>
      TransGen.tail cbRelConvTrans acRelConv)

def Relation.converseTransGenCommutes
  {T: Type*}
  (Relation: T → T → Prop)
:
  converse (TransGen Relation) = TransGen (converse Relation)
:=
  funext fun _ =>
    funext fun _ =>
      propext
        (Iff.intro
          converseTransGenFlip
          transGenConverseFlip)


structure LabeledTransitionSystem (State: Type*) where
  Labels: Type*
  isTransition: State → Labels → State → Prop

def IsSimulation
  (tranSys: LabeledTransitionSystem State)
  (Relation: State → State → Prop)
:=
  ∀ {a: State}
    {label: tranSys.Labels}
    {aNext b: State}
  ,
    Relation a b →
    tranSys.isTransition a label aNext →
  ∃ bNext: State,
    Relation aNext bNext ∧
    tranSys.isTransition b label bNext

def IsSimulation.transClosureIsSim
  (isSimulation: IsSimulation tranSys Rel)
:
  IsSimulation tranSys (Relation.TransGen Rel)
:=
  fun {_a label _aNext b} abRel isNextA =>
    open Relation.TransGen in
    head_induction_on
      (P :=
        fun a _ =>
          ∀ (label: tranSys.Labels)
            {aNext}
          ,
            tranSys.isTransition a label aNext →
          ∃ bNext,
            (Relation.TransGen Rel) aNext bNext ∧
            tranSys.isTransition b label bNext)
      abRel
      (fun abRel _l _aNext isNextA =>
        let ⟨bNext, abNextRel, isNextB⟩ :=
          isSimulation abRel isNextA
        ⟨bNext, single abNextRel, isNextB⟩)
      (fun acRel _cbRelTrans exBNext l _aNext isNextA =>
        let ⟨_bNextMid, abNextRel, isNextCB⟩ :=
          isSimulation acRel isNextA
        let ⟨bNext, bbNextRelTrans, isNextB⟩ :=
          exBNext l isNextCB
        let abNextRelTrans :=
          Relation.TransGen.head abNextRel bbNextRelTrans
        ⟨bNext, abNextRelTrans, isNextB⟩)
      label
      isNextA


structure Bisimulation
  (tranSys: LabeledTransitionSystem State)
where
  Rel: State → State → Prop
  isSimulation: IsSimulation tranSys Rel
  isSimulationConv:
    IsSimulation tranSys (Relation.converse Rel)

def Bisimulation.identity
  (tranSys: LabeledTransitionSystem State)
:
  Bisimulation tranSys
:= {
  Rel := fun a b => a = b
  isSimulation :=
    fun eq isNextA => ⟨_, rfl, eq ▸ isNextA⟩
  isSimulationConv :=
    fun eq isNextB => ⟨_, rfl, eq ▸ isNextB⟩
}

def Bisimulation.union
  (bisimA bisimB: Bisimulation tranSys)
:
  Bisimulation tranSys
:= {
  Rel := fun a b => bisimA.Rel a b ∨ bisimB.Rel a b
  isSimulation := fun
    | Or.inl abRel, isNextA =>
      let ⟨bNext, abNextRel, isNextB⟩ :=
        bisimA.isSimulation abRel isNextA
      ⟨bNext, Or.inl abNextRel, isNextB⟩
    | Or.inr abRel, isNextA =>
      let ⟨bNext, abNextRel, isNextB⟩ :=
        bisimB.isSimulation abRel isNextA
      ⟨bNext, Or.inr abNextRel, isNextB⟩
  isSimulationConv := fun
    | Or.inl baRel, isNextA =>
      let ⟨bNext, baNextRel, isNextB⟩ :=
        bisimA.isSimulationConv baRel isNextA
      ⟨bNext, Or.inl baNextRel, isNextB⟩
    | Or.inr baRel, isNextA =>
      let ⟨bNext, baNextRel, isNextB⟩ :=
        bisimB.isSimulationConv baRel isNextA
      ⟨bNext, Or.inr baNextRel, isNextB⟩
}

def Bisimulation.converse
  (bisim: Bisimulation tranSys)
:
  Bisimulation tranSys
:= {
  Rel := Relation.converse bisim.Rel
  isSimulation := bisim.isSimulationConv
  isSimulationConv := bisim.isSimulation
}

def Bisimulation.symmetricClosure
  (bisim: Bisimulation tranSys)
:
  Bisimulation tranSys
:=
  bisim.union bisim.converse
  

def Bisimulation.transitiveClosure
  (tranSys: LabeledTransitionSystem State)
  (bisim: Bisimulation tranSys)
:
  Bisimulation tranSys
:= {
  Rel := Relation.TransGen bisim.Rel
  isSimulation :=
    IsSimulation.transClosureIsSim bisim.isSimulation
  isSimulationConv :=
    Relation.converseTransGenCommutes bisim.Rel ▸
    IsSimulation.transClosureIsSim bisim.isSimulationConv
}


def IsBisimilar
  (tranSys: LabeledTransitionSystem State)
  (a b: State)
:=
  ∃ bisim: Bisimulation tranSys, bisim.Rel a b

def isEquivalence
  (tranSys: LabeledTransitionSystem State)
:
  Equivalence (IsBisimilar tranSys)
:= {
  refl :=
    fun _ => ⟨Bisimulation.identity tranSys, rfl⟩
  symm :=
    fun ⟨bisim, rel⟩ =>
      ⟨bisim.symmetricClosure, Or.inr rel⟩
  trans :=
    fun ⟨bisimA, relA⟩ ⟨bisimB, relB⟩ =>
      let bisim := (bisimA.union bisimB).transitiveClosure
      let isRel: bisim.Rel _ _ :=
        Relation.TransGen.head
          (Or.inl relA)
          (Relation.TransGen.single (Or.inr relB))
      ⟨bisim, isRel⟩
}
