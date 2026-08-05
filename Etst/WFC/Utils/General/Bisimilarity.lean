import Mathlib.Logic.Relation
import Mathlib.Tactic.TypeStar


theorem Relation.swap_comp {A B C: Sort*}
  (Ab: A → B → Prop)
  (Bc: B → C → Prop)
:
  Eq
    (Relation.Comp (Function.swap Bc) (Function.swap Ab))
    (Function.swap (Relation.Comp Ab Bc))
:=
  funext fun _ =>
  funext fun _ =>
  propext ⟨
    fun ⟨b, r2, r1⟩ => ⟨b, r1, r2⟩,
    fun ⟨b, r1, r2⟩ => ⟨b, r2, r1⟩,
  ⟩


abbrev LabeledTransitionSystem
  (L T: Type*)
:=
  L → T → T → Prop

namespace LabeledTransitionSystem
  def IsSimulation {L T}
    (lts: LabeledTransitionSystem L T)
    (R: T → T → Prop)
  :
    Prop
  :=
    ∀ l p q p', R p q → lts l p p' → ∃ q', lts l q q' ∧ R p' q'

  def IsBisimulation {L T}
    (lts: LabeledTransitionSystem L T)
    (R: T → T → Prop)
  :
    Prop
  :=
    lts.IsSimulation R ∧ lts.IsSimulation (Function.swap R)
  
  def IsBisimilar {L T}
    (lts: LabeledTransitionSystem L T)
    (p q: T)
  :
    Prop
  :=
    ∃ R, lts.IsBisimulation R ∧ R p q
  
  
  def IsSimulation.comp {L T}
    {lts: LabeledTransitionSystem L T}
    {R0 R1: T → T → Prop}
    (sim1: lts.IsSimulation R0)
    (sim2: lts.IsSimulation R1)
  :
    lts.IsSimulation (Relation.Comp R0 R1)
  :=
    fun l a c a' ⟨b, r1ab, r2bc⟩ ltsAa' =>
      let ⟨b', ltsBb', r1a'b'⟩ := sim1 l a b a' r1ab ltsAa'
      let ⟨c', ltsCc', r2b'c'⟩ := sim2 l b c b' r2bc ltsBb'
      ⟨c', ltsCc', b', r1a'b', r2b'c'⟩
  
  def IsBisimulation.comp {L T}
    {lts: LabeledTransitionSystem L T}
    {R0 R1: T → T → Prop}
    (bisim1: lts.IsBisimulation R0)
    (bisim2: lts.IsBisimulation R1)
  :
    lts.IsBisimulation (Relation.Comp R0 R1)
  := ⟨
    IsSimulation.comp bisim1.left bisim2.left,
    Relation.swap_comp R0 R1 ▸
    IsSimulation.comp bisim2.right bisim1.right,
  ⟩
  
  def IsBisimilar_is_equivalence {L T}
    (lts: LabeledTransitionSystem L T)
  :
    Equivalence (IsBisimilar lts)
  :=
    {
      refl _p := ⟨
        Eq,
        ⟨
          fun _l _a _b a' hab ltsAa' => ⟨a', hab ▸ ltsAa', rfl⟩,
          fun _l _a _b a' hba ltsAa' => ⟨a', hba.symm ▸ ltsAa', rfl⟩,
        ⟩,
        rfl,
      ⟩,
      symm bisim :=
        let ⟨R, ⟨sim, simSwap⟩, rpq⟩ := bisim
        ⟨Function.swap R, ⟨simSwap, sim⟩, rpq⟩,
      trans :=
        fun ⟨_R1, bisim1, r1⟩ ⟨_R2, bisim2, r2⟩ =>
          ⟨_, IsBisimulation.comp bisim1 bisim2, _, r1, r2⟩,
    }
  
end LabeledTransitionSystem
