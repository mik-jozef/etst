import Etst.WFC.Utils.Trisets.Triset

namespace Etst


namespace Pair
  /-
    A `PreTrisetPair` is either null, a pair of `PreTrisetPair`s,
    or a triset of `PreTrisetPair`s.
    
    Trisets are nonwellfounded, pairs are. (Does this mean that
    pairs are inductive and trisets coinductive?)
  -/
  inductive PreTrisetPair where
  | null
  | pair (zth fst: PreTrisetPair)
  | set (ts: PreTriset)
  
  namespace PreTrisetPair
    /-
      Encodes a `PreTrisetPair` as a raw pair.
      Contrast with `PreTriset`, where all pairs code trisets.
    -/
    def toPair: PreTrisetPair → Pair
    | .null => .pair (.nat 0) .null
    | .pair p0 p1 => .pair (.nat 0) (.pair p0.toPair p1.toPair)
    | .set ts => .pair (.nat 1) ts
    
    -- The encoding of `PreTrisetPair`s as raw pairs is injective.
    def toPair_inj {a b: PreTrisetPair} (h: a.toPair = b.toPair): a = b :=
      match a, b, h with
      | .null, .null, _ => rfl
      | .pair a0 a1, .pair b0 b1, h => by
          injection h with hTag h01
          injection h01 with h0 h1
          exact congrArg₂ pair (toPair_inj h0) (toPair_inj h1)
      | .set _, .set _, h =>
          congrArg set (Pair.noConfusion h fun _ hr => hr)
    
    
    -- Strong (a la "definite") membership, `a ∈ b`.
    def Ins: PreTrisetPair → PreTrisetPair → Prop
    | set ts, elem => ts.Ins elem.toPair
    | _, _ => False
    
    -- Weak (a la "possible") membership, `a ∈? b`.
    def Inw: PreTrisetPair → PreTrisetPair → Prop
    | set ts, elem => ts.Inw elem.toPair
    | _, _ => False
    
    -- Definite membership implies possible membership.
    def insLeInw {elem: PreTrisetPair}:
      (ts: PreTrisetPair) → ts.Ins elem → ts.Inw elem
    | set _, ins => ins.toPos
    | .null, ins => ins.elim
    | pair _ _, ins => ins.elim
    
    
    inductive TransitionLabels where
    | ins -- definite member of a triset
    | inw -- possible member of a triset
    | zth -- zeroth element of a pair
    | fst -- first element of a pair
    | isNull -- self loop that identifies null values
    
    /-
      One can transition a triset to its elements, a pair
      to its components, and null to itself.
    -/
    def transitionSystem:
      LabeledTransitionSystem TransitionLabels PreTrisetPair
    := fun
      | .ins, a, b => a.Ins b
      | .inw, a, b => a.Inw b
      | .zth, a, b => ∃ a1, a = pair b a1
      | .fst, a, b => ∃ a0, a = pair a0 b
      | .isNull, a, b => a = .null ∧ b = .null
    
    def IsBisim := transitionSystem.IsBisimilar
    
    def setoid: Setoid PreTrisetPair where
      r := IsBisim
      iseqv := transitionSystem.IsBisimilar_is_equivalence
    
  end PreTrisetPair
  
  def TrisetPair := Quotient PreTrisetPair.setoid
  
  namespace TrisetPair
    structure ExactTransStruct
      (label: PreTrisetPair.TransitionLabels)
      (a b: TrisetPair)
      (preA preB: PreTrisetPair)
    :
      Prop
    where
      aEq: a = ⟦preA⟧
      bEq: b = ⟦preB⟧
      trans: PreTrisetPair.transitionSystem label preA preB
    
    def ExactTrans
      (label: PreTrisetPair.TransitionLabels)
      (a b: TrisetPair)
    :
      Prop
    :=
      ∃ preA preB, ExactTransStruct label a b preA preB
    
    
    -- `ts` is a triset with definite member `elem`.
    def ExactIns (ts elem: TrisetPair): Prop :=
      ExactTrans .ins ts elem
    
    -- `ts` is a triset with possible member `elem`.
    def ExactInw (ts elem: TrisetPair): Prop :=
      ExactTrans .inw ts elem
    
    -- `p` is a pair with zeroth component `zth`.
    def ExactZth (p zth: TrisetPair): Prop :=
      ExactTrans .zth p zth
    
    -- `p` is a pair with first component `fst`.
    def ExactFst (p fst: TrisetPair): Prop :=
      ExactTrans .fst p fst
    
    -- `p` is null.
    def ExactNull (p: TrisetPair): Prop :=
      ExactTrans .isNull p p
    
    
    def ExactMem: TriRelation TrisetPair where
      RelDef := ExactIns
      RelPos := ExactInw
      def_le_pos
      | ⟨preA, preB, ⟨aEq, bEq, ins⟩⟩ =>
        ⟨preA, preB, ⟨aEq, bEq, PreTrisetPair.insLeInw preA ins⟩⟩
    
  end TrisetPair
end Pair
