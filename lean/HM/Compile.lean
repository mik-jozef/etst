import Set
import HM.Assign


namespace Program
  def compile: Program lIn lOut terminatesIf precond postcond →
    {
      hm: HamkinsMachine
    //
      And
        (∀ (m: ↑terminatesIf)
          -- TODO perhaps would be better to implement m.toTape instead.
          (tape: Nat2)
          (tapeSound: ∀ locIn: lIn.Location, tape locIn.address = m.val l)
        ,
          ∃ tapeOut: Nat2, hm.fn tape = some tapeOut)
        (∀ (m: ↑precond)
          (tape: Nat2)
          (tapeSound: ∀ locIn: lIn.Location, tape locIn.address = m.val l)
          (locOut: lOut.Location)
        ,
          match hm.fn tape with
          | none => True
          | some tapeOut => Nat2.toMemory tapeOut ∈ postcond m)
    }
  
    | assign src dest precond postcond isSound =>
        ⟨
          Assign.hm src dest,
          And.intro
            (fun m tape tapeSound => sorry)
            (sorry)
        ⟩
    | ite cond a b precond postcond terminatesIf isSoundPrecond
        isSoundPostcondA isSoundPostcondB
        isSoundTerminatesA isSoundTerminatesB => sorry
    | Program.while cond body precond postcond terminatesIf
        variant variantTransitive isSoundPrecond
        isSoundPostcondStep isSoundPostcondLim isSoundTerminates => sorry
    | seq a b precond postcond terminatesIf
        isSoundPrecondA isSoundPrecondB isSoundPostcond
        isSoundTerminatesA isSoundTerminatesB => sorry
    | addPair additionalLayout precond => sorry
    | pop => sorry
end Program
