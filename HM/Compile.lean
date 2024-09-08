import Set
import HM.Assign


namespace Program
  def compile: Program terminatesIf precond postcond →
    {
      hm: HamkinsMachine
    //
      And
        (∀ (input: ↑terminatesIf), hm.halts input)
        (∀ (input: ↑precond),
          match hm.fn tape with
          | none => True
          | some output => output ∈ postcond input)
    }
  
    | hm machine pre post isSound isSoundTerminates => sorry
    | ite cond a b precond postcond terminatesIf isSoundPrecond
        isSoundPostcondA isSoundPostcondB
        isSoundTerminatesA isSoundTerminatesB => sorry
    | Program.while cond body precond postcond terminatesIf
        variant variantTransitive isSoundPrecond
        isSoundPostcondStep isSoundPostcondLim isSoundTerminates => sorry
end Program
