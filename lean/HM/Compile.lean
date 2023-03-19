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
          hm.halts tape)
        (∀ (m: ↑precond)
          (tape: Nat2)
          (tapeSound: ∀ locIn: lIn.Location, tape locIn.address = m.val l)
        ,
          match hm.fn tape with
          | none => True
          | some tapeOut => tapeOut.toMemory ∈ postcond m)
    }
  
    | assign src dest precond postcond isSound =>
        ⟨
          Assign.hm src dest,
          And.intro
            (fun m tape tapeSound => Assign.hm.terminates src dest tape)
            (fun m tape tapeSound =>
              match h: HamkinsMachine.fn (Assign.hm src dest) tape with
              | none => trivial
              | some tapeOut =>
                  let haltN :=
                    choiceEx (Assign.hm.terminates src dest tape)
                  
                  let configN := (Assign.hm src dest).stage tape haltN
                  let configN.stateEq: configN.state = Assign.State.halt :=
                    haltN.property
                  
                  let output := Assign.finalTape src dest tape
                  
                  let inv: configN.tape = output :=
                    (Assign.invariantsHold src dest tape haltN).left.invHalt
                       configN.stateEq
                  
                  let hc := HamkinsMachine.haltsConsistent
                    (Assign.hm src dest) tape output haltN
                    (And.intro haltN.property inv)
                  
                  let tapeEq: tapeOut = output :=
                    Option.noConfusion (h.symm.trans hc) id
                  
                  let mEq:
                    Layout.Memory.assign src dest m.val = Nat2.toMemory output
                  :=
                    funext fun i =>
                      sorry
                  
                  tapeEq ▸ show Nat2.toMemory output ∈ postcond m from
                    mEq ▸ isSound m)
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
