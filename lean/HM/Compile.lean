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
                  
                  let inv.eq: Assign.invariant src dest tape configN =
                    (configN.tape = (Assign.finalTape src dest tape))
                  :=-- Why does this not work??
                    -- by unfold Assign.invariant rw [configN.stateEq] rfl
                    by unfold Assign.invariant exact configN.stateEq ▸ rfl
                  let inv: configN.tape = (Assign.finalTape src dest tape) :=
                    inv.eq ▸ Assign.invariantHolds src dest tape haltN
                  
                  let isSoundM:
                    Layout.Memory.assign src dest m.val ∈ postcond m
                  :=
                    isSound m
                  
                  let mEq:
                    Layout.Memory.assign src dest m.val = Nat2.toMemory tapeOut
                  :=
                    funext fun i =>
                      sorry
                  
                  show Nat2.toMemory tapeOut ∈ postcond m from
                    mEq ▸ isSoundM)
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
