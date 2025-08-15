import old.HM.HamkinsMachine


-- A (hopefully, to be proven) sound and complete, conservative
-- extension of Hamkins machines, that ought to be more user-friendly
-- for writing useful programs, and more convenient to reason about.
-- TODO work in progress.
inductive HmProgram:
  -- A set of input values that are guaranteed to terminate. Might
  -- be left empty if one is not interested in analyzing termination.
  (terminatesIf: Set Nat2) →
  -- A set of input values for which there is a postcondition.
  -- Values not in the precondition are still allowed as arguments,
  -- but nothing is guaranteed about the output.
  (precond: Set Nat2) →
  -- For each input value satisfying the precondition, a set of
  -- output values that is guaranteed to contain the result of
  -- the computation. Can be thought of as a dependent return type
  -- of the program.
  (postcond: ↑precond → Set Nat2) →
  Type 1
where
  | hm
      (hm: HamkinsMachine)
      
      (precond: Set Nat2)
      (postcond: ↑precond → Set Nat2)
      
      (isSound: ∀ (input: ↑precond) (output: Nat2),
        hm.fn input = output → output ∈ postcond input)
      
      (isSoundTerminates: ∀ input: ↑precond, hm.fn input ≠ none)
    :
      HmProgram terminatesIf precond postcond
  | ite
      (index: Nat)
      (a: HmProgram aTerminates aPrecond aPostcond)
      (b: HmProgram bTerminates bPrecond bPostcond)
      
      (precond: Set Nat2)
      (postcond: ↑precond → Set Nat2)
      
      (terminatesIf: Set Nat2)
      
      (isSoundPrecond:
        ∀ input: ↑precond,
          (input.val index = Two.one → aPrecond input) ∧
          (input.val index = Two.zero → bPrecond input))
      
      (isSoundPostcondA:
        ∀ input: ↑precond,
          (condTrue: input.val index = Two.one) →
            let apr: aPrecond input := (isSoundPrecond input).left condTrue
            aPostcond ⟨input, apr⟩ ⊆ postcond input)
      
      (isSoundPostcondB:
        ∀ input: ↑precond,
          (condFalse: input.val index = Two.zero) →
            let bpr: bPrecond input := (isSoundPrecond input).right condFalse
            bPostcond ⟨input, bpr⟩ ⊆ postcond input)
      
      (isSoundTerminatesA: ∀ input: ↑precond,
        terminatesIf input → input.val index = Two.one → aTerminates input)
      
      (isSoundTerminatesB: ∀ input: ↑precond,
        terminatesIf input → input.val index = Two.zero → bTerminates input)
    :
      HmProgram terminatesIf precond postcond
  | while
      (cond: Nat)
      (body: HmProgram bTerminates bPrecond bPostcond)
      
      (precond: Set Nat2)
      (postcond: ↑precond → Set Nat2)
      
      (terminatesIf: Set Nat2)
      
      (variant: (a b: Nat2) → Prop)
      (variantTransitive:
        (ab: variant a b) →
        (bc: variant b c) →
        variant a c)
      
      (isSoundPrecond: ∀ input: ↑precond,
        input.val cond = Two.one → bPrecond input)
      
      (isSoundPostcondStep:
        ∀ input: ↑precond,
          (condTrue: input.val cond = Two.one) →
          let bpr := isSoundPrecond input condTrue
          bPostcond ⟨input, bpr⟩ ⊆ precond)
      
      -- TODO
      -- (isSoundPostcondLim:
      --   ∀ (input: ↑precond)
      --     (seq: HmProgram.TapeSeq cond input isSoundPrecond bPostcond)
      --   ,
      --     (seq.limSup ∈ precond))
      
      (isSoundTerminates:
        ∀ (input: ↑precond)
           (condT: input.val cond = Two.one)
           (output: ↑(bPostcond ⟨input, isSoundPrecond input condT⟩))
          ,
           variant input output)
    :
      HmProgram terminatesIf precond postcond
