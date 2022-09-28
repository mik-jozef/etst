-- I'm keeping this monster of a thing because of how bad it is.

    -- What's a normal way of proving X from `(if X then A else B) = A`?
    -- TODO ask on proofassistants
    -- Also, instead of doing this, I would rather prove that `aPred`
    -- satisfies the definition.
    let aPred: ∃ aPred: WellOrder, WellOrder.isIsomorphic aPred.succ a :=
      if isSucc: ∃ wPred: WellOrder, WellOrder.isIsomorphic wPred.succ a then
        isSucc
      else
        let nope: a.pred = none := by
          conv =>
            lhs
            unfold WellOrder.pred
            simp [isSucc]
            rfl
        let nope1: some aPred.val = none := aPred.property ▸ nope
        False.elim (Option.noConfusion nope1)
    
    
  def pred.iso
    (a b: WellOrder)
    (isIsoAB: WellOrder.isIsomorphic a b)
    (aPred: { aPred: WellOrder // a.pred = some aPred })
  :
    { bPred: WellOrder //
        b.pred = some bPred ∧ WellOrder.isIsomorphic aPred bPred }
  :=
    -- What's a normal way of proving X from `(if X then A else B) = A`?
    -- TODO ask on proofassistants
    -- Also, instead of doing this, I would rather prove that `aPred`
    -- satisfies the definition.
    -- Help, lol
    let aPredHack: { aPred: WellOrder // WellOrder.isIsomorphic aPred.succ a } :=
      if isSucc: ∃ wPred: WellOrder, WellOrder.isIsomorphic wPred.succ a then
        choiceEx isSucc
      else
        let nope: a.pred = none := by
          conv =>
            lhs
            unfold WellOrder.pred
            unfold WellOrder.predProp
            simp [isSucc]
        let nope1: some aPred.val = none := aPred.property ▸ nope
        False.elim (Option.noConfusion nope1)
    
    -- I am not a religious person, but when writing code like
    -- this, I feel like I'm sinning.
    let bPredHack: { bPred: WellOrder // WellOrder.isIsomorphic bPred.succ b } :=
      if isSucc: ∃ wPred: WellOrder, WellOrder.isIsomorphic wPred.succ a then
        ⟨aPredHack, WellOrder.isIsomorphic.trans aPredHack.property isIsoAB⟩
      else
        let nope: a.pred = none := by
          conv =>
            lhs
            unfold WellOrder.pred
            unfold WellOrder.predProp
            simp [isSucc]
        let nope1: some aPred.val = none := aPred.property ▸ nope
        False.elim (Option.noConfusion nope1)
    
    let exB: ∃ bpr, WellOrder.isIsomorphic bpr.succ b :=
      Exists.intro bPredHack.val bPredHack.property
    
    let bPred: { bPred: WellOrder //
      pred b = some bPred ∧ WellOrder.isIsomorphic aPred bPred }
    := ⟨
      choiceEx exB, -- Use axiom of choice so we can prove equality.
      And.intro (   -- Forgive me, Lord.
        by conv =>
          lhs
          unfold pred
          unfold predProp
          simp [exB]
      )
        sorry
    ⟩
    
    bPred
  