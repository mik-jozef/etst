/-
  General stuff related to fixed points.
-/

import Set
import Ordinal

open Classical


structure Tuple (T: Type u) where
  length: Ordinal
  elements: ↑length → T

instance: Membership T (Tuple T) where
  mem := fun (t: T) (tuple: Tuple T) => ∃ n: ↑tuple.length, tuple.elements n = t

instance: Coe (Tuple T) (Set T) where
  coe tuple := fun t: T => t ∈ tuple

-- Why u no work?
instance: Coe (Tuple T) Type where
  coe tuple := { t: T // t ∈ tuple }

namespace Tuple
  def empty: Tuple T := {
    length := 0
    elements := fun n => False.elim (Ordinal.zero.nGreater n n.property)
  }
  
  def Len (T: Type) (length: Ordinal) := { t: Tuple T // t.length = length }
  
  def zeroth (tuple: Tuple T) (hasZeroth: 0 < tuple.length): T :=
    tuple.elements ⟨0, hasZeroth⟩
  
  -- Dear world, please, index things right.
  def first (tuple: Tuple T) (hasFirst: 1 < tuple.length): T :=
    tuple.elements ⟨1, hasFirst⟩
  
  noncomputable def last (tuple: Tuple T) (nLimit: ¬ tuple.length.isLimit): T :=
    let i := Ordinal.pred.nLimit tuple.length nLimit
    tuple.elements ⟨
      i,
      Ordinal.predLt tuple.length i (Ordinal.succ.pred.eq i.property)
    ⟩
  
  def isElement (tuple: Tuple T): Set T := fun t: T => t ∈ tuple
  def Element (tuple: Tuple T): Type := { t: T // t ∈ tuple }
  
  noncomputable def append (tuple: Tuple T) (t: T): Tuple T := {
    length := tuple.length.succ
    elements :=
      fun n =>
        if h: n = tuple.length then
          t
        else
          tuple.elements ⟨
            n,
            (Ordinal.lt.succ.le n.property).elim id (fun eq => False.elim (h eq))
          ⟩
  }
  
  def cut (tuple: Tuple T) (newLength: ↑tuple.length.succ): Tuple T :=
    let le: newLength ≤ tuple.length := Ordinal.lt.succ.le newLength.property
    {
      length := newLength
      elements := fun n => tuple.elements ⟨n, Ordinal.ltle.trans n.property le⟩
    }
  
  def isPrefix.withLength (a b: Tuple T) (ab: a.length ≤ b.length): Prop :=
    ∀ i: ↑a.length, a.elements i = b.elements ⟨i, Ordinal.ltle.trans i.property ab⟩
  
  def isPrefix (a b: Tuple T): Prop := 
    if ab: a.length ≤ b.length then
      b.cut ⟨a.length, Ordinal.le.succ.lt ab⟩ = a
    else
      False
  
  def isPrefix.le (a b: Tuple T) (pref: isPrefix a b): a.length ≤ b.length :=
    byContradiction fun nab =>
      let prefFalse: isPrefix a b = False := dif_neg nab
      cast prefFalse pref
  
  /- TODO lots of unused code here
  def isPrefix.eq (a b: Tuple T) (pref: isPrefix a b) (i: ↑a.length):
    a.elements i = b.elements
      ⟨i, Ordinal.ltle.trans i.property (isPrefix.le a b pref)⟩
  :=
    sorry-/
  
  def isMono [ord: PartialOrder T] (tuple: Tuple T): Prop :=
    ∀ i0 i1: ↑tuple.length,
      i0.val < i1.val → ord.le (tuple.elements i0) (tuple.elements i1)
  def Mono (T: Type) [PartialOrder T] := { ch: Tuple T // isMono ch }
  
  -- def isChain [ord: PartialOrder T] (tuple: Tuple T): Prop :=
  --   ∀ t0 t1: ↑tuple, ord.le t0 t1 ∨ ord.le t1 t0
  -- def Chain (T: Type) [_ord: PartialOrder T] := { ch: Tuple T // isChain ch }

  /-def isChain.not.exIncomparable
    [ord: PartialOrder T]
    (tuple: Tuple T)
    (nChain: ¬ tuple.isChain)
  :
    ∃ t0 t1: ↑tuple, ¬  ord.le t0 t1 ∧ ¬ ord.le t1 t0
  :=
    sorry-/
end Tuple


section ord
  variable [ord: PartialOrder T]
  
  def isMonotonic (op: T → T): Prop := ∀ t0 t1: T, t0 ≤ t1 → op t0 ≤ op t1
  
  def isChain (s: Set T): Prop := ∀ t0 t1: ↑s, ord.le t0 t1 ∨ ord.le t1 t0
  def Chain (T: Type) [_ord: PartialOrder T] := { ch: Set T // isChain ch }
  
  def Chain.option.some (chainOpt: @Chain (Option T) ord.option): Chain T := ⟨
      fun t => chainOpt.val t,
      fun t0 t1 =>
        (chainOpt.property ⟨t0, t0.property⟩ ⟨t1, t1.property⟩).elim
          (fun lt01 => Or.inl lt01)
          (fun lt10 => Or.inr lt10)
    ⟩
  
  
  def isLeast (s: Set T): Set T :=
    fun t: T => t ∈ s ∧ ∀ tt: T, tt ∈ s → t < tt ∨ t = tt
  def Least (s: Set T) := { t: T // isLeast s t }
  
  
  def isUpperBound (s: Set T): Set T := fun t: T => ∀ tt: ↑s, tt ≤ t
  def UpperBound (s: Set T) := { t: T // isUpperBound s t }
  
  
  def isSupremum (s: Set T) := isLeast (isUpperBound s)
  def Supremum (s: Set T) := Least (isUpperBound s)
  
  def chainComplete (_: PartialOrder T): Prop :=
    ∀ ch: Chain T, ∃ t: T, isSupremum ch.val t
  
  noncomputable def Chain.sup
    (ch: Chain T)
    (cc: chainComplete ord)
  :
    Supremum ch.val
  :=
    choiceEx (cc ch)
  
  
  noncomputable def chainComplete.option.chain.sup
    (cc: chainComplete ord)
    (chainOpt: @Chain (Option T) ord.option)
  :
    { t // @isSupremum (Option T) ord.option chainOpt.val t }
  :=
    let chain: Chain T := Chain.option.some chainOpt
    let supChain := (_root_.Chain.sup chain cc)
    
    ⟨
      if none ∈ chainOpt.val then
        none
      else
        supChain.val,
      And.intro
        (if h: none ∈ chainOpt.val then
          if_pos h ▸ (fun t => PartialOrder.option.noneGe t.val)
        else
          if_neg h ▸ fun tSome =>
            match hh: tSome.val with
              | none => h (hh ▸ tSome.property)
              | some t =>
                  let tOptIn: some t ∈ chainOpt.val := hh ▸ tSome.property
                  let tInChain: t ∈ chain.val := tOptIn
                  supChain.property.left ⟨t, tInChain⟩)
        fun upperBound ubIsUpperBound =>
          if h: none ∈ chainOpt.val then
            match hh: upperBound with
              | none => if_pos h ▸ (Or.inr (hh ▸ rfl))
              | some _ => False.elim (ubIsUpperBound ⟨none, h⟩)
          else
            if_neg h ▸ match upperBound with
              | none =>
                  Or.inl (And.intro trivial Option.noConfusion)
              | some ub =>
                  let ubIsUB: isUpperBound chain.val ub :=
                    fun t => ubIsUpperBound ⟨t, t.property⟩
                  let ubLT := supChain.property.right ub ubIsUB
                  ubLT.elim
                    (fun lt => Or.inl (PartialOrder.option.lt.toOpt lt))
                    (fun eq => Or.inr (congr rfl eq))
    ⟩
  
  def chainComplete.option (cc: chainComplete ord): chainComplete ord.option :=
    fun chainOpt => ⟨
      chainComplete.option.chain.sup cc chainOpt,
      (chainComplete.option.chain.sup cc chainOpt).property
    ⟩
  
  noncomputable def sup.eq
    (ch: Chain T)
    (a b: Supremum ch.val)
  :
    a = b
  :=
    let abLtEq := (a.property.right b.val b.property.left)
    let baLtEq := (b.property.right a.val a.property.left)
    
    let abLe := (ord.leIffLtOrEq a.val b.val).mpr abLtEq
    let baLe := (ord.leIffLtOrEq b.val a.val).mpr baLtEq
    
    Subtype.eq (PartialOrder.antisymm a.val b.val abLe baLe)
  
  def sup.none.has
    (cc: chainComplete ord)
    (chain: @Chain (Option T) ord.option)
    (hasNone: none ∈ chain.val)
  :
    (@_root_.Chain.sup (Option T) ord.option chain cc.option).val = none
  :=
    let _ := ord.option
    
    let chainSupCc := chainComplete.option.chain.sup cc chain
    let chainSupSup := _root_.Chain.sup chain cc.option
    
    let eq := sup.eq chain chainSupSup chainSupCc
    let eqVal: chainSupSup.val = chainSupCc.val := congr rfl eq
    
    let supNone: chainSupCc.val = Option.none :=
      dif_pos hasNone
    eqVal.trans supNone
  
  def sup.none.nHas
    (cc: chainComplete ord)
    (ch: @Chain (Option T) ord.option)
    (noneFree: none ∉ ch.val)
  :
    (@Chain.sup (Option T) ord.option ch cc.option).val ≠ none
  :=
    let _ := ord.option
    
    let chainSupCc := chainComplete.option.chain.sup cc ch
    let chainSupSup := ch.sup cc.option
    
    let eq := sup.eq ch chainSupSup chainSupCc
    let eqVal: chainSupSup.val = chainSupCc.val := congr rfl eq
    
    let supNotNone: chainSupCc.val ≠ Option.none :=
      fun eq =>
        let chain: Chain T := Chain.option.some ch
        let supEq: chainSupCc.val = some (chain.sup cc).val :=
          dif_neg noneFree
        Option.noConfusion (eq ▸ supEq)
    
    eqVal ▸ supNotNone
  
  def Tuple.Mono.toChain
    (tuple: Tuple.Mono T)
  :
    Chain T
  :=
    ⟨
      tuple.val,
      fun t0 t1 =>
        let i0 := choiceEx t0.property
        let i1 := choiceEx t1.property
        (i0.val.val.total i1.val).elim
          (fun lt =>
            Or.inl
              (i0.property ▸ i1.property ▸ (tuple.property i0 i1 lt)))
          (fun gtOrEq =>
            gtOrEq.elim
              (fun gt =>
                Or.inr
                  (i0.property ▸ i1.property ▸ (tuple.property i1 i0 gt)))
              (fun eqIValVal =>
                let iValEq := Subtype.eq eqIValVal
                let tEq: t0 = t1 :=
                  Subtype.eq (i0.property.symm.trans (iValEq ▸ i1.property))
                Or.inl (tEq ▸ (ord.refl t0))))
    ⟩
  
  
  def ordinalRecursion
    (step: (prev: Tuple T) → T)
    (n: Ordinal)
  :
    T
  :=
    let prevElements (nn: ↑n) :=
      have: nn < n := nn.property
      ordinalRecursion step nn
    
    step {
      length := n
      elements := prevElements
    }
  termination_by ordinalRecursion step n => n
  
  def ordinalRecursion.mono -- TODO do I need you?
    {nn n : Ordinal}
    (step: (prev: Tuple T) → T)
    (stepMono:
      ∀ (tuple: Tuple T) (i: ↑tuple.length),
        tuple.elements i ≤ step tuple)
    (ltN: nn < n)
  :
    ordinalRecursion step nn ≤ ordinalRecursion step n
  :=
    let nn: ↑n := ⟨nn, ltN⟩
    
    let prevElements (nn: ↑n) := ordinalRecursion step nn
    let tuple: Tuple T := {
      length := n
      elements := prevElements
    }
    
    let eq: step tuple = ordinalRecursion step n :=
      by unfold ordinalRecursion; rfl
    let mono: ordinalRecursion step nn ≤ step tuple := stepMono tuple nn
    eq ▸ mono
  
  noncomputable def lfp.option.step
    (cc: chainComplete ord)
    (op: T → T)
    (prev: Tuple (Option T))
  :
    Option T
  :=
    let _ := ord.option
    
    if h: prev.length.isLimit then
      if hh: prev.isMono then
        ((Tuple.Mono.toChain ⟨prev, hh⟩).sup cc.option).val
      else
        none
    else
      let nn: { nn // nn.succ = prev.length } := Ordinal.pred.nLimit prev.length h
      let lt: nn < prev.length := Ordinal.pred.nLimit.lt prev.length h
      
      match prev.elements ⟨nn, lt⟩ with
        | none => none
        | some t => op t
  
  noncomputable def lfp.option.stage
    (cc: chainComplete ord)
    (op: T → T)
    (n: Ordinal)
  :
    Option T
  :=
    ordinalRecursion (step cc op) n
  
  @[reducible] noncomputable def lfp.option.stage.prev
    (cc: chainComplete ord)
    (op: T → T)
    (n: Ordinal)
  :
    Tuple (Option T)
  := {
    length := n,
    elements :=
      fun nn =>
        have: nn < n := nn.property
        stage cc op nn
  }
  
  @[reducible] noncomputable def lfp.option.stage.prev.lengthEq
    (cc: chainComplete ord)
    (op: T → T)
    (n: Ordinal)
  :
    (prev cc op n).length = n
  :=
    rfl
  
  def lfp.opOption (op: T → T): (Option T) → (Option T)
    | none => none
    | some t => op t
  
  
  structure lfp.option.stages.Props
    (cc: chainComplete ord)
    (op: T → T)
    (nn n: Ordinal)
    (leNn: nn ≤ n)
  where
    prev: Tuple (Option T)
    prevLength: prev.length = n
    prevEq: (nn: ↑n) →
      prev.elements ⟨nn, prevLength ▸ nn.property⟩ = stage cc op nn
    prevIsMono: @Tuple.isMono (Option T) ord.option prev
    
    notNone: stage cc op n ≠ none
    isMono: ord.option.le (stage cc op nn) (stage cc op n)
    succStep: (h: ¬ n.isLimit) →
      stage cc op n = opOption op (stage cc op (Ordinal.pred.nLimit n h))
    limitStep: n.isLimit →
      stage cc op n =
        (@Chain.sup
          (Option T) ord.option
          (@Tuple.Mono.toChain (Option T) ord.option ⟨prev, prevIsMono⟩)
          cc.option).val
  
  
  
  -- This is what happens when Lean does not allow a function
  -- to mention itself in its return type.
  noncomputable def lfp.option.stages.props
    (cc: chainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (nn n: Ordinal)
    (leNn: nn ≤ n)
  :
    stages.Props cc op nn n leNn
  :=
    let _ := ord.option
    let stageN := stage cc op n
    let stageNn := stage cc op nn
    
    let prev: Tuple (Option T) := stage.prev cc op n
    
    let eq n: prev.elements n = stage cc op n := rfl
    
    let prevIsMono: prev.isMono :=
      fun nnn nn ltNnn =>
        have: nn < n := nn.property
        (eq nnn) ▸ (eq nn) ▸
          (stages.props cc op opMono nnn nn (Or.inl ltNnn)).isMono
    
    let prevIsSome: none ∉ prev :=
      fun noneIn =>
        let i := choiceEx noneIn
        let neqNone: stage cc op i.val ≠ none :=
          have: i.val < n := i.val.property
          (stages.props cc op opMono i.val i.val (Or.inr rfl)).notNone
        neqNone i.property
    
    let prevMono: Tuple.Mono (Option T) := ⟨prev, prevIsMono⟩
    let prevChain := Tuple.Mono.toChain prevMono
    let supPrevChain := prevChain.sup cc.option
      
    if h: n.isLimit then
      let stepPrevEq: step cc op prev = supPrevChain.val := by
        unfold step
        rw [dif_pos h]
        rw [dif_pos prevIsMono]
      
      let stageNEq: stage cc op n = supPrevChain.val :=
        let stageNLeft: stage cc op n = step cc op prev := by
          unfold stage
          unfold ordinalRecursion
          rfl
        stageNLeft.trans stepPrevEq
      
      let isMono: stageNn ≤ supPrevChain.val :=
        if h: nn = n then
          (ord.option.leIffLtOrEq stageNn supPrevChain.val).mpr
            (Or.inr (stageNEq ▸ h ▸ rfl))
        else
          let nn := ⟨nn, Ordinal.le.lt leNn h⟩
          let eqMono: prev.elements nn = Tuple.elements prevMono.val nn := rfl
          supPrevChain.property.left
            ⟨stageNn, ⟨nn, eqMono ▸ (eq nn)⟩⟩
      
      {
        prev := prev
        prevLength := rfl
        prevEq := eq
        prevIsMono := prevIsMono
        
        notNone := stageNEq ▸ (sup.none.nHas cc prevChain prevIsSome)
        isMono := stageNEq ▸ isMono
        succStep := fun nope => False.elim (nope h)
        limitStep := fun _ => stageNEq
      }
    else
      let nPred: { nn // nn.succ = prev.length } :=
        Ordinal.pred.nLimit prev.length h
      let lt: nPred < prev.length :=
        Ordinal.pred.nLimit.lt prev.length h
      
      match hh: prev.elements ⟨nPred, lt⟩ with
        | none => False.elim (prevIsSome ⟨⟨nPred, lt⟩, hh⟩)
        | some t =>
            let nPredEqT: stage cc op nPred.val = some t := hh
            let stepPrevEq: step cc op prev = op t := by
              unfold step
              rw [dif_neg h]
              simp [hh]
            
            let stageNEqStep: stage cc op n = step cc op prev := by
                unfold stage
                unfold ordinalRecursion
                rfl
            
            let stageNEq: stage cc op n = op t :=
              stageNEqStep.trans stepPrevEq
            
            let lePrev: stage cc op nPred ≤ stage cc op n :=
              if hhh: nPred.val.isLimit then
                let props := stages.props cc op opMono nPred nPred (Or.inr rfl)
                
                let predPrev := props.prev
                
                let eqPred n: predPrev.elements n = stage cc op n :=
                  props.prevEq ⟨n, props.prevLength ▸ n.property⟩
                
                let predPrevIsMono: predPrev.isMono :=
                  fun n0 n1 ltN =>
                    (eqPred n0) ▸ (eqPred n1) ▸ (
                      have: n1 < n := Ordinal.lt.trans n1.property
                        (props.prevLength ▸ lt)
                      stages.props cc op opMono n0 n1 (Or.inl ltN)
                    ).isMono
                
                let predPrevChain :=
                  Tuple.Mono.toChain ⟨predPrev, predPrevIsMono⟩
                
                let predPrevSup := Chain.sup predPrevChain cc.option
                
                let predPrevLUB: stage cc op nPred = predPrevSup.val :=
                  props.limitStep hhh
                
                let isUB: isUpperBound predPrevChain.val (stage cc op n) :=
                  fun someTt =>
                    let ttInPredPrev: someTt.val ∈ predPrev := someTt.property
                    let ttIndex := choiceEx ttInPredPrev
                    let indexLt: ttIndex.val < nPred.val :=
                      props.prevLength ▸ ttIndex.val.property
                    let ttIndexWithLt: { nn: Ordinal // nn < nPred.val } :=
                      ⟨ttIndex.val, indexLt⟩
                    
                    let stageTtEqSomeTt: stage cc op ttIndex.val.val = someTt.val :=
                      (props.prevEq ttIndexWithLt) ▸ ttIndex.property
                    
                    match hhhh: someTt.val with
                      | none => False.elim ((
                          have: ttIndex.val < n :=
                            Ordinal.lt.trans indexLt lt
                          stages.props cc op opMono
                            ttIndex.val ttIndex.val (Or.inr rfl)
                        ).notNone (stageTtEqSomeTt.symm ▸ hhhh))
                      | some tt =>
                          let stageTtEq:
                            stage cc op ttIndex.val = some tt
                          :=
                            hhhh ▸ stageTtEqSomeTt
                          
                          let ltTtNPredStage:
                            stage cc op ttIndex.val ≤ stage cc op nPred.val
                          :=
                            (
                              stages.props cc op opMono
                                ttIndex.val nPred (Or.inl indexLt)
                            ).isMono
                          
                          let ltTtNPredSome: some tt ≤ some t :=
                            hhhh ▸ stageTtEqSomeTt ▸ nPredEqT.symm ▸ ltTtNPredStage
                          
                          let ltTtNPred: tt ≤ t := ltTtNPredSome
                          
                          let opLt: op tt ≤ op t := opMono tt t ltTtNPred
                          
                          let opLt: op tt ≤ stage cc op n := stageNEq ▸ opLt
                          
                          let ttSucNLimit: ¬ (ttIndex.val.val.succ).isLimit :=
                            Ordinal.succ.hasPred ttIndex.val.val
                          
                          let ttSuccPred := Ordinal.pred.nLimit ttIndex.val.val.succ ttSucNLimit
                          let ttSuccEq: ttSuccPred = ttIndex.val.val :=
                            Ordinal.succ.inj ttSuccPred.property
                          
                          let ttLtNPred: ttIndex.val.val.succ < nPred :=
                            Ordinal.succ.ltLimit indexLt hhh
                          have: ttIndex.val.val.succ < n :=
                            Ordinal.lt.trans ttLtNPred lt
                          
                          let opEqNLimit:
                            stage cc op ttIndex.val.val.succ =
                              opOption op (stage cc op (Ordinal.pred.nLimit ttIndex.val.val.succ ttSucNLimit))
                          :=
                            (
                              stages.props cc op opMono
                                ttIndex.val.val.succ ttIndex.val.val.succ (Or.inr rfl)
                            ).succStep (Ordinal.succ.hasPred ttIndex.val.val)
                          
                          let opEq:
                            stage cc op ttIndex.val.val.succ =
                              opOption op (stage cc op ttIndex.val.val)
                          :=
                            --ttSuccEq ▸ opEqNLimit
                            by conv =>
                              rhs
                              rw [ttSuccEq.symm]; exact opEqNLimit
                          
                          let ltTtOpTtStage:
                            stage cc op ttIndex.val ≤
                              opOption op (stage cc op ttIndex.val)
                          :=
                            opEq ▸ (
                              stages.props cc op opMono
                                ttIndex.val ttIndex.val.val.succ
                                  (Or.inl (Ordinal.succGt ttIndex.val))
                            ).isMono
                          
                          let ltTtOpTt: some tt ≤ opOption op tt :=
                            stageTtEq ▸ ltTtOpTtStage
                          
                          PartialOrder.trans _ _ _ ltTtOpTt opLt
                
                let nPredLeStageN := predPrevSup.property.right stageN isUB
                predPrevLUB ▸
                  ((ord.option.leIffLtOrEq predPrevSup.val stageN).mpr nPredLeStageN)
              else
                let nPredPred: { nn // nn.succ = nPred.val } :=
                  Ordinal.pred.nLimit nPred hhh
                let ltNPredPred: nPredPred < nPred.val :=
                  Ordinal.pred.nLimit.lt nPred hhh
                let ltNPred: nPredPred < prev.length :=
                  Ordinal.lt.trans ltNPredPred lt
                
                match hhhh: prev.elements ⟨nPredPred, ltNPred⟩ with
                  | none => False.elim (prevIsSome ⟨⟨nPredPred, ltNPred⟩, hhhh⟩)
                  | some tt =>
                      let predPredLt:
                        stage cc op nPredPred ≤ stage cc op nPred
                      :=
                        (stages.props cc op opMono nPredPred nPred
                          (Or.inl ltNPredPred)).isMono
                      
                      let nPredPredEqTT: stage cc op nPredPred = some tt := hhhh
                      let stageNpredOptionEq:
                        stage cc op nPred.val = opOption op tt
                      :=
                        nPredPredEqTT ▸ (
                          stages.props cc op opMono nPred nPred (Or.inr rfl)
                        ).succStep hhh
                      
                      let ttLtTSome: some tt ≤ t :=
                        nPredPredEqTT ▸ nPredEqT ▸ predPredLt
                      let ttLtT: tt ≤ t := ttLtTSome
                      let opLt: opOption op tt ≤ op t := opMono tt t ttLtT
                      
                      stageNpredOptionEq ▸ stageNEq ▸ opLt
            
            let isMono: stage cc op nn ≤ stage cc op n :=
              leNn.elim
                (fun ltNn =>
                  let leNPred: nn ≤ nPred :=
                    Ordinal.lt.succ.le (nPred.property.symm ▸ ltNn)
                  
                  let leTNPred: stage cc op nn ≤ stage cc op nPred :=
                    (stages.props cc op opMono nn nPred leNPred).isMono
                  
                  PartialOrder.trans _ _ _ leTNPred lePrev)
                (fun eq => eq ▸ PartialOrder.refl (stage cc op n))
            
            {
              prev := prev
              prevLength := rfl
              prevEq := eq
              prevIsMono := prevIsMono
              
              notNone := stageNEq ▸ Option.noConfusion
              isMono := isMono
              succStep :=
                fun nLimit =>
                  let eqPred: nPred = Ordinal.pred.nLimit n nLimit := rfl
                  let eqT:
                    stage cc op (Ordinal.pred.nLimit n nLimit).val = t
                  :=
                    eqPred ▸ hh ▸ rfl
                  let opOptionEq := eqT ▸ rfl
                  stageNEq.trans opOptionEq
              limitStep := fun nope => False.elim (h nope)
            }
  termination_by lfp.option.stages.props cc op opMono nn n lt => n
  
  
  
  def isFixedPoint (op: T → T): Set T := fun t => t = op t
  def Lfp (op: T → T) := Least (isFixedPoint op)
  def lfp (cc: chainComplete ord) (op: T → T):
    Lfp op
  :=
    sorry
end ord
