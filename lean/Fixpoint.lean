/-
  General stuff related to fixed points.
-/

import Set
import Ordinal
import Hartogs

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
    let i := Ordinal.nLimit.pred tuple.length nLimit
    tuple.elements ⟨
      i,
      Ordinal.pred.lt (Ordinal.succ.pred.eq i.property)
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
  
  def isMonotonic (op: T → T): Prop := ∀ t0 t1: T, t0 .≤ t1 → op t0 .≤ op t1
  
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
    fun t: T => t ∈ s ∧ ∀ tt: T, tt ∈ s → t .≤ tt
  def Least (s: Set T) := { t: T // isLeast s t }
  
  
  def isUpperBound (s: Set T): Set T := fun t: T => ∀ tt: ↑s, tt.val .≤ t
  def UpperBound (s: Set T) := { t: T // isUpperBound s t }
  
  
  def isSupremum (s: Set T) := isLeast (isUpperBound s)
  def Supremum (s: Set T) := Least (isUpperBound s)
  
  
  def isChainComplete (_: PartialOrder T): Prop :=
    ∀ ch: Chain T, ∃ t: T, isSupremum ch.val t
  
  noncomputable def Chain.sup
    (ch: Chain T)
    (cc: isChainComplete ord)
  :
    Supremum ch.val
  :=
    choiceEx (cc ch)
  
  
  noncomputable def isChainComplete.option.chain.sup
    (cc: isChainComplete ord)
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
            match upperBound with
              | none => if_pos h ▸ (ord.option.refl none)
              | some _ => False.elim (ubIsUpperBound ⟨none, h⟩)
          else
            if_neg h ▸ match upperBound with
              | none => trivial
              | some ub =>
                  let ubIsUB: isUpperBound chain.val ub :=
                    fun t => ubIsUpperBound ⟨t, t.property⟩
                  supChain.property.right ub ubIsUB
    ⟩
  
  def isChainComplete.option (cc: isChainComplete ord): isChainComplete ord.option :=
    fun chainOpt => ⟨
      isChainComplete.option.chain.sup cc chainOpt,
      (isChainComplete.option.chain.sup cc chainOpt).property
    ⟩
  
  noncomputable def sup.eq
    {ch: Chain T}
    (a b: Supremum ch.val)
  :
    a = b
  :=
    let abLe := a.property.right b.val b.property.left
    let baLe := b.property.right a.val a.property.left
    
    Subtype.eq (PartialOrder.antisymm a.val b.val abLe baLe)
  
  def sup.none.has
    (cc: isChainComplete ord)
    (chain: @Chain (Option T) ord.option)
    (hasNone: none ∈ chain.val)
  :
    (@_root_.Chain.sup (Option T) ord.option chain cc.option).val = none
  :=
    let _ := ord.option
    
    let chainSupCc := isChainComplete.option.chain.sup cc chain
    let chainSupSup := _root_.Chain.sup chain cc.option
    
    let eq := sup.eq chainSupSup chainSupCc
    let eqVal: chainSupSup.val = chainSupCc.val := congr rfl eq
    
    let supNone: chainSupCc.val = Option.none :=
      dif_pos hasNone
    eqVal.trans supNone
  
  def sup.none.nHas
    (cc: isChainComplete ord)
    (ch: @Chain (Option T) ord.option)
    (noneFree: none ∉ ch.val)
  :
    (@Chain.sup (Option T) ord.option ch cc.option).val ≠ none
  :=
    let _ := ord.option
    
    let chainSupCc := isChainComplete.option.chain.sup cc ch
    let chainSupSup := ch.sup cc.option
    
    let eq := sup.eq chainSupSup chainSupCc
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
        tuple.elements i .≤ step tuple)
    (ltN: nn < n)
  :
    ordinalRecursion step nn .≤ ordinalRecursion step n
  :=
    let nn: ↑n := ⟨nn, ltN⟩
    
    let prevElements (nn: ↑n) := ordinalRecursion step nn
    let tuple: Tuple T := {
      length := n
      elements := prevElements
    }
    
    let eq: step tuple = ordinalRecursion step n :=
      by unfold ordinalRecursion; rfl
    let mono: ordinalRecursion step nn .≤ step tuple := stepMono tuple nn
    eq ▸ mono
  
  noncomputable def lfp.option.step
    (cc: isChainComplete ord)
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
      let nn: { nn // nn.succ = prev.length } := Ordinal.nLimit.pred prev.length h
      let lt: nn < prev.length := Ordinal.nLimit.pred.lt prev.length h
      
      match prev.elements ⟨nn, lt⟩ with
        | none => none
        | some t => op t
  
  noncomputable def lfp.option.stage
    (cc: isChainComplete ord)
    (op: T → T)
    (n: Ordinal)
  :
    Option T
  :=
    ordinalRecursion (step cc op) n
  
  @[reducible] noncomputable def lfp.option.stage.prev
    (cc: isChainComplete ord)
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
    (cc: isChainComplete ord)
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
    (cc: isChainComplete ord)
    (op: T → T)
    (nn n: Ordinal)
    (leNn: nn ≤ n)
  where
    prev: Tuple (Option T)
    prevLength: prev.length = n
    prevEq: (nn: ↑n) →
      prev.elements ⟨nn, prevLength ▸ nn.property⟩ = stage cc op nn
    prevIsMono: @Tuple.isMono (Option T) ord.option prev
    prevIsSome: none ∉ prev
    
    notNone: stage cc op n ≠ none
    isMono: ord.option.le (stage cc op nn) (stage cc op n)
    succStep: (h: ¬ n.isLimit) →
      stage cc op n = opOption op (stage cc op (Ordinal.nLimit.pred n h))
    limitStep: n.isLimit →
      stage cc op n =
        (@Chain.sup
          (Option T) ord.option
          (@Tuple.Mono.toChain (Option T) ord.option ⟨prev, prevIsMono⟩)
          cc.option).val
  
  
  
  -- This is what happens when Lean does not allow a function
  -- to mention itself in its return type.
  noncomputable def lfp.option.stages.props
    (cc: isChainComplete ord)
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
      
      let isMono: stageNn .≤ supPrevChain.val :=
        if h: nn = n then
          ord.option.ltOrEqToLe (Or.inr (stageNEq ▸ h ▸ rfl))
        else
          let nn := ⟨nn, leNn.toLt h⟩
          let eqMono: prev.elements nn = Tuple.elements prevMono.val nn := rfl
          supPrevChain.property.left
            ⟨stageNn, ⟨nn, eqMono ▸ (eq nn)⟩⟩
      
      {
        prev := prev
        prevLength := rfl
        prevEq := eq
        prevIsMono := prevIsMono
        prevIsSome := prevIsSome
        
        notNone := stageNEq ▸ (sup.none.nHas cc prevChain prevIsSome)
        isMono := stageNEq ▸ isMono
        succStep := fun nope => False.elim (nope h)
        limitStep := fun _ => stageNEq
      }
    else
      let nPred: { nn // nn.succ = prev.length } :=
        Ordinal.nLimit.pred prev.length h
      let lt: nPred < prev.length :=
        Ordinal.nLimit.pred.lt prev.length h
      
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
            
            let lePrev: stage cc op nPred .≤ stage cc op n :=
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
                            stage cc op ttIndex.val .≤ stage cc op nPred.val
                          :=
                            (
                              stages.props cc op opMono
                                ttIndex.val nPred (Or.inl indexLt)
                            ).isMono
                          
                          let ltTtNPredSome: some tt .≤ some t :=
                            hhhh ▸ stageTtEqSomeTt ▸ nPredEqT.symm ▸ ltTtNPredStage
                          
                          let ltTtNPred: tt .≤ t := ltTtNPredSome
                          
                          let opLt: op tt .≤ op t := opMono tt t ltTtNPred
                          
                          let opLt: some (op tt) .≤ stage cc op n := stageNEq ▸ opLt
                          
                          let ttSucNLimit: ¬ (ttIndex.val.val.succ).isLimit :=
                            Ordinal.succ.hasPred ttIndex.val.val
                          
                          let ttSuccPred := Ordinal.nLimit.pred ttIndex.val.val.succ ttSucNLimit
                          let ttSuccEq: ttSuccPred = ttIndex.val.val :=
                            Ordinal.succ.inj ttSuccPred.property
                          
                          let ttLtNPred: ttIndex.val.val.succ < nPred :=
                            Ordinal.succ.ltLimit indexLt hhh
                          have: ttIndex.val.val.succ < n :=
                            Ordinal.lt.trans ttLtNPred lt
                          
                          let opEqNLimit:
                            stage cc op ttIndex.val.val.succ =
                              opOption op (stage cc op (Ordinal.nLimit.pred ttIndex.val.val.succ ttSucNLimit))
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
                            stage cc op ttIndex.val .≤
                              opOption op (stage cc op ttIndex.val)
                          :=
                            opEq ▸ (
                              stages.props cc op opMono
                                ttIndex.val ttIndex.val.val.succ
                                  (Or.inl (Ordinal.succ.gt ttIndex.val))
                            ).isMono
                          
                          let ltTtOpTt: some tt .≤ opOption op tt :=
                            stageTtEq ▸ ltTtOpTtStage
                          
                          PartialOrder.trans _ _ _ ltTtOpTt opLt
                
                let nPredLeStageN := predPrevSup.property.right stageN isUB
                
                predPrevLUB ▸ nPredLeStageN
              else
                let nPredPred: { nn // nn.succ = nPred.val } :=
                  Ordinal.nLimit.pred nPred hhh
                let ltNPredPred: nPredPred < nPred.val :=
                  Ordinal.nLimit.pred.lt nPred hhh
                let ltNPred: nPredPred < prev.length :=
                  Ordinal.lt.trans ltNPredPred lt
                
                match hhhh: prev.elements ⟨nPredPred, ltNPred⟩ with
                  | none => False.elim (prevIsSome ⟨⟨nPredPred, ltNPred⟩, hhhh⟩)
                  | some tt =>
                      let predPredLt:
                        stage cc op nPredPred .≤ stage cc op nPred
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
                      
                      let ttLtTSome: some tt .≤ t :=
                        nPredPredEqTT ▸ nPredEqT ▸ predPredLt
                      let ttLtT: tt .≤ t := ttLtTSome
                      let opLt: opOption op tt .≤ op t := opMono tt t ttLtT
                      
                      stageNpredOptionEq ▸ stageNEq ▸ opLt
            
            let isMono: stage cc op nn .≤ stage cc op n :=
              leNn.elim
                (fun ltNn =>
                  let leNPred: nn ≤ nPred :=
                    Ordinal.lt.succ.le (nPred.property.symm ▸ ltNn)
                  
                  let leTNPred: stage cc op nn .≤ stage cc op nPred :=
                    (stages.props cc op opMono nn nPred leNPred).isMono
                  
                  PartialOrder.trans _ _ _ leTNPred lePrev)
                (fun eq => eq ▸ PartialOrder.refl (stage cc op n))
            
            {
              prev := prev
              prevLength := rfl
              prevEq := eq
              prevIsMono := prevIsMono
              prevIsSome := prevIsSome
              
              notNone := stageNEq ▸ Option.noConfusion
              isMono := isMono
              succStep :=
                fun nLimit =>
                  let eqPred: nPred = Ordinal.nLimit.pred n nLimit := rfl
                  let eqT:
                    stage cc op (Ordinal.nLimit.pred n nLimit).val = t
                  :=
                    eqPred ▸ hh ▸ rfl
                  let opOptionEq := eqT ▸ rfl
                  stageNEq.trans opOptionEq
              limitStep := fun nope => False.elim (h nope)
            }
  termination_by lfp.option.stages.props cc op opMono nn n lt => n
  
  
  noncomputable def lfp.stageProp
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    { t: T // lfp.option.stage cc op n = some t }
  :=
    let props := lfp.option.stages.props cc op opMono n n (Or.inr rfl)
    
    match h: lfp.option.stage cc op n with
      | none => False.elim (props.notNone h)
      | some t => ⟨t, rfl⟩
  
  noncomputable def lfp.stage
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    T
  :=
    stageProp cc op opMono n
  
  noncomputable def lfp.stage.eqOption
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    lfp.option.stage cc op n = stage cc op opMono n
  :=
    (stageProp cc op opMono n).property
  
  def lfp.stage.isMono
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    {nn n: Ordinal}
    (leN: nn ≤ n)
  :
    stage cc op opMono nn .≤ stage cc op opMono n
  :=
    let _ := ord.option
    let props := lfp.option.stages.props cc op opMono nn n leN
    
    let someLe: some (stage cc op opMono nn) .≤ some (stage cc op opMono n) :=
      (eqOption cc op opMono nn) ▸
      (eqOption cc op opMono n) ▸
        props.isMono
    
    someLe
  
  def lfp.stage.succ
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n nPred: Ordinal)
    (nPredEq: n.pred = nPred)
  :
    stage cc op opMono n = op (stage cc op opMono nPred)
  :=
    let _ := ord.option
    let props := lfp.option.stages.props cc op opMono n n (Or.inr rfl)
    
    let notLimit := Ordinal.hasPred.isNotLimit n nPred nPredEq
    let pred := Ordinal.nLimit.pred n notLimit
    
    let eqPredDot: nPred.succ = n := Ordinal.pred.succ.eq nPredEq
    let eqPred: pred = nPred := Ordinal.succ.inj (eqPredDot.symm ▸ pred.property)
    
    let someEq:
      some (stage cc op opMono n) =
        opOption op (some (stage cc op opMono pred))
    :=
      (eqOption cc op opMono n) ▸
      (eqOption cc op opMono pred) ▸
        props.succStep notLimit
    
    Option.noConfusion someEq (fun x => eqPred ▸ x)
  
  noncomputable def lfp.stage.prevTuple
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    Tuple T
  := {
    length := n
    elements := fun nn => stage cc op opMono nn
  }
  
  def lfp.stage.prevChain
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
  :
    Chain T
  :=
    Tuple.Mono.toChain ⟨
      prevTuple cc op opMono n,
      fun _ _ nlt => isMono cc op opMono (Or.inl nlt)
    ⟩
  
  def lfp.stage.limit
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    {n: Ordinal}
    (isLimit: n.isLimit)
  :
    stage cc op opMono n = ((prevChain cc op opMono n).sup cc).val
  :=
    let _ := ord.option
    let props := lfp.option.stages.props cc op opMono n n (Or.inr rfl)
    let stageN := stage cc op opMono n
    
    let prevTuple := prevTuple cc op opMono n
    let prevChain := prevChain cc op opMono n
    let prevSup := prevChain.sup cc
    
    let chainOpt := Tuple.Mono.toChain ⟨props.prev, props.prevIsMono⟩
    let chainOptSup := Chain.sup chainOpt cc.option
    let chainOpt.nHasNone: none ∉ chainOpt.val := props.prevIsSome
    
    let chainLe: ord.option.le chainOptSup.val prevSup.val :=
      let isUB: isUpperBound chainOpt.val prevSup.val :=
        fun tOpt =>
          match h: tOpt.val with
            | none => props.prevIsSome (h ▸ tOpt.property)
            | some t =>
                let tIndex := choiceEx tOpt.property
                
                let fckLean := tIndex.val.val
                let tIndexLtN: fckLean < n :=
                  props.prevLength ▸ tIndex.val.property
                let tIndexLt := ⟨tIndex.val, tIndexLtN⟩
                
                let eqSome: some (stage cc op opMono tIndexLt.val) = some t :=
                  h ▸ (eqOption cc op opMono tIndexLt).symm.trans
                  ((props.prevEq tIndexLt).symm.trans (tIndex.property))
                
                let prevTupleT: prevTuple.elements tIndexLt = t :=
                  Option.noConfusion eqSome id
                
                let tIn: t ∈ prevChain.val := ⟨tIndexLt, prevTupleT⟩
                
                prevSup.property.left ⟨t, tIn⟩
      
      chainOptSup.property.right prevSup.val isUB
    
    let chainGe: some prevSup.val .≤ chainOptSup.val :=
      match h: chainOptSup.val with
        | none => False.elim (sup.none.nHas cc chainOpt chainOpt.nHasNone h)
        | some chOptSup =>
            let isUB: isUpperBound prevChain.val chOptSup :=
              fun t =>
                let chainOptSupH: Supremum chainOpt.val :=
                  ⟨some chOptSup, h ▸ chainOptSup.property⟩
                
                let tIndex: { i // prevTuple.elements i = t } :=
                  choiceEx t.property
                
                let tIndexLtN: tIndex.val.val < props.prev.length :=
                  props.prevLength.symm ▸ tIndex.val.property
                let tIndexLt: { nn // nn < props.prev.length } :=
                  ⟨tIndex.val, tIndexLtN⟩
                let tIndexLtN: { nn // nn < n } :=
                  ⟨tIndex.val, props.prevLength ▸ tIndexLtN⟩
                
                let tIndexSomeEq:
                  some (prevTuple.elements tIndex.val) = some t.val
                :=
                  congr rfl tIndex.property
                
                let optEq: lfp.option.stage cc op tIndex.val = some t.val :=
                  (eqOption cc op opMono tIndexLt) ▸ tIndexSomeEq
                
                let propsPrevEq: props.prev.elements tIndexLt = some t.val :=
                  (props.prevEq tIndexLtN) ▸ optEq
                
                let tInChainOpt := ⟨tIndexLt, propsPrevEq⟩
                
                chainOptSupH.property.left ⟨t, tInChainOpt⟩
            
            prevSup.property.right chOptSup isUB
    
    let chainEq: chainOptSup.val = some prevSup.val :=
      ord.option.antisymm _ _ chainLe chainGe
    
    let limitStepOpt: some stageN = chainOptSup.val :=
      (eqOption cc op opMono n) ▸ props.limitStep isLimit
    
    let eqSome: some stageN = some prevSup.val := limitStepOpt.trans chainEq
    
    Option.noConfusion eqSome id
  
  
  
  def isFixedPoint (op: T → T): Set T := fun t => t = op t
  def FixedPoint (op: T → T): Type := { t: T // isFixedPoint op t }
  
  
  noncomputable def lfp.stage.fixed.index
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
  :
    { n: Ordinal // isFixedPoint op (stage cc op opMono n) }
  :=
    let stages := stage cc op opMono
    
    let pair := allOrdMapsRepeat stages
    let nn := pair.val.fst
    let n := pair.val.snd
    
    let stageN := stages n
    let stageNn := stages nn
    let stageNnSucc := stages nn.succ
    
    let stageEq: stageNn = stageN := pair.property.left
    
    let nnLeSucc: nn ≤ nn.succ := Or.inl (Ordinal.succ.gt nn)
    let nnSuccLeN: nn.succ ≤ n := Ordinal.succ.le pair.property.right
    
    let stageNnLeSucc: stageNn .≤ stageNnSucc := isMono cc op opMono nnLeSucc
    let stageNnSuccLe: stageNnSucc .≤ stageN := isMono cc op opMono nnSuccLeN
    
    let stageNnEqSucc: stageNn = stageNnSucc :=
      ord.antisymm _ _ stageNnLeSucc (stageEq ▸ stageNnSuccLe)
    
    let stageNnSuccEq: stageNnSucc = op stageNn :=
      succ cc op opMono nn.succ nn (Ordinal.succ.pred.eq rfl)
    
    let isFP: stageNn = op stageNn := stageNnSuccEq ▸ stageNnEqSucc
    
    ⟨nn, isFP⟩
  
  noncomputable def lfp.stage.fixed
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
  :
    { t: T // isFixedPoint op (t) }
  :=
    let index := lfp.stage.fixed.index cc op opMono
    
    ⟨stage cc op opMono index, index.property⟩
  
  noncomputable def lfp.stage.leFp
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (n: Ordinal)
    (fp: T)
    (fpIsFp: isFixedPoint op fp)
  :
    stage cc op opMono n .≤ fp
  :=
    if h: n.isLimit then
      let prev := lfp.stage.prevChain cc op opMono n
      let prevSup := prev.sup cc
      
      let isUB: isUpperBound prev.val fp :=
        fun tPrev =>
          let tPrevIndex := choiceEx tPrev.property
        
          have: tPrevIndex.val < n := tPrevIndex.val.property
          tPrevIndex.property ▸ leFp cc op opMono tPrevIndex.val fp fpIsFp
      
      let stageNEq: stage cc op opMono n = prevSup.val := limit cc op opMono h
      
      stageNEq ▸ prevSup.property.right fp isUB
    else
      let nPred := Ordinal.nLimit.pred n h
      
      let nPredEq: stage cc op opMono n = op (stage cc op opMono nPred) :=
        succ cc op opMono n nPred (Ordinal.succ.pred.eq nPred.property)
      
      have := Ordinal.nLimit.pred.lt n h
      let nPredLe := leFp cc op opMono nPred fp fpIsFp
      
      fpIsFp ▸ nPredEq ▸ opMono _ _ nPredLe
  termination_by lfp.stage.leFp cc op opMono n fp fpIsFp => n
  
  
  def Lfp (op: T → T) := Least (isFixedPoint op)
  noncomputable def lfp
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
  :
    Lfp op
  :=
    let fpIndex := lfp.stage.fixed.index cc op opMono
    let fp := lfp.stage.fixed cc op opMono
    
    ⟨fp.val, And.intro fp.property (lfp.stage.leFp cc op opMono fpIndex)⟩
  
  def lfp.eq
    {op: T → T}
    (a b: Lfp op)
  :
    a = b
  :=
    let ab: a.val .≤ b.val := a.property.right b.val b.property.left
    let ba: b.val .≤ a.val := b.property.right a.val a.property.left
    
    Subtype.eq (ord.antisymm a.val b.val ab ba)
  
  def lfp.stage.fixed.index.higher
    (cc: isChainComplete ord)
    (op: T → T)
    (opMono: isMonotonic op)
    (opLfp: Lfp op)
    (n: Ordinal)
    (nGe: index cc op opMono ≤ n)
  :
    stage cc op opMono n = opLfp.val
  :=
    let opLfp.standard := lfp cc op opMono
    
    let i := index cc op opMono
    
    let stageN := stage cc op opMono n
    let stageI := stage cc op opMono i
    
    let eq.left: stageI = opLfp.standard.val := rfl
    let eq.right: opLfp.standard.val = opLfp.val := congr rfl (lfp.eq _ _)
    let eq.opLfp: stageI = opLfp.val := eq.left.trans eq.right
    
    let stageN.le: stageN .≤ stageI :=
      lfp.stage.leFp cc op opMono n stageI i.property
    
    let stageN.ge: stageI .≤ stageN := lfp.stage.isMono cc op opMono nGe
    
    let eq.ni := ord.antisymm _ _ stageN.le stageN.ge
    
    eq.ni.trans eq.opLfp
end ord