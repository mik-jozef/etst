import Tuple
import Chain

noncomputable def lfp.stage.option
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
:
  Option T
:=
  let previousStages: Tuple (Option T) := {
    length := n
    elements :=
      fun nn =>
        have: nn < n := nn.property
        lfp.stage.option cc op nn
  }
  if hLim: n.IsActualLimit then
    if hChain: IsChain ord.optionTop.le previousStages then
      (cc.optionTop.supExists ⟨previousStages, hChain⟩).unwrap
    else
      none
  else
    have: n.pred < n := Ordinal.notLimitToPredLt hLim
    let prev := lfp.stage.option cc op n.pred
    
    match prev with
      | none => none
      | some t => op t
termination_by lfp.stage.option cc op n => n

noncomputable def lfp.stage.option.previous
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
:
  Tuple (Option T)
:= {
  length := n
  elements :=
    fun nn =>
      have: nn < n := nn.property
      lfp.stage.option cc op nn
}

def lfp.stage.option.previous.isChainToIsChain
  {ord: PartialOrder T}
  (isChain: IsChain ord.optionTop.le (previous cc op n))
  (nn: Ordinal)
  (nnLeN: nn ≤ n)
:
  IsChain ord.optionTop.le (Tuple.coe.coe (previous cc op nn))
:=
  IsChain.subset isChain (previous cc op nn)
    fun _t tIn => 
      let tIndex := tIn.unwrap
      ⟨
        ⟨tIndex.val, tIndex.val.property.trans_le nnLeN⟩,
        tIndex.property,
      ⟩  

noncomputable def lfp.stage.option.previous.eq
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  (nn: ↑n)
:
  (lfp.stage.option.previous cc op n).elements nn =
    lfp.stage.option cc op nn
:=
  rfl

def lfp.stage.option.limit.ifChain
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  (nIsLimit: n.IsActualLimit)
  (isChain: IsChain ord.optionTop.le (previous cc op n))
:
  IsSupremum ord.optionTop (previous cc op n) (lfp.stage.option cc op n)
:=
  let eq:
    lfp.stage.option cc op n =
      (cc.optionTop.supExists ⟨previous cc op n, isChain⟩).unwrap
  := by
    unfold lfp.stage.option;
    exact dif_pos nIsLimit ▸ dif_pos isChain ▸ rfl
  eq ▸ (cc.optionTop.supExists ⟨previous cc op n, isChain⟩).unwrap.property

def lfp.stage.option.pred.ifSome
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  (nNotLimit: ¬n.IsActualLimit)
  {t: T}
  (eqSome: option cc op n.pred = t)
:
  option cc op n = op t
:=
  by
    unfold option
    exact (dif_neg nNotLimit) ▸ eqSome ▸ rfl

def lfp.stage.option.pred.ifNone
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  (nNotLimit: ¬n.IsActualLimit)
  (eqNone: option cc op n.pred = none)
:
  option cc op n = none
:=
  by
    unfold option
    exact (dif_neg nNotLimit) ▸ eqNone.symm ▸ rfl

def lfp.stage.option.succ.ifSome
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  {t: T}
  (eqSome: option cc op n = t)
:
  option cc op n.succ = op t
:=
  pred.ifSome cc op n.succ
    (Ordinal.succ_not_limit n)
    ((Ordinal.pred_succ n).symm ▸ eqSome)

def lfp.stage.option.succ.ifNone
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (n: Ordinal)
  (eqNone: option cc op n = none)
:
  option cc op n.succ = none
:=
  pred.ifNone cc op n.succ
    (Ordinal.succ_not_limit n)
    ((Ordinal.pred_succ n).symm ▸ eqNone)

def lfp.stage.option.isMono.ifChain.limit
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
  (nIsLimit: n.IsActualLimit)
  (isChain: IsChain ord.optionTop.le (previous cc op n))
  (isMono: ∀ nn0 nn1: ↑n, nn0 ≤ nn1 →
    ord.optionTop.le (option cc op nn0) (option cc op nn1))
:
  ord.optionTop.le
    (stage.option cc op n)
    (stage.option cc op n.succ)
:=
  let _ := ord.optionTop
  
  let nIsSup := limit.ifChain cc op n nIsLimit isChain
  let nSuccIsUB:
    IsUpperBound
      (PartialOrder.optionTop ord)
      (fun t => t ∈ previous cc op n)
      (option cc op n.succ)
  :=
    fun tt =>
      let ttIndex := tt.property.unwrap
      let ttLeN: tt ≤ option cc op n := nIsSup.isMember tt
      match hTt: tt.val with
      | none =>
        let noneLeN: none ≤ option cc op n := hTt ▸ ttLeN
        let nEqNone := PartialOrder.optionTop.noneLeToEqNone noneLeN
        let nSuccEqNone := succ.ifNone cc op n nEqNone
        nSuccEqNone ▸ ord.optionTop.le_refl _
      | some ttRaw =>
        match hN :option cc op n with
        | none =>
          let nSuccEqNone := succ.ifNone cc op n hN
          nSuccEqNone ▸ trivial
        | some nRaw =>
          let ttLeNSome: some ttRaw ≤ some nRaw := hTt ▸ hN ▸ ttLeN
          let ttLeNRaw: ttRaw ≤ nRaw := ttLeNSome
          
          let opTtLeOpN: op ttRaw ≤ op nRaw := opMono ttLeNRaw
          
          let opNRawEq: option cc op n.succ = op nRaw :=
            option.succ.ifSome cc op n hN
          let opTtRawEq: option cc op ttIndex.val.val.succ = op ttRaw :=
            option.succ.ifSome cc op ttIndex.val (ttIndex.property.trans hTt)
          
          let ttIndexLeSucc:
            option cc op ttIndex ≤
            option cc op ttIndex.val.val.succ
          :=
            isMono
              ttIndex.val
              ⟨ttIndex.val.val.succ, nIsLimit.succ_lt ttIndex.val⟩
              (ttIndex.val.val.le_succ_self)
          
          let ttLeOpTt: ttRaw ≤ op ttRaw :=
            show some ttRaw ≤ op ttRaw from
            opTtRawEq.symm ▸ hTt ▸ ttIndex.property.symm.trans_le ttIndexLeSucc
          let ttLeOpN: ttRaw ≤ op nRaw := ttLeOpTt.trans opTtLeOpN
          opNRawEq ▸ ttLeOpN
  nIsSup.isLeMember nSuccIsUB

def lfp.stage.option.isMono.ifChain.{u}
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (a b: Ordinal.{u}) -- I'd make these hidden but no idea how to do termination_by
  (ab: a ≤ b)
  (isChain: IsChain ord.optionTop.le (previous cc op b))
:
  ord.optionTop.le
    (lfp.stage.option cc op a)
    (lfp.stage.option cc op b)
:=
  let _ := ord.optionTop
  
  if hEq: a = b then
    hEq ▸ ord.optionTop.le_refl (option cc op a)
  else if hLim: b.IsActualLimit then
    let isSup := option.limit.ifChain cc op b hLim isChain
    let abLt := ab.lt_of_ne hEq
    
    isSup.isMember ⟨option cc op a, ⟨⟨a, abLt⟩, rfl⟩⟩
  else
    have: b.pred < b := Ordinal.notLimitToPredLt hLim
    
    let abLt := ab.lt_of_ne hEq
    
    let aLeBPred: a ≤ b.pred :=
      let _ := Ordinal.partialOrder.toPreorder.{u}
      Ordinal.le_pred_of_lt abLt
    
    let isChainPred :=
      option.previous.isChainToIsChain isChain b.pred b.pred_le_self
    
    let abp: option cc op a ≤ option cc op b.pred :=
      option.isMono.ifChain cc op opMono a b.pred aLeBPred isChainPred
    
    let bpb: option cc op b.pred ≤ option cc op b :=
      if hPredLim: b.pred.IsActualLimit then
        let isMono (aa bb: ↑b.pred) ab :=
          let bbLtB: bb < b := bb.property.trans_le (b.pred_le_self)
          option.isMono.ifChain cc op opMono aa bb ab
            (option.previous.isChainToIsChain isChain bb (le_of_lt bbLtB))
        
        let leSuccPred :=
          ifChain.limit cc op opMono b.pred hPredLim isChainPred isMono
        let succPredEq: option cc op b.pred.succ = option cc op b :=
          congr rfl (Ordinal.succ_pred_of_not_limit hLim)
        
        succPredEq ▸ leSuccPred
      else
        match hPredPred: option cc op b.pred.pred with
        | none =>
            let bPredNone: option cc op b.pred = none :=
              lfp.stage.option.pred.ifNone cc op b.pred hPredLim hPredPred
            let bNone: option cc op b = none :=
              lfp.stage.option.pred.ifNone cc op b hLim bPredNone
            bPredNone ▸ bNone ▸ ord.optionTop.le_refl _
        | some t =>
            let bPredSome: option cc op b.pred = op t :=
              lfp.stage.option.pred.ifSome cc op b.pred hPredLim hPredPred
            let bSome: option cc op b = op (op t) :=
              lfp.stage.option.pred.ifSome cc op b hLim bPredSome
            
            let optionPredPredLe:
              option cc op b.pred.pred ≤ option cc op b.pred
            :=
              isMono.ifChain cc op opMono _ _ b.pred.pred_le_self
                (previous.isChainToIsChain isChain b.pred b.pred_le_self)
            
            let tLeOpT: t ≤ op t := show some t ≤ op t from
              bPredSome ▸ hPredPred ▸ optionPredPredLe
            
            bPredSome ▸ bSome ▸ opMono tLeOpT
    
    abp.trans bpb
termination_by lfp.stage.option.isMono.ifChain cc op opMono a b ab isChain => b

def lfp.stage.option.previous.isChain.{u}
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal.{u})
:
  IsChain ord.optionTop.le (previous cc op n)
:=
  let isMono {a b: ↑n} (ab: a ≤ b) :=
    have: b < n := b.property
    let isChainB := isChain cc op opMono b
    lfp.stage.option.isMono.ifChain cc op opMono a b ab isChainB
    
  fun t0 t0Mem t1 t1Mem _ =>
    let t0Index := t0Mem.unwrap
    let t1Index := t1Mem.unwrap
    
    if h: t0Index.val ≤ t1Index then
      Or.inl (t0Index.prop ▸ t1Index.prop ▸ isMono h)
    else
      let hReverse := le_of_lt (not_le.mp h)
      
      Or.inr (t0Index.prop ▸ t1Index.prop ▸ isMono hReverse)
termination_by lfp.stage.option.previous.isChain cc op n => n

noncomputable def lfp.stage.option.notNone
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  option cc op n ≠ none
:=
  if h: n.IsActualLimit then
    let prev := previous cc op n
    let prevIsChain := previous.isChain cc op opMono n
    let isSup := limit.ifChain cc op n h prevIsChain
    let supNoneIffNoneIn := IsChainComplete.supNoneIffNoneIn
      cc ⟨prev, prevIsChain⟩ ⟨option cc op n, isSup⟩
    let noneNinPrev: none ∉ prev :=
      fun noneInPrev =>
        let noneIndex := noneInPrev.unwrap
        have: noneIndex < n := noneIndex.val.property
        let neqNone := notNone cc op opMono noneIndex
        neqNone noneIndex.property
    
    supNoneIffNoneIn.not.mpr noneNinPrev
  else
    have: n.pred < n := Ordinal.notLimitToPredLt h
    let predNotNone := notNone cc op opMono n.pred
    let nPred: { t: T // option cc op n.pred = t } :=
      match h: option cc op n.pred  with
      | none => False.elim (predNotNone h)
      | some t => ⟨t, rfl⟩
    let optN := pred.ifSome cc op n h nPred.property
    fun eq => Option.noConfusion (eq.symm.trans optN)
termination_by lfp.stage.option.notNone cc op opMono n => n


noncomputable def lfp.stage.withEq
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  { t: T // t = stage.option cc op n }
:=
  match h: stage.option cc op n with
  | none => False.elim (stage.option.notNone cc op opMono n h)
  | some t => ⟨t, rfl⟩

noncomputable def lfp.stage
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  T
:=
  (stage.withEq cc op opMono n).val

def lfp.stage.eqOption
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  stage cc op opMono n = option cc op n
:=
  (stage.withEq cc op opMono n).property

def lfp.stage.isMono
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  {a b: Ordinal}
  (ab: a ≤ b)
:
  ord.le
    (lfp.stage cc op opMono a)
    (lfp.stage cc op opMono b)
:=
  let _ := ord.optionTop
  
  let stageA := lfp.stage.withEq cc op opMono a
  let stageB := lfp.stage.withEq cc op opMono b
  
  let aEq: option cc op a = stageA := stageA.property.symm
  let bEq: option cc op b = stageB := stageB.property.symm
  
  let isChain := option.previous.isChain cc op opMono b
  let opAB := option.isMono.ifChain cc op opMono a b ab isChain
  
  show some stageA.val ≤ some stageB.val from aEq ▸ bEq ▸ opAB

noncomputable def lfp.stage.previous
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  Tuple T
:= {
  length := n,
  elements := fun nn => stage cc op opMono nn
}

def lfp.stage.previous.eqOption
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
  (nn: ↑n)
:
  (previous cc op opMono n).elements nn =
    (option.previous cc op n).elements nn
:=
  stage.eqOption cc op opMono nn

def lfp.stage.limit
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  {n: Ordinal}
  (nLim: n.IsActualLimit)
:
  IsSupremum ord (previous cc op opMono n) (stage cc op opMono n)
:=
  let _ := ord.optionTop
  
  let isChain := option.previous.isChain cc op opMono n
  let isSupOpt := option.limit.ifChain cc op n nLim isChain
  let stageEq := stage.eqOption cc op opMono n
  
  {
    isMember := fun t =>
      let prevSet: Set (Option T) := option.previous cc op n
      
      let tIndex := t.property.unwrap
      
      let prevEq := previous.eqOption cc op opMono n tIndex.val
      
      let tOpt: prevSet := ⟨t, ⟨tIndex.val, prevEq ▸ (congr rfl tIndex.property)⟩⟩
      let tOptLeOptionN := isSupOpt.isMember tOpt
      
      show tOpt.val ≤ (stage cc op opMono n) from
        stageEq ▸ tOptLeOptionN
    isLeMember := fun t tUB =>
      let optNLeT := isSupOpt.isLeMember
        fun tt =>
          let ttIndex := tt.property.unwrap
          let ttRaw := stage cc op opMono ttIndex
          
          let ttRawLeT := tUB ⟨ttRaw, ⟨ttIndex.val, rfl⟩⟩
          
          let ttRawEq: some ttRaw = tt :=
            ttIndex.property ▸ (stage.eqOption cc op opMono ttIndex)
          
          ttRawEq ▸ ttRawLeT
      
      show some (stage cc op opMono n) ≤ t from
        stageEq ▸ optNLeT
  }

def lfp.stage.succ
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
:
  stage cc op opMono n.succ = op (stage cc op opMono n)
:=
  let stageEqN := stage.eqOption cc op opMono n
  let stageEqNSucc := stage.eqOption cc op opMono n.succ
  
  let optSucc := option.succ.ifSome cc op n stageEqN.symm
  
  let someEq:
    some (stage cc op opMono n.succ) = some (op (stage cc op opMono n))
  :=
    stageEqNSucc ▸ optSucc
  
  Option.noConfusion someEq id

def lfp.stage.leFP
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  (n: Ordinal)
  (fp: FixedPoint op)
:
  stage cc op opMono n ≤ fp.val
:=
  if h: n.IsActualLimit then
    let prev := previous cc op opMono n
    let stageN := stage cc op opMono n
    
    let fpIsUB: IsUpperBound ord prev fp.val :=
      fun tt =>
        let ttIndex := tt.property.unwrap
        have: ttIndex < n := ttIndex.val.property
        ttIndex.property ▸ leFP cc op opMono ttIndex fp
    
    let stageNIsLUB: IsSupremum ord prev stageN :=
      stage.limit cc op opMono h
    
    stageNIsLUB.isLeMember fpIsUB
  else
    have: n.pred < n := Ordinal.notLimitToPredLt h
    
    let stageNPred := stage cc op opMono n.pred
    
    let predLe: stageNPred ≤ fp.val := leFP cc op opMono n.pred fp
    let opPredLe: op stageNPred ≤ op fp.val := opMono predLe
    
    let opFpEq: fp.val = op fp.val := fp.property
    let stageNEq: stage cc op opMono n = op stageNPred :=
      (Ordinal.succ_pred_of_not_limit h) ▸ succ cc op opMono n.pred
    
    opFpEq ▸ stageNEq ▸ opPredLe
termination_by lfp.stage.leFP cc op opMono n fp => n


structure lfp.OrdPair (stages: Ordinal → T) where
  n0: Ordinal
  n1: Ordinal
  stagesEq: stages n0 = stages n1
  lt: n0 < n1

def Lfp
  (ord: PartialOrder T)
  (op: T → T)
:=
  Least ord (IsFixedPoint op)

def IsLfp
  (ord: PartialOrder T)
  (op: T → T)
  (t: T)
:=
  iIsLeast ord (IsFixedPoint op) t

noncomputable def lfp.fixedStage
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
:
  { n: Ordinal // IsLfp ord op (stage cc op opMono n) }
:=
  let stages: Ordinal → T := lfp.stage cc op opMono
  let stagesNotInjective := not_injective_of_ordinal stages
  
  let ⟨⟨nA, nB⟩, ⟨stageEq, nNeq⟩⟩ :=
    existsDistinctOfNotInjective stagesNotInjective
  
  let ⟨n0, n1, stageEq, nLt⟩: lfp.OrdPair stages :=
    if h: nA ≤ nB then
      ⟨nA, nB, stageEq, h.lt_of_ne nNeq⟩
    else
      ⟨nB, nA, stageEq.symm, not_le.mp h⟩
  
  let n0SuccLeN1: n0.succ ≤ n1 := Order.succ_le_of_lt nLt
  let stageN0SuccLeN1: stages n0.succ ≤ stages n1 :=
    lfp.stage.isMono cc op opMono n0SuccLeN1
  
  let stageSuccLe: stages n0.succ ≤ stages n0 := stageEq ▸ stageN0SuccLeN1
  let stageLeSucc: stages n0 ≤ stages n0.succ :=
    lfp.stage.isMono cc op opMono (Ordinal.le_succ_self n0)
  
  let stageEqSucc: stages n0 = stages n0.succ :=
    ord.le_antisymm _ _ stageLeSucc stageSuccLe
  
  let stageEqOp: stages n0.succ = op (stages n0) :=
    lfp.stage.succ cc op opMono n0
  
  ⟨
    n0,
    stageEqSucc.trans stageEqOp,
    fun t tFP => lfp.stage.leFP cc op opMono n0 ⟨t, tFP⟩,
  ⟩

noncomputable def lfp
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
:
  Lfp ord op
:=
  let fs := lfp.fixedStage cc op opMono
  
  ⟨
    lfp.stage cc op opMono fs,
    fs.property,
  ⟩

def lfp.stage.eqLfp
  {ord: PartialOrder T}
  (cc: IsChainComplete ord)
  (op: T → T)
  (opMono: IsMonotonic ord ord op)
  {nn n: Ordinal}
  (nnLe: nn ≤ n)
  (isLfpNn: IsLfp ord op (stage cc op opMono nn))
:
  IsLfp ord op (stage cc op opMono n)
:=
  let stages := stage cc op opMono
  
  let leNn: stages nn ≤ stages n :=
    lfp.stage.isMono cc op opMono nnLe
  let geNn: stages n ≤ stages nn :=
    lfp.stage.leFP cc op opMono n ⟨stages nn, isLfpNn.isMember⟩
  
  let eq: stage cc op opMono nn = stage cc op opMono n :=
    PartialOrder.le_antisymm _ _ leNn geNn
  
  eq ▸ isLfpNn
