import Arities
import Interpretation


def operatorC (salg: Salgebra sig) (dl: DefList sig) (b: Valuation salg.D):
  Valuation salg.D → Valuation salg.D
:=
  fun c => dl.interpretation salg b c

def operatorC.isMonotonic
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  IsMonotonic
    (Valuation.ord.standard salg.D)
    (Valuation.ord.standard salg.D)
    (operatorC salg dl b)
:=
  fun cLe x =>
    Expr.interpretation.isMonotonic.standard
      salg (dl.getDef x) b cLe

noncomputable def operatorC.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  Lfp (Valuation.ord.standard salg.D) (operatorC salg dl b)
:=
  _root_.lfp
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)


noncomputable def operatorC.stage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  Valuation salg.D
:=
  lfp.stage
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

noncomputable def operatorC.fixedStage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  { n: Ordinal //
    IsLfp
      (Valuation.ord.standard salg.D)
      (operatorC salg dl b)
      (stage salg dl b n)
  }
:=
  lfp.fixedStage
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)

noncomputable def operatorC.fixedIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  { n: Ordinal //
    operatorC.stage salg dl b n = (operatorC.lfp salg dl b).val }
:= ⟨
  operatorC.fixedStage salg dl b,
  rfl,
⟩

structure operatorC.FixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (bA: Valuation salg.D)
  (bB: Valuation salg.D)
  (n: Ordinal): Prop
where
  eqLfpA: operatorC.stage salg dlA bA n = (operatorC.lfp salg dlA bA).val
  eqLfpB: operatorC.stage salg dlB bB n = (operatorC.lfp salg dlB bB).val

noncomputable def operatorC.fixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (bA: Valuation salg.D)
  (bB: Valuation salg.D)
:
  { n // operatorC.FixedIndex2 salg dlA dlB bA bB n }
:=
  let fixedA := operatorC.fixedIndex salg dlA bA
  let fixedB := operatorC.fixedIndex salg dlB bB
  
  if h: fixedA.val ≤ fixedB.val then
    ⟨
      fixedB.val,
      ⟨
        let isLfpAtB := lfp.stage.gtLfpEqLfp
          (Valuation.ord.standard.isChainComplete salg.D)
          (operatorC salg dlA bA)
          (operatorC.isMonotonic salg dlA bA)
          h
          ((operatorC.lfp salg dlA bA).property)
        
        iIsLeast.isUnique
          (Valuation.ord.standard salg.D)
          isLfpAtB
          (lfp salg dlA bA).property,
        fixedB.property,
      ⟩
    ⟩
  else
    ⟨
      fixedA.val,
      ⟨
        fixedA.property,
        let isLfpAtA := lfp.stage.gtLfpEqLfp
          (Valuation.ord.standard.isChainComplete salg.D)
          (operatorC salg dlB bB)
          (operatorC.isMonotonic salg dlB bB)
          (le_of_not_le h)
          ((operatorC.lfp salg dlB bB).property)
        
        iIsLeast.isUnique
          (Valuation.ord.standard salg.D)
          isLfpAtA
          (lfp salg dlB bB).property,
      ⟩
    ⟩

noncomputable def operatorC.stage.previous
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  Tuple (Valuation salg.D)
:=
  lfp.stage.previous
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

def operatorC.stage.limit
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
:
  IsSupremum
    (Valuation.ord.standard salg.D)
    (previous salg dl b n)
    (operatorC.stage salg dl b n)
:=
  lfp.stage.limit
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    nIsLimit

def operatorC.stage.limitAt
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
  (x: Nat)
:
  IsSupremum
    (Set3.ord.standard salg.D)
    (Set.pointwiseAt (fun d => d ∈ previous salg dl b n) x)
    (operatorC.stage salg dl b n x)
:=
  let isSup := operatorC.stage.limit salg dl b nIsLimit
  let supAt := Set.pointwiseSup.supAt ⟨_, isSup⟩ x
  
  supAt.property

def operatorC.stage.succEq
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  operatorC.stage salg dl b n.succ =
    (operatorC salg dl b) (operatorC.stage salg dl b n)
:=
  lfp.stage.succEq
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

def operatorC.stage.pred
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nNotLim: ¬n.IsActualLimit)
:
  operatorC.stage salg dl b n =
    (operatorC salg dl b) (operatorC.stage salg dl b n.pred)
:=
  let nEq: n.pred.succ = n := Ordinal.succ_pred_of_not_limit nNotLim
  let stageEq:
    operatorC.stage salg dl b n.pred.succ =
      operatorC.stage salg dl b n
  :=
    congr rfl nEq
  
  stageEq.symm.trans (succEq salg dl b n.pred)

noncomputable def operatorC.stage.eqPrevN
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nn: ↑n)
:
  operatorC.stage salg dl b nn =
    (operatorC.stage.previous salg dl b n).elements nn
:=
  rfl


def operatorC.stage.isMonotonic.approximation
  (salg: Salgebra sig)
  (dl: DefList sig)
  {b0 b1: Valuation salg.D}
  (b0LeB1: b0 ⊑ b1)
  (n: Ordinal)
:
  operatorC.stage salg dl b0 n ⊑ operatorC.stage salg dl b1 n
:=
  let stageN0 := operatorC.stage salg dl b0 n
  let stageN1 := operatorC.stage salg dl b1 n
  
  if h: n.IsActualLimit then
    let lim0 := limit salg dl b0 h
    let lim1 := limit salg dl b1 h
    
    fun x => {
      defLe :=
        fun d dIn0 =>
          let exVal0 :=
            Valuation.ord.standard.inSup.inSomeSet.defMem
              ⟨stageN0, lim0⟩ dIn0
          
          let val0 := exVal0.unwrap
          let valIndex := val0.val.property.unwrap
          let val1 := stage salg dl b1 valIndex
          let val0Eq: val0 = stage salg dl b0 valIndex :=
            valIndex.property.symm
          
          have: valIndex < n := valIndex.val.property
          let valLe: val0.val.val ⊑ val1 :=
            val0Eq ▸ approximation salg dl b0LeB1 valIndex
          
          let dIn1 := (valLe x).defLe val0.property
          
          let val1LeStage1 := lim1.isMember ⟨val1, ⟨valIndex.val, rfl⟩⟩
          
          (val1LeStage1 x).defLe dIn1,
      posLe :=
        fun d dIn1 =>
          let exVal1 :=
            Valuation.ord.standard.inSup.inSomeSet.posMem
              ⟨stageN1, lim1⟩ dIn1
          
          let val1 := exVal1.unwrap
          let valIndex := val1.val.property.unwrap
          let val0 := stage salg dl b0 valIndex
          let val1Eq: val1 = stage salg dl b1 valIndex :=
            valIndex.property.symm
          
          have: valIndex < n := valIndex.val.property
          let valLe: val0 ⊑ val1 :=
            val1Eq ▸ approximation salg dl b0LeB1 valIndex
          
          let dIn0 := (valLe x).posLe val1.property
          
          let val0LeStage0 := lim0.isMember ⟨val0, ⟨valIndex.val, rfl⟩⟩
          
          (val0LeStage0 x).posLe dIn0,
    }
  else
    let nPred := n.pred
    
    let opC0 := operatorC salg dl b0
    let opC1 := operatorC salg dl b1
    
    let s0Pred := operatorC.stage salg dl b0 nPred
    let s1Pred := operatorC.stage salg dl b1 nPred
    
    let s0Eq: operatorC.stage salg dl b0 n = opC0 s0Pred :=
      operatorC.stage.pred salg dl b0 h
    
    let s1Eq: operatorC.stage salg dl b1 n = opC1 s1Pred :=
      operatorC.stage.pred salg dl b1 h
    
    let s0PredLeS1Pred: s0Pred ⊑ s1Pred :=
      have: nPred < n := Ordinal.notLimitToPredLt h
      operatorC.stage.isMonotonic.approximation salg dl b0LeB1 nPred
    
    fun x =>
      let ILe := Expr.interpretation.isMonotonic.approximation
        salg (dl.getDef x) b0 b1 s0Pred s1Pred b0LeB1 s0PredLeS1Pred
  
      s0Eq ▸ s1Eq ▸ ILe
termination_by n


noncomputable def operatorB (salg: Salgebra sig) (dl: DefList sig):
  Valuation salg.D → Valuation salg.D
:=
  fun b => (operatorC.lfp salg dl b).val

def operatorB.eqLfpC
  (lfp:
    Lfp
      (Valuation.ord.standard salg.D)
      (operatorC salg dl b))
:
  lfp.val = operatorB salg dl b
:=
  congr rfl
    (Least.eq
      (Valuation.ord.standard salg.D)
      lfp
      (operatorC.lfp salg dl b))


noncomputable def operatorB.isMonotonic.commonFixedStage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b0 b1: Valuation salg.D)
:
  {
    n: Ordinal
  //
    operatorC.stage salg dl b0 n = operatorB salg dl b0 ∧
    operatorC.stage salg dl b1 n = operatorB salg dl b1
  }
:=
  let lfpI0 := operatorC.fixedStage salg dl b0
  let lfpI1 := operatorC.fixedStage salg dl b1
  
  if h: lfpI0.val ≤ lfpI1 then
    let isLfp:
      IsLfp
        (Valuation.ord.standard salg.D)
        (operatorC salg dl b0)
        (operatorC.stage salg dl b0 lfpI1)
    :=
      lfp.stage.gtLfpEqLfp
        (Valuation.ord.standard.isChainComplete salg.D)
        (operatorC salg dl b0)
        (operatorC.isMonotonic salg dl b0)
        h
        lfpI0.property
    ⟨
      lfpI1,
      And.intro
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b0 ↑lfpI1,
          isLfp,
        ⟩)
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b1 ↑lfpI1,
          lfpI1.property,
        ⟩)
    ⟩
  else
    let isLfp:
      IsLfp
        (Valuation.ord.standard salg.D)
        (operatorC salg dl b1)
        (operatorC.stage salg dl b1 lfpI0)
    :=
      lfp.stage.gtLfpEqLfp
        (Valuation.ord.standard.isChainComplete salg.D)
        (operatorC salg dl b1)
        (operatorC.isMonotonic salg dl b1)
        (le_of_not_le h)
        lfpI1.property
    ⟨
      lfpI0,
      And.intro
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b0 ↑lfpI0,
          lfpI0.property,
        ⟩)
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b1 ↑lfpI0,
          isLfp,
        ⟩)
    ⟩

def operatorB.isMonotonic (salg: Salgebra sig) (dl: DefList sig):
  IsMonotonic
    (Valuation.ord.approximation salg.D)
    (Valuation.ord.approximation salg.D)
    (operatorB salg dl)
:=
  fun {b0 b1} b0LeB1 =>
    fun x =>
      let lfpI := isMonotonic.commonFixedStage salg dl b0 b1
      
      let le := operatorC.stage.isMonotonic.approximation
        salg dl b0LeB1 lfpI
      
      (lfpI.property.left ▸ lfpI.property.right ▸ le) x

noncomputable def operatorB.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Lfp (Valuation.ord.approximation salg.D) (operatorB salg dl)
:=
  _root_.lfp
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)


noncomputable def operatorB.stage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  Valuation salg.D
:=
  lfp.stage
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

noncomputable def operatorB.fixedIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  { n: Ordinal // operatorB.stage salg dl n = (operatorB.lfp salg dl).val }
:= ⟨
  lfp.fixedStage
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl),
  rfl
⟩

structure operatorB.FixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (n: Ordinal): Prop
where
  eqLfpA: operatorB.stage salg dlA n = (operatorB.lfp salg dlA).val
  eqLfpB: operatorB.stage salg dlB n = (operatorB.lfp salg dlB).val

noncomputable def operatorB.fixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
:
  { n // operatorB.FixedIndex2 salg dlA dlB n }
:=
  let fixedA := operatorB.fixedIndex salg dlA
  let fixedB := operatorB.fixedIndex salg dlB
  
  if h: fixedA.val ≤ fixedB.val then
    ⟨
      fixedB.val,
      ⟨
        let isLfpAtB := lfp.stage.gtLfpEqLfp
          (Valuation.ord.approximation.isChainComplete salg.D)
          (operatorB salg dlA)
          (operatorB.isMonotonic salg dlA)
          h
          ((operatorB.lfp salg dlA).property)
        
        iIsLeast.isUnique
          (Valuation.ord.approximation salg.D)
          isLfpAtB
          (lfp salg dlA).property,
        fixedB.property,
      ⟩
    ⟩
  else
    ⟨
      fixedA.val,
      ⟨
        fixedA.property,
        let isLfpAtA := lfp.stage.gtLfpEqLfp
          (Valuation.ord.approximation.isChainComplete salg.D)
          (operatorB salg dlB)
          (operatorB.isMonotonic salg dlB)
          (le_of_not_le h)
          ((operatorB.lfp salg dlB).property)
        
        iIsLeast.isUnique
          (Valuation.ord.approximation salg.D)
          isLfpAtA
          (lfp salg dlB).property,
      ⟩
    ⟩

noncomputable def operatorB.stage.previous
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  Tuple (Valuation salg.D)
:=
  lfp.stage.previous
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

def operatorB.stage.limit
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
:
  IsSupremum
    (Valuation.ord.approximation salg.D)
    (operatorB.stage.previous salg dl n)
    (operatorB.stage salg dl n)
:=
  lfp.stage.limit
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    nIsLimit

def operatorB.stage.limitAt
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
  (x: Nat)
:
  IsSupremum
    (Set3.ord.approximation salg.D)
    (Set.pointwiseAt (fun d => d ∈ previous salg dl n) x)
    (operatorB.stage salg dl n x)
:=
  let isSup := operatorB.stage.limit salg dl nIsLimit
  let supAt := Set.pointwiseSup.supAt ⟨_, isSup⟩ x
  
  supAt.property

def operatorB.stage.succEq
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  operatorB.stage salg dl n.succ =
    (operatorB salg dl) (operatorB.stage salg dl n)
:=
  lfp.stage.succEq
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

noncomputable def operatorB.stage.eqPrevN
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorC.stage salg dl b nn =
    (operatorC.stage.previous salg dl b n).elements nn
:=
  rfl

def operatorB.stage.isMonotonic
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n nn: Ordinal}
  (nnLt: nn ≤ n)
:
  stage salg dl nn ⊑ stage salg dl n
:=
  lfp.stage.isMono
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    (nnLt)


def Valuation.IsModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Set (Valuation salg.D)
:=
  fun v => v = dl.interpretation salg v v

noncomputable def DefList.wellFoundedModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  (operatorB.lfp salg dl).val

def DefList.wellFoundedModel.isModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  (dl.wellFoundedModel salg).IsModel salg dl
:=
  let wfm := dl.wellFoundedModel salg
  let clfp := (operatorC.lfp salg dl wfm).val
  
  let wfmEq: wfm = clfp :=
    (operatorB.lfp salg dl).property.isMember
  
  let clfpEq: clfp = dl.interpretation salg wfm wfm :=
    let eq: clfp = dl.interpretation salg wfm clfp :=
      (operatorC.lfp salg dl wfm).property.isMember
    wfmEq ▸ eq
  
  wfmEq.trans clfpEq

def DefList.wellFoundedModel.isLfp
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  IsLfp
    (Valuation.ord.approximation salg.D)
    (operatorB salg dl)
    (dl.wellFoundedModel salg)
:=
  (operatorB.lfp salg dl).property


def Salgebra.IsDefinable
  (salg: Salgebra sig)
  (set: Set3 salg.D)
:
  Prop
:=
  ∃
    (dl: FinBoundedDL sig)
    (x: Nat)
  ,
    set = dl.wellFoundedModel salg x

def Salgebra.Definable
  (salg: Salgebra sig)
:
  Type
:=
  { set: Set3 salg.D // salg.IsDefinable set }
