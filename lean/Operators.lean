import Arities
import Interpretation

open Classical


def operatorC (alg: Algebra s) (dl: DefList s Var) (b: Valuation Var alg.D):
  Valuation Var alg.D → Valuation Var alg.D
:=
  fun c => DefList.I alg b c dl

def operatorC.isMonotonic
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
:
  isMonotonic (Valuation.ord.standard Var alg.D) (operatorC alg dl b)
:=
  fun c0 c1 cLe =>
    fun x =>
      match x with
      | Sum.inl x => I.isMonotonic.standard alg (dl.getDef x) b c0 c1 cLe
      | Sum.inr _ => (Set3.ord.standard alg.D).refl _

noncomputable def operatorC.lfp
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
:
  Lfp (Valuation.ord.standard Var alg.D) (operatorC alg dl b)
:=
  @_root_.lfp
    (Valuation Var alg.D)
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)


noncomputable def operatorC.stage
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
:
  Valuation Var alg.D
:=
  lfp.stage
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)
    n

noncomputable def operatorC.lfp.index
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
:
  { n: Ordinal // operatorC.stage alg dl b n = (operatorC.lfp alg dl b).val }
:= ⟨
  @_root_.lfp.stage.fixed.index
    (Valuation Var alg.D)
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b),
  rfl
⟩

noncomputable def operatorC.stage.prevTuple
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
:
  Tuple (Valuation Var alg.D)
:=
  lfp.stage.prevTuple
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)
    n

def operatorC.stage.prevChain
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
:
  Chain (Valuation.ord.standard Var alg.D)
:=
  lfp.stage.prevChain
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)
    n

noncomputable def operatorC.stage.prevChain.stage.in
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorC.stage alg dl b nn ∈ (operatorC.stage.prevChain alg dl b n).val
:=
  ⟨nn, rfl⟩

noncomputable def operatorC.stage.prevChain.in.index
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
  (val: Valuation Var alg.D)
  (valInPrevChain: val ∈ (operatorC.stage.prevChain alg dl b n).val)
:
  { i: ↑n // operatorC.stage alg dl b i = val }
:=
  let pT := operatorC.stage.prevTuple alg dl b n
  
  let i: { i: ↑n // Tuple.elements pT i = val } := choiceEx valInPrevChain
  
  ⟨i.val, i.property⟩

def operatorC.stage.limit
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  {n: Ordinal}
  (nIsLimit: n.isLimit)
:
  operatorC.stage alg dl b n =
    ((prevChain alg dl b n).sup
      (Valuation.ord.standard Var alg.D)
      (Valuation.ord.standard.isChainComplete Var alg.D)).val
:=
  lfp.stage.limit
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)
    nIsLimit

def operatorC.stage.succ
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n nPred: Ordinal)
  (nPredEq: n.pred = nPred)
:
  operatorC.stage alg dl b n =
    (operatorC alg dl b) (operatorC.stage alg dl b nPred)
:=
  lfp.stage.succ
    (Valuation.ord.standard Var alg.D)
    (Valuation.ord.standard.isChainComplete Var alg.D)
    (operatorC alg dl b)
    (operatorC.isMonotonic alg dl b)
    n nPred
    nPredEq

noncomputable def operatorC.stage.eqPrevN
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorC.stage alg dl b nn =
    (operatorC.stage.prevTuple alg dl b n).elements nn
:=
  rfl

def operatorC.boundEmpty
  (alg: Algebra s)
  (dl: DefList s Var)
  (b val: Valuation Var alg.D)
  (x: Nat)
:
  (operatorC alg dl b) val (Sum.inr x) = Set3.empty
:=
  rfl

def operatorC.stage.boundEmpty
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
  (x: Nat)
:
  (operatorC.stage alg dl b n) (Sum.inr x) = Set3.empty
:=
  if h: n.isLimit then
    let prevStages := stage.prevChain alg dl b n
    
    let prevEmpty (nn: ↑n) :=
      have: nn < n := nn.property
      operatorC.stage.boundEmpty alg dl b nn x
    
    let prevStages.sup := prevStages.sup
      (Valuation.ord.standard Var alg.D)
      (Valuation.ord.standard.isChainComplete Var alg.D)
    
    let prevStages.supEq: operatorC.stage alg dl b n = prevStages.sup.val :=
      stage.limit alg dl b h
    
    let ninSupPos d:
      ¬d ∈ (operatorC.stage alg dl b n (Sum.inr x)).posMem
    :=
      prevStages.supEq ▸ Valuation.ord.standard.ninChain.ninSup.posMem
        prevStages
        (Sum.inr x)
        d
        (fun prev =>
          let prevIndex := operatorC.stage.prevChain.in.index
            alg dl b n prev prev.property
          let stagePrevIndex.isEmpty:
            stage alg dl b prevIndex.val.val (Sum.inr x) = Set3.empty
          :=
            prevEmpty ⟨prevIndex.val, prevIndex.val.property⟩
          
          prevIndex.property ▸ stagePrevIndex.isEmpty ▸
            (Set3.empty.nin.pos d))
    
    Set3.empty.fromNoPos ninSupPos
  else
    let nPred := Ordinal.nLimit.pred n h
    
    let stepEq := stage.succ alg dl b n nPred
      (Ordinal.succ.pred.eq nPred.property)
    
    stepEq ▸ rfl
  termination_by operatorC.stage.boundEmpty alg dl b n x => n

-- Readability? Never heard of it.
def operatorC.stage.isMonotonic.approximation
  (alg: Algebra s)
  (dl: DefList s Var)
  (b0 b1: Valuation Var alg.D)
  (b0LeB1: b0 ⊑ b1)
  (n: Ordinal)
:
  operatorC.stage alg dl b0 n ⊑ operatorC.stage alg dl b1 n
:=
  let D.so := Set3.ord.standard alg.D
  let D.cc := Set3.ord.standard.isChainComplete alg.D
  
  let Val.so := (Valuation.ord.standard Var alg.D)
  let cc := (Valuation.ord.standard.isChainComplete Var alg.D)
  
  let pt0 := operatorC.stage.prevTuple alg dl b0 n
  let pt1 := operatorC.stage.prevTuple alg dl b1 n
  
  if h: n.isLimit then
    let prevChain0 := operatorC.stage.prevChain alg dl b0 n
    let prevChain1 := operatorC.stage.prevChain alg dl b1 n
    
    let sup0 := prevChain0.sup Val.so cc
    let sup1 := prevChain1.sup Val.so cc
    
    let sup0EqStage: operatorC.stage alg dl b0 n = sup0.val :=
      operatorC.stage.limit alg dl b0 h
    
    let sup1EqStage: operatorC.stage alg dl b1 n = sup1.val :=
      operatorC.stage.limit alg dl b1 h
    
    let sup0Pointwise := pointwiseSup D.so D.cc prevChain0
    let sup1Pointwise := pointwiseSup D.so D.cc prevChain1
    
    let sup0Pointwise.typed := pointwiseSup.typed D.so D.cc prevChain0
    let sup1Pointwise.typed := pointwiseSup.typed D.so D.cc prevChain1
    
    let sup0EqPointwiseSup: sup0 = sup0Pointwise := sup.eq _ _ _
    let sup0EqPointwiseSup.var (var: (Sum Var Nat)):
      sup0.val var = sup0Pointwise.val var
    :=
      congr (congr rfl sup0EqPointwiseSup) rfl
    
    let sup0EqPointwiseSup.typed (var: (Sum Var Nat)):
      sup0.val var = (sup0Pointwise.typed var).val
    :=
      sup0EqPointwiseSup.var var
    
    let sup1EqPointwiseSup: sup1 = sup1Pointwise := sup.eq _ _ _
    let sup1EqPointwiseSup.var (var: (Sum Var Nat)):
      sup1.val var = sup1Pointwise.val var
    :=
      congr (congr rfl sup1EqPointwiseSup) rfl
    
    let sup1EqPointwiseSup.typed (var: (Sum Var Nat)):
      sup1.val var = (sup1Pointwise.typed var).val
    :=
      sup1EqPointwiseSup.var var
    
    let prevChainLeNn: sup0.val ⊑ sup1.val :=
      fun x =>
        let ch0At := pointwiseSup.atChain D.so prevChain0 x
        let ch1At := pointwiseSup.atChain D.so prevChain1 x
        
        let sup0At := sup0Pointwise.typed x
        let sup1At := sup1Pointwise.typed x
        
        And.intro
          (fun d dIn =>
            let dIn.typed: d ∈ sup0At.val.defMem :=
              sup0EqPointwiseSup.typed x ▸ dIn
            
            let exSCh0At: ∃ sCh0At: ↑ch0At.val, d ∈ sCh0At.val.defMem :=
              Set3.ord.standard.inSup.inChain.defMem.ex ch0At d dIn.typed
            let sCh0At := choiceEx exSCh0At
            
            let prevStage0:
              {
                prevStage:
                  {
                    prevStage: Valuation Var alg.D
                  //
                    prevStage ∈ prevChain0.val
                  }
              //
                sCh0At.val.val = prevStage.val x
              }
            :=
              choiceEx sCh0At.val.property
            
            let prevStage0.index.tmp:
              { nn: ↑n // pt0.elements nn
                = prevStage0.val.val }
            :=
              (choiceEx prevStage0.val.property)
            
            let prevStage.i:
              { nn: ↑n // operatorC.stage alg dl b0 nn = prevStage0.val.val }
            :=
              ⟨prevStage0.index.tmp, prevStage0.index.tmp.property⟩
            
            let prevStage1 := operatorC.stage alg dl b1 prevStage.i.val
            
            let prevStage1.ge: prevStage0.val.val ⊑ prevStage1 :=
              (prevStage.i.property) ▸
              have: prevStage.i.val < n := prevStage.i.val.property
              (operatorC.stage.isMonotonic.approximation alg dl b0 b1 b0LeB1
                prevStage.i.val)
            
            let prevStage1.inChain: prevStage1 ∈ prevChain1.val :=
              operatorC.stage.prevChain.stage.in alg dl b1 n prevStage.i
            
            let prevStage1.typed:
              { t: Valuation Var alg.D // t ∈ prevChain1.val }
            :=
              ⟨prevStage1, prevStage1.inChain⟩
            
            let prevStage1.leSup1: prevStage1 ≤ sup1.val :=
              sup1.property.left prevStage1.typed
            
            let dInPrevStage0: d ∈ (prevStage0.val.val x).defMem :=
              prevStage0.property ▸ sCh0At.property
            
            let dInPrevStage1: d ∈ (prevStage1 x).defMem :=
              (prevStage1.ge x).left d dInPrevStage0
            
            (prevStage1.leSup1 x).left d dInPrevStage1)
          (fun d dIn =>
            let dIn.typed: d ∈ sup1At.val.posMem :=
              sup1EqPointwiseSup.typed x ▸ dIn
            
            let exSCh1At: ∃ sCh1At: ↑ch1At.val, d ∈ sCh1At.val.posMem :=
              Set3.ord.standard.inSup.inChain.posMem.ex ch1At d dIn.typed
            let sCh1At := choiceEx exSCh1At
            
            let prevStage1 := choiceEx sCh1At.val.property
            
            let prevStage1.index.tmp:
              { nn: ↑n // pt1.elements nn
                = prevStage1.val.val }
            :=
              (choiceEx prevStage1.val.property)
            
            let prevStage.i:
              { nn: ↑n // operatorC.stage alg dl b1 nn = prevStage1.val.val }
            :=
              ⟨prevStage1.index.tmp, prevStage1.index.tmp.property⟩
            
            let prevStage0 := operatorC.stage alg dl b0 prevStage.i.val
            
            let prevStage0.le: prevStage0 ⊑ prevStage1.val.val :=
              (prevStage.i.property) ▸
              have: prevStage.i.val < n := prevStage.i.val.property
              (operatorC.stage.isMonotonic.approximation alg dl b0 b1 b0LeB1
                prevStage.i.val)
            
            let prevStage0.inChain: prevStage0 ∈ prevChain0.val :=
              operatorC.stage.prevChain.stage.in alg dl b0 n prevStage.i
            
            let prevStage0.typed:
              { t: Valuation Var alg.D // t ∈ prevChain0.val }
            :=
              ⟨prevStage0, prevStage0.inChain⟩
            
            let prevStage0.leSup0: prevStage0 ≤ sup0.val :=
              sup0.property.left prevStage0.typed
            
            let dInPrevStage1: d ∈ (prevStage1.val.val x).posMem :=
              prevStage1.property ▸ sCh1At.property
            
            let dInPrevStage0: d ∈ (prevStage0 x).posMem :=
              (prevStage0.le x).right d dInPrevStage1
            
            (prevStage0.leSup0 x).right d dInPrevStage0)
    
    sup0EqStage ▸ sup1EqStage ▸ prevChainLeNn
  else
    let nPred := Ordinal.nLimit.pred n h
    
    let opC0 := operatorC alg dl b0
    let opC1 := operatorC alg dl b1
    
    let s0Pred := operatorC.stage alg dl b0 nPred
    let s1Pred := operatorC.stage alg dl b1 nPred
    
    let s0Eq: operatorC.stage alg dl b0 n = opC0 s0Pred :=
      operatorC.stage.succ alg dl b0 n nPred (Ordinal.succ.pred.eq nPred.property)
    
    let s1Eq: operatorC.stage alg dl b1 n = opC1 s1Pred :=
      operatorC.stage.succ alg dl b1 n nPred (Ordinal.succ.pred.eq nPred.property)
    
    let s0PredLeS1Pred: s0Pred ⊑ s1Pred :=
      have: nPred < n := Ordinal.nLimit.pred.lt n h
      operatorC.stage.isMonotonic.approximation alg dl b0 b1 b0LeB1 nPred
    
    fun x =>
      match x with
      | Sum.inl x =>
          let ILe := I.isMonotonic.approximation
            alg (dl.getDef x) b0 b1 s0Pred s1Pred b0LeB1 s0PredLeS1Pred
      
          s0Eq ▸ s1Eq ▸ ILe
      | Sum.inr x =>
          let b0Empty := operatorC.stage.boundEmpty alg dl b0 n x
          let b1Empty := operatorC.stage.boundEmpty alg dl b1 n x
          
          b0Empty ▸ b1Empty ▸ (Set3.ord.approximation alg.D).refl _
termination_by operatorC.stage.isMonotonic.approximation alg dl b0 b1 b0LeB1 n
  => n


noncomputable def operatorB (alg: Algebra s) (dl: DefList s Var):
  Valuation Var alg.D → Valuation Var alg.D
:=
  fun b => (operatorC.lfp alg dl b).val

def operatorB.isMonotonic (alg: Algebra s) (dl: DefList s Var):
  isMonotonic (Valuation.ord.approximation Var alg.D) (operatorB alg dl)
:=
  fun b0 b1 b0LeB1 =>
    fun x =>
      let lfpI0 := operatorC.lfp.index alg dl b0
      let lfpI1 := operatorC.lfp.index alg dl b1
      
      let lfpI:
        {
          n: Ordinal
        //
          operatorC.stage alg dl b0 n = operatorB alg dl b0 ∧
          operatorC.stage alg dl b1 n = operatorB alg dl b1
        }
      :=
        if h: lfpI0.val ≤ lfpI1 then
          let higher :=
            lfp.stage.fixed.index.higher
              (Valuation.ord.standard Var alg.D)
              (Valuation.ord.standard.isChainComplete Var alg.D)
              (operatorC alg dl b0)
              (operatorC.isMonotonic alg dl b0)
              (operatorC.lfp alg dl b0)
              lfpI1
              h
          ⟨lfpI1, And.intro higher lfpI1.property⟩
        else
          let lt: lfpI1.val ≤ lfpI0 := (lfpI0.val.total lfpI1).elim
            (fun nope => False.elim (h (Or.inl nope)))
            (fun le =>
              le.elim
                (fun lt => (Or.inl lt))
                (fun eq => (Or.inr eq.symm)))
          
          let higher :=
            lfp.stage.fixed.index.higher
              (Valuation.ord.standard Var alg.D)
              (Valuation.ord.standard.isChainComplete Var alg.D)
              (operatorC alg dl b1)
              (operatorC.isMonotonic alg dl b1)
              (operatorC.lfp alg dl b1)
              lfpI0
              lt
          ⟨lfpI0, And.intro lfpI0.property higher⟩
      
      let le := operatorC.stage.isMonotonic.approximation
        alg dl b0 b1 b0LeB1 lfpI
      
      (lfpI.property.left ▸ lfpI.property.right ▸ le) x

noncomputable def operatorB.lfp
  (alg: Algebra s)
  (dl: DefList s Var)
:
  Lfp (Valuation.ord.approximation Var alg.D) (operatorB alg dl)
:=
  @_root_.lfp
    (Valuation Var alg.D)
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)


noncomputable def operatorB.stage
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
:
  Valuation Var alg.D
:=
  lfp.stage
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    n

noncomputable def operatorB.lfp.index
  (alg: Algebra s)
  (dl: DefList s Var)
:
  { n: Ordinal // operatorB.stage alg dl n = (operatorB.lfp alg dl).val }
:= ⟨
  @_root_.lfp.stage.fixed.index
    (Valuation Var alg.D)
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl),
  rfl
⟩

noncomputable def operatorB.stage.prevTuple
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
:
  Tuple (Valuation Var alg.D)
:=
  lfp.stage.prevTuple
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    n

def operatorB.stage.prevChain
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
:
  Chain (Valuation.ord.approximation Var alg.D)
:=
  lfp.stage.prevChain
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    n

noncomputable def operatorB.stage.prevChain.stage.in
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorB.stage alg dl nn ∈ (operatorB.stage.prevChain alg dl n).val
:=
  ⟨nn, rfl⟩

noncomputable def operatorB.stage.prevChain.in.index
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
  (val: Valuation Var alg.D)
  (valInPrevChain: val ∈ (operatorB.stage.prevChain alg dl n).val)
:
  { i: ↑n // operatorB.stage alg dl i = val }
:=
  let pT := operatorB.stage.prevTuple alg dl n
  
  let i: { i: ↑n // Tuple.elements pT i = val } := choiceEx valInPrevChain
  
  ⟨i.val, i.property⟩

def operatorB.stage.limit
  (alg: Algebra s)
  (dl: DefList s Var)
  {n: Ordinal}
  (nIsLimit: n.isLimit)
:
  operatorB.stage alg dl n =
    ((prevChain alg dl n).sup
      (Valuation.ord.approximation Var alg.D)
      (Valuation.ord.approximation.isChainComplete Var alg.D)).val
:=
  lfp.stage.limit
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    nIsLimit

def operatorB.stage.succ
  (alg: Algebra s)
  (dl: DefList s Var)
  (n nPred: Ordinal)
  (nPredEq: n.pred = nPred)
:
  operatorB.stage alg dl n =
    (operatorB alg dl) (operatorB.stage alg dl nPred)
:=
  lfp.stage.succ
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    n nPred
    nPredEq

noncomputable def operatorB.stage.eqPrevN
  (alg: Algebra s)
  (dl: DefList s Var)
  (b: Valuation Var alg.D)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorC.stage alg dl b nn =
    (operatorC.stage.prevTuple alg dl b n).elements nn
:=
  rfl

def operatorB.boundEmpty.stage1
  (alg: Algebra s)
  (dl: DefList s Var)
  (x: Nat)
:
  (operatorB.stage alg dl Ordinal.zero.succ) (Sum.inr x) = Set3.empty
:=
  let stage0 := operatorB.stage alg dl Ordinal.zero
  let opCLfp := operatorC.lfp alg dl stage0
  
  let opBZero.eq:
    operatorB alg dl stage0 = (operatorC.lfp alg dl stage0).val
  :=
    rfl
  
  let lfpEqStep: opCLfp.val = operatorC alg dl stage0 opCLfp.val :=
    opCLfp.property.left
  
  let opCBoundEmpty: opCLfp.val (Sum.inr x) = Set3.empty :=
    lfpEqStep ▸ operatorC.boundEmpty alg dl stage0 _ x
  
  let stepEq := stage.succ alg dl Ordinal.zero.succ Ordinal.zero
    (Ordinal.succ.pred.eq rfl)
  
  stepEq ▸ opBZero.eq ▸ opCBoundEmpty

def operatorB.stage.isMonotonic.approximation
  (alg: Algebra s)
  (dl: DefList s Var)
  (n nn: Ordinal)
  (nnLt: nn ≤ n)
:
  stage alg dl nn .≤ stage alg dl n
:=
  lfp.stage.isMono
    (Valuation.ord.approximation Var alg.D)
    (Valuation.ord.approximation.isChainComplete Var alg.D)
    (operatorB alg dl)
    (operatorB.isMonotonic alg dl)
    (nnLt)

def operatorB.boundEmpty
  (alg: Algebra s)
  (dl: DefList s Var)
  (n: Ordinal)
  (nNeqZero: n ≠ 0)
  (x: Nat)
:
  (operatorB.stage alg dl n) (Sum.inr x) = Set3.empty
:=
  let stage1Eq := boundEmpty.stage1 alg dl x
  
  let nLtZero := Ordinal.zero.lt n nNeqZero
  let nLeOne := Ordinal.lt.leSucc nLtZero
  
  let emptyLe := stage1Eq ▸ operatorB.stage.isMonotonic.approximation
    alg dl n Ordinal.zero.succ nLeOne (Sum.inr x)
  
  let noDPos d: d ∉ (stage alg dl n (Sum.inr x)).posMem :=
    fun dIn => emptyLe.right d dIn
  
  Set3.eq
    (Set.eq fun d => Iff.intro
      (fun dIn => noDPos d ((stage alg dl n (Sum.inr x)).defLePos d dIn))
      False.elim)
    (Set.eq fun d => Iff.intro (noDPos d) False.elim)
