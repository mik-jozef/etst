import Utils.Lfp
import Set3

open Classical


inductive Two
  | zero
  | one

instance: Coe Two Nat where
  coe :=
    fun two =>
      match two with
        | Two.zero => 0
        | Two.one => 1

def Nat2 := Nat → Two
def Nat2.zeros: Nat2 := fun _ => Two.zero

-- Converts a number to little endian.
def Nat2.fromNat (n: Nat): Nat2 :=
  fun i =>
    let d := Nat.pow 2 i
    
    if n % (d * 2) >= d then Two.one else Two.zero


def Tuple.Nat2.IsEventuallyZeroAtIndex
  (tuple: Tuple Nat2)
  (index: Nat)
:
  Prop
:=
  ∃ lowerBound: ↑tuple.length,
    ∀ i: ↑tuple.length,
      lowerBound.val ≤ i.val → tuple.elements i index = Two.zero

noncomputable def Tuple.Nat2.limSup
  (tuple: Tuple Nat2)
  (ifUndefined: Nat2)
:
  Nat2
:=
  if tuple.length = 0 then
    ifUndefined
  else
    fun n: Nat =>
      if IsEventuallyZeroAtIndex tuple n then
        Two.zero
      else
        Two.one

def Tuple.Nat2.limSup.zero
  (tuple: Tuple Nat2)
  (ifUndefined: Nat2)
  (tEmpty: tuple.length = 0)
:
  limSup tuple ifUndefined = ifUndefined
:=
  if_pos tEmpty

def Tuple.Nat2.limSup.eq
  (tuple: Tuple Nat2)
  (ifUndefined: Nat2)
  (isDefined: tuple.length ≠ 0)
  (result: Nat2)
  (isResSound:
    ∀ n: Nat,
    IsEventuallyZeroAtIndex tuple n ↔ result n = Two.zero)
:
  limSup tuple ifUndefined = result
:=
  by unfold limSup; rw [if_neg isDefined]; exact funext fun n =>
    if h: IsEventuallyZeroAtIndex tuple n then
      (if_pos h).trans ((isResSound n).mp h).symm
    else
      match hh: result n with
      | Two.zero => False.elim (((Iff.not (isResSound n)).mp h) hh)
      | Two.one => (if_neg h).trans rfl


def Tuple.Nat2.limSup.isEventuallyConstant
  (t: Tuple Nat2)
  (ifU: Nat2)
  (lowerBound: ↑t.length)
  (res: Nat2)
  (constantAbove: ∀ i: ↑t.length, lowerBound.val ≤ i → t.elements i = res)
:
  limSup t ifU = res
:=
  let isDefined: t.length ≠ 0 :=
    fun eq =>
      let ltZero: lowerBound.val < 0 := eq ▸ lowerBound.property
      Ordinal.not_lt_zero _ ltZero
  
  limSup.eq t ifU isDefined res fun _n =>
    Iff.intro
      (fun evntZero =>
        let lbN := evntZero.unwrap
        
        let lbMax: ↑t.length := max lowerBound lbN.val
        let geLowerBound: lowerBound ≤ lbMax := Ordinal.le_max_left _ _
        let geLbN: lbN.val ≤ lbMax := Ordinal.le_max_rite _ _
        
        let cAboveMax := constantAbove lbMax geLowerBound
        let eqZero := lbN.property lbMax geLbN
        
        (congr cAboveMax.symm rfl).trans eqZero)
      (fun eqZero =>
        ⟨
          lowerBound,
          fun i geLb => (congr (constantAbove i geLb) rfl).trans eqZero
        ⟩)


inductive Dir
  | left
  | right
  | none

def Dir.shift (dir: Dir) (n: Nat): Option Nat :=
  match dir, n with
    | Dir.left, 0 => Option.none
    | Dir.left, x+1 => x
    | Dir.right, x => some (x + 1)
    | Dir.none, x => x

structure HamkinsMachine.Move (State: Type) where
  state: State
  symbol: Two
  dir: Dir

def HamkinsMachine.Move.eq {State: Type}:
  {m0 m1: HamkinsMachine.Move State} →
  m0.state = m1.state →
  m0.symbol = m1.symbol →
  m0.dir = m1.dir →
  m0 = m1
  
  | ⟨_,_,_⟩, ⟨_,_,_⟩, rfl, rfl, rfl => rfl

@[reducible] def HamkinsMachine.GetMove (State: Type) :=
  State → Two → HamkinsMachine.Move State

/-
  Infinite time Turing machine is too long. I hereby name you Hamkins
  machine.
  
  Note: Unlike the original definition [0], here we only have one tape for
  simplicity. In "Infinite time Turing machines with only one tape" [1],
  the authors claim one-tape machines are [TL;DR: bad]. Well, it is their
  definitions that are bad. A proper reaction to a move-left instruction
  while head at zero is for the machine to crash and burn. Nevertheless,
  thank you JDH for this awesome concept!
  
  0. https://arxiv.org/abs/math/9808093
  1. https://arxiv.org/abs/math/9907044
-/
structure HamkinsMachine where
  State: Type
  
  isFinite: Type.IsFinite State
  
  initialState: State
  haltState: State
  limitState: State
  
  getMove: HamkinsMachine.GetMove State
  
  haltHalts (two: Two): getMove haltState two = {
    state := haltState
    symbol := two
    dir := Dir.none
  }


namespace HamkinsMachine
  structure Configuration (hm: HamkinsMachine) where
    state: hm.State
    tape: Nat2
    head: Nat
  
  def Configuration.eq: {a b: Configuration hm} →
    (eqs: a.state = b.state) →
    (eqt: a.tape = b.tape) →
    (eqh: a.head = b.head) →
    a = b
  
    | ⟨_,_,_⟩, ⟨_,_,_⟩, rfl, rfl, rfl => rfl
  
  def step
    (hm: HamkinsMachine)
    (config: Configuration hm)
  :
    Configuration hm
  :=
    let move := hm.getMove (config.state) (config.tape config.head)
    -- With this, the `step.eq.X` proofs do not work. How to fix?
    --let newHead := move.dir.shift config.head
    let newHead :=
      (hm.getMove (config.state) (config.tape config.head)).dir.shift config.head
    
    match newHead with
      | none => config
      | some nh =>
          {
            state := move.state
            tape := fun n => if n = config.head then move.symbol else config.tape n
            head := nh
          }
  
  def step.eq.none
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (moveV: Move hm.State)
    (moveEq: moveV = hm.getMove (config.state) (config.tape config.head))
    (newHeadEq: none = moveV.dir.shift config.head)
  :
    hm.step config = config
  :=
    by unfold step; rw [moveEq.symm]; rw [newHeadEq.symm]
  
  def step.eq.some
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (moveV: Move hm.State)
    (moveEq: moveV = hm.getMove (config.state) (config.tape config.head))
    (newHead: Nat)
    (newHeadEq: some newHead = moveV.dir.shift config.head)
  :
    hm.step config = {
      state := moveV.state
      tape := fun n => if n = config.head then moveV.symbol else config.tape n
      head := newHead
    }
  :=
    by unfold step; rw [moveEq.symm]; rw [newHeadEq.symm]
  
  def step.halt
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (isHalt: config.state = hm.haltState)
  :
    hm.step config = config
  :=
    let symbol := config.tape config.head
    
    let moveObj: HamkinsMachine.Move hm.State := {
      state := hm.haltState
      symbol := symbol
      dir := Dir.none
    }
    
    let stepObj: HamkinsMachine.Configuration hm := {
      state := moveObj.state
      tape := fun n =>
        if n = config.head
          then moveObj.symbol
          else config.tape n
      head := config.head
    }
    let stepObj.tapeEq:
      stepObj.tape = config.tape
    :=
      funext fun n =>
        if h: n = config.head then
          (if_pos h).trans (h ▸ rfl)
        else
          if_neg h
    
    let move.eq: hm.getMove hm.haltState symbol = moveObj :=
      hm.haltHalts symbol
    
    let stageNPred.eq:
      config = ⟨hm.haltState, config.tape, config.head⟩
    :=
      HamkinsMachine.Configuration.eq isHalt rfl rfl
    
    let stepEq: hm.step config = stepObj :=
      stageNPred.eq ▸ HamkinsMachine.step.eq.some
        hm
        ⟨hm.haltState, config.tape, config.head⟩
        moveObj
        move.eq.symm
        config.head
        (rfl)
    
    stepEq.trans
      (HamkinsMachine.Configuration.eq isHalt.symm stepObj.tapeEq rfl)
  
  noncomputable def stage (hm: HamkinsMachine) (input: Nat2) (n: Ordinal):
    Configuration hm
  :=
    if h: n.IsActualLimit then
      let prevStages: Tuple Nat2 := {
        length := n,
        elements :=
          fun nn =>
            have: nn < n := nn.property
            (stage hm input nn).tape
      }
      
      {
        state :=
          if ∃ nn: ↑n,
            have: nn < n := nn.property
            (hm.stage input nn).state = hm.haltState
          then
            hm.haltState
          else if n = 0 then
            hm.initialState
          else
            hm.limitState
        -- If the machine halted, limSup is safe.
        tape := Tuple.Nat2.limSup prevStages input
        head := 0
      }
    else
      have: n.pred < n := Ordinal.predLtOfNotLimit h
      hm.step (hm.stage input n.pred)
    termination_by stage hm n => n
  
  noncomputable def stage.prevStages
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    Tuple Nat2
  := {
    length := n,
    elements :=
      fun nn => (stage hm input nn).tape
  }
  
  def stage.eq.step
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
    (nl: ¬n.IsActualLimit)
  :
    hm.stage input n = hm.step (hm.stage input n.pred)
  :=
    by conv =>
      lhs
      unfold stage
      rw [dif_neg nl]
  
  @[reducible] def stage.haltsAt
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  : Prop :=
    (stage hm input n).state = hm.haltState
  
  structure stage.eq.Zero
    (hm: HamkinsMachine)
    (input: Nat2)
  where
    (tapeEq: (hm.stage input 0).tape = input)
    (stateEq: (hm.stage input 0).state = hm.initialState)
    (headEq: (hm.stage input 0).head = 0)
  
  def stage.eq.zero
    (hm: HamkinsMachine)
    (input: Nat2)
  :
    Zero hm input
  :=
    {
      tapeEq :=
        let prevStages := stage.prevStages hm input 0
        
        let eqLim:
          (hm.stage input 0).tape = Tuple.Nat2.limSup prevStages input
        := by
          unfold HamkinsMachine.stage
          exact dif_pos Ordinal.zero.isLimit ▸ rfl
        
        eqLim.trans (Tuple.Nat2.limSup.zero prevStages input rfl)
      stateEq :=
        let nex := all.notEx
          (fun _ => trivial)
          (fun (nLe0: { nn // nn < 0 }) _ =>
            False.elim (Ordinal.not_lt_zero nLe0.val nLe0.property))
        
        by
          unfold HamkinsMachine.stage
          exact dif_pos Ordinal.zero.isLimit ▸ if_neg nex ▸ if_pos rfl ▸ rfl
      headEq := 
        by
          unfold HamkinsMachine.stage;
          exact dif_pos Ordinal.zero.isLimit ▸ rfl
    }
  
  structure stage.eq.Limit
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  where
    (tapeEq:
      (hm.stage input n).tape =
        Tuple.Nat2.limSup (stage.prevStages hm input n) input)
    
    (stateHalt: (∃ nn: ↑n, stage.haltsAt hm input nn)
      → (hm.stage input n).state = hm.haltState)
    
    (stateLimit: n = 0 ∨
      (¬(∃ nn: ↑n, stage.haltsAt hm input nn)
        → (hm.stage input n).state = hm.limitState))
    
    (headEq: (hm.stage input n).head = 0)
  
  def stage.eq.infLimit
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
    (nl: n.IsActualLimit)
  :
    Limit hm input n
  :=
    {
      tapeEq :=
        by unfold HamkinsMachine.stage; exact dif_pos nl ▸ rfl
      stateHalt := fun ex =>
        by
          unfold HamkinsMachine.stage
          exact dif_pos nl ▸ if_pos ex ▸ rfl
      stateLimit :=
        if h: n = 0 then
          Or.inl h
        else
          Or.inr fun nex =>
          by
            unfold HamkinsMachine.stage
            exact dif_pos nl ▸ if_neg nex ▸ if_neg h ▸ rfl
      headEq :=
        by unfold HamkinsMachine.stage; exact dif_pos nl ▸ rfl
    }
  
  def stage.eq.step.succ
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    hm.stage input n.succ = hm.step (hm.stage input n)
  :=
    let nSuccPredEq: n.succ.pred = n := Ordinal.pred_succ n
    
    let eqSucc:
      hm.stage input n.succ = hm.step (hm.stage input n.succ.pred)
    :=
      stage.eq.step hm input n.succ (Ordinal.succ_not_limit n)
    
    let eq: hm.stage input n.succ.pred = hm.stage input n :=
      congr rfl nSuccPredEq
    
    eq ▸ eqSucc
  
  def stage.haltsAt.ge
    (hAt: stage.haltsAt hm input n)
    (ng: Ordinal)
    (ngGe: n ≤ ng)
  :
    stage.haltsAt hm input ng
  :=
    if hEq: n = ng then
      hEq ▸ hAt
    else
      let ngGt: n < ng := lt_of_le_of_ne ngGe hEq
      let ngNotZero: ¬ng.IsZero := Ordinal.lt.notZero ngGt
      
      if hLim: ng.IsActualLimit then
        let lim := stage.eq.infLimit hm input ng ⟨hLim, ngNotZero⟩
        lim.stateHalt ⟨⟨n, ngGt⟩, hAt⟩
      else
        let ngPred := Ordinal.nLimit.pred ng hLim
        have: ngPred < ng := Ordinal.nLimit.pred.lt ng hLim
        
        let ngGePred: n ≤ ngPred :=
          Ordinal.ltSucc.le (ngPred.property.symm ▸ ngGt)
        
        let haltsAtPred := stage.haltsAt.ge hAt ngPred ngGePred
        
        let stepConstant := step.halt hm (stage hm input ngPred) haltsAtPred
        
        let stageNgEqStep := stage.eq.step hm input ng hLim
        
        let stageEq := stepConstant.symm.trans stageNgEqStep.symm
        
        by unfold haltsAt exact stageEq ▸ haltsAtPred
  
  termination_by stage.haltsAt.ge hAt ng ngGe => ng
  
  def stage.haltsAt.gt
    (hAt: stage.haltsAt hm input n)
    {ng: Ordinal}
    (ngGt: n < ng)
  :
    stage.haltsAt hm input ng
  :=
    stage.haltsAt.ge hAt ng (Or.inl ngGt)
  
  def stage.haltsWith
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal)
  :
    Prop
  :=
    stage.haltsAt hm input n ∧ (stage hm input n).tape = output
  
  def stage.haltsConsistent.step
    (hw0: stage.haltsWith hm input output0 n)
    (hw1: stage.haltsWith hm input output1 n.succ)
  :
    output0 = output1
  :=
    let stage0 := hm.stage input n
    let stage1 := hm.stage input n.succ
    
    let stage0.stateEq: stage0.state = hm.haltState := hw0.left
    
    let stage.eqL: stage1 = hm.step stage0 := stage.eq.step.succ hm input n
    let stage.eqR: hm.step stage0 = stage0 := step.halt hm stage0 stage0.stateEq
    let stage.eq: hm.stage input n = hm.stage input n.succ :=
      (stage.eqL.trans stage.eqR).symm
    
    hw0.right.symm.trans (stage.eq ▸ hw1.right)
  
  def stage.haltsConsistent.le
    {n0 n1: Ordinal}
    (hw0: stage.haltsWith hm input output0 n0)
    (hw1: stage.haltsWith hm input output1 n1)
    (nLe: n0 ≤ n1)
  :
    output0 = output1
  :=
    if hEq: n0 = n1 then
      hw0.right.symm.trans (hEq ▸ hw1.right)
    else
      let n1.lt: n0 < n1 := nLe.toLt hEq
      let n1.notZero: ¬n1.isZero := Ordinal.lt.notZero n1.lt
      
      if h: n1.isLimit then
        let prev := prevStages hm input n1
        
        let lim := stage.eq.infLimit hm input n1 ⟨h, n1.notZero⟩
        let limTape := lim.tapeEq
        
        let limEq0 := limSup.eventuallyConstant prev input ⟨n0, n1.lt⟩ output0
          fun nn1 n0LB =>
            have: nn1 < n1 := nn1.property
            
            let outputMid := (hm.stage input nn1).tape
            let hwMid: stage.haltsWith hm input outputMid nn1 :=
              And.intro (stage.haltsAt.ge hw0.left nn1 n0LB) rfl
            
            (stage.haltsConsistent.le hw0 hwMid n0LB).symm
        
        limEq0.symm.trans (limTape.symm.trans hw1.right)
      else
        let n1Pred := Ordinal.nLimit.pred n1 h
        have: n1Pred < n1 := Ordinal.nLimit.pred.lt n1 h
        
        let nLePred: n0 ≤ n1Pred :=
          Ordinal.ltSucc.le (n1Pred.property.symm ▸ n1.lt)
        
        let tapeAtPred := (hm.stage input n1Pred).tape
        let hwPred: stage.haltsWith hm input tapeAtPred n1Pred :=
          And.intro (stage.haltsAt.ge hw0.left n1Pred nLePred) rfl
        
        nLePred.elim
          (fun nLtPred =>
            let eqR := stage.haltsConsistent.le hw0 hwPred (Or.inl nLtPred)
            eqR.trans (stage.haltsConsistent.step
              hwPred (n1Pred.property.symm ▸ hw1)))
          (fun nEqPred =>
            stage.haltsConsistent.step
              (nEqPred ▸ hw0) (n1Pred.property.symm ▸ hw1))
  termination_by stage.haltsConsistent.le n0 n1 hw0 hw1 nLt => n1

  def stage.haltsConsistent
    {n0 n1: Ordinal}
    (hw0: stage.haltsWith hm input output0 n0)
    (hw1: stage.haltsWith hm input output1 n1)
  :
    output0 = output1
  :=
    -- Without loss of generality, let's assume n0 is lesser.
    -- Could this be made simpler in a theorem prover?
    (n0.total n1).elim
      (fun lt => stage.haltsConsistent.le hw0 hw1 (Or.inl lt))
      (fun gtOrEq => gtOrEq.elim
        (fun gt => (stage.haltsConsistent.le hw1 hw0 (Or.inl gt)).symm)
        (fun eq => hw0.right.symm.trans (eq ▸ hw1.right)))
  
  def computes (hm: HamkinsMachine) (input output: Nat2): Prop :=
    ∃ n: Ordinal,
      stage.haltsWith hm input output n
  
  noncomputable def fn (hm: HamkinsMachine) (input: Nat2): Option Nat2 :=
    if h: ∃ output: Nat2, hm.computes input output then
      some (choiceEx h)
    else
      none
  
  def haltsConsistent
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal)
    (hw: stage.haltsWith hm input output n)
  :
    fn hm input = output
  :=
    let computes: hm.computes input output := ⟨n, hw⟩
    let exOut: ∃ output: Nat2, hm.computes input output := ⟨output, computes⟩
    let out := choiceEx exOut
    let outN := choiceEx out.property
    
    let eqR: out.val = output := stage.haltsConsistent outN.property hw
    let eqL: fn hm input = some out.val := dif_pos exOut
    
    eqL.trans (congr rfl eqR)
  
  def halts (hm: HamkinsMachine) (input: Nat2): Prop :=
    ∃ n: Ordinal, (hm.stage input n).state = hm.haltState
  def loops (hm: HamkinsMachine) (input: Nat2): Prop := hm.fn input = none
  
  def computable (fn: Nat2 → Option Nat2): Prop :=
    ∃ hm: HamkinsMachine, ∀ arg: Nat2, fn arg = hm.fn arg
  
  def trivialMachine: HamkinsMachine := {
    State := Null
    isFinite := ⟨[Null.null], fun n => ⟨⟨0, by simp⟩, by simp⟩⟩
    initialState := Null.null
    haltState := Null.null
    limitState := Null.null
    getMove := fun state symbol => {
      state := state
      symbol := symbol
      dir := Dir.none
    }
    haltHalts := by simp
  }
  
  
  def label: HamkinsMachine → Nat2 :=
    sorry
  
  noncomputable def enumeration (nat2: Nat2): HamkinsMachine :=
    if h: ∃ hm: HamkinsMachine, hm.label = nat2 then
      h.unwrap
    else trivialMachine
end HamkinsMachine


namespace Program
    structure TapeSeq
      (cond: Nat)
      {domain: Set Nat2}
      {codomain: Set Nat2}
      (seqZero: Nat2)
      (loopCompatible: ∀ m: ↑codomain, m.val cond = Two.one → m.val ∈ domain)
      (stepFn: ↑domain → Set Nat2)
    where
      
      seq: Nat → ↑codomain
      
      seqZeroEq: seq 0 = seqZero
      
      condT: ∀ (n: Nat) (ct: (seq n).val cond = Two.one),
        (seq (n + 1)).val ∈ stepFn ⟨seq n, loopCompatible (seq n) ct⟩
      
      condF: ∀ n, (seq n).val cond = Two.zero → seq (n + 1) = (seq n)
    
    -- Why not just extend Tuple in TapeSeq? And use the already defined limsup?
    -- Well, you deal with all the typecasts between Ordinal.omega and .length!
    -- Also, who wants to convert between Nat and Ordinal? Not me.
    noncomputable def TapeSeq.limSup (m: TapeSeq c s lC sF): Nat2 :=
      fun loc =>
        if h: ∃ lowerBound: Nat, ∀ n: Nat,
          lowerBound ≤ n → (m.seq lowerBound).val loc = (m.seq n).val loc
        then
          (m.seq (h.unwrap)).val loc
        else
          Two.one
    end Program

inductive Program:
  (terminatesIf: Set Nat2) →
  (precond: Set Nat2) →
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
      Program terminatesIf precond postcond
  | ite
      (cond: Nat)
      (a: Program aTerminates aPrecond aPostcond)
      (b: Program bTerminates bPrecond bPostcond)
      
      (precond: Set Nat2)
      (postcond: ↑precond → Set Nat2)
      
      (terminatesIf: Set Nat2)
      
      (isSoundPrecond:
        ∀ input: ↑precond,
          (input.val cond = Two.one → aPrecond input) ∧
          (input.val cond = Two.zero → bPrecond input))
      
      (isSoundPostcondA:
        ∀ input: ↑precond,
          (condTrue: input.val cond = Two.one) →
            let apr: aPrecond input := (isSoundPrecond input).left condTrue
            aPostcond ⟨input, apr⟩ ⊆ postcond input)
      
      (isSoundPostcondB:
        ∀ input: ↑precond,
          (condFalse: input.val cond = Two.zero) →
            let bpr: bPrecond input := (isSoundPrecond input).right condFalse
            bPostcond ⟨input, bpr⟩ ⊆ postcond input)
      
      (isSoundTerminatesA: ∀ input: ↑precond,
        terminatesIf input → input.val cond = Two.one → aTerminates input)
      
      (isSoundTerminatesB: ∀ input: ↑precond,
        terminatesIf input → input.val cond = Two.zero → bTerminates input)
    :
      Program terminatesIf precond postcond
  | while
      (cond: Nat)
      (body: Program bTerminates bPrecond bPostcond)
      
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
      
      -- TODO I think this is wrong. It's not just
      -- omega-sequences that must have sound limits,
      -- any sequence must.
      (isSoundPostcondLim:
        ∀ (input: ↑precond)
          (seq: Program.TapeSeq cond input isSoundPrecond bPostcond)
        ,
          (seq.limSup ∈ precond))
      
      (isSoundTerminates:
        ∀ (input: ↑precond)
           (condT: input.val cond = Two.one)
           (output: ↑(bPostcond ⟨input, isSoundPrecond input condT⟩))
          ,
           variant input output)
    :
      Program terminatesIf precond postcond


namespace HM
  -- Aint nobody got time to track bound variables.
  -- If it's free, it contains the empty type.
  inductive PosExpr (Var: Type) where
      -- A variable with which a definition can be associated.
    | varVar (v: Var)
      -- A variable that can be introduced by a quantifier.
    | varNat (n: Nat)
      -- Represents all subsets of expr.
    | subs (expr: PosExpr Var)
      -- Represents all meetsets (sets sharing a common element) of expr.
    | meet (expr: PosExpr Var)
      -- Binary union of a and b.
    | un (a b: PosExpr Var)
      -- Binary intersection of a and b.
    | ir (a b: PosExpr Var)
      -- If cond is inhabited, then expr, else empty.
    | cond (cond expr: PosExpr Var)
      -- Arbitrary union / existential quantifier.
      -- Nc is a complement of n.
    | Un (n nc: Nat) (expr: PosExpr Var)
      -- Arbitrary intersection / universal quantifier.
      -- Nc is a complement of n.
    | Ir (n nc: Nat) (expr: PosExpr Var)
  
  structure DefList
    (Var: Type)
    (fin: Type.IsFinite Var)
  where
    rules: ↑Var → PosExpr Var
    isFinite: ∃ list: List Var, ∀ v: ↑Var, v ∈ list
  
  structure Valuation (Var: Type) :=
    var: ↑Var → Set3 HamkinsMachine
    nat: Nat → Set3 HamkinsMachine
  
  def I (vlt: Valuation Var): PosExpr Var → Set3 HamkinsMachine
    | PosExpr.varVar v => vlt.var v
    | PosExpr.varNat v => vlt.nat v
    | PosExpr.subs a => sorry
    | PosExpr.meet a => sorry
    | PosExpr.cond cond expr => sorry
    | PosExpr.un a b => sorry
    | PosExpr.ir a b => sorry
    | PosExpr.Un var cVar body => sorry
    | PosExpr.Ir var cVar body => sorry
end HM
