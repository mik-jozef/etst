import Utils.Lfp
import WFC.Ch0_Set3


def Null.isFinite: Finite Null := ⟨
  fun _ => Fin.mk 0 (Nat.lt_succ_self 0),
  fun _ => null,
  fun _ => rfl,
  fun ⟨_, isLtOne⟩ =>
    Fin.eq_of_val_eq (Nat.lt_one_iff.mp isLtOne).symm,
⟩

inductive Two
| zero
| one

def Two.flip: Two → Two
| Two.zero => Two.one
| Two.one => Two.zero

def Two.toNat: Two → Nat
| Two.zero => 0
| Two.one => 1

def Two.ofNat: Nat → Two
| 0 => Two.zero
| n+1 => Two.flip (Two.ofNat n)

instance: Coe Two Nat where coe := Two.toNat
instance: Coe Nat Two where coe := Two.ofNat


def shiftNatFn
  (head: T)
  (fn: Nat → T)
:
  Nat → T
|
  0 => head
| Nat.succ n => fn n
  

@[reducible] def Nat2 := Nat → Two
def Nat2.zero: Nat2 := fun _ => Two.zero

-- Converts a number to its binary representation in little endian.
def Nat2.fromNat: Nat → Nat2
| 0 => Nat2.zero
| n+1 => shiftNatFn (Two.ofNat n) (fromNat (n.succ / 2))


def Tuple.Nat2.IsEventuallyZeroAtIndex
  (tuple: Tuple Nat2)
  (index: Nat)
:
  Prop
:=
  ∃ lowerBound: ↑tuple.length,
  ∀ i: ↑tuple.length,
    lowerBound.val ≤ i.val →
    tuple.elements i index = Two.zero

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

def Tuple.Nat2.limSup.eqZeroLength
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
:= by
  unfold limSup;
  rw [if_neg isDefined];
  exact
    funext fun n =>
      if h: IsEventuallyZeroAtIndex tuple n then
        (if_pos h).trans ((isResSound n).mp h).symm
      else
        match hh: result n with
        | Two.zero => absurd hh ((Iff.not (isResSound n)).mp h)
        | Two.one => (if_neg h).trans rfl

def Tuple.Nat2.limSup.eqOfEventuallyConstant
  (t: Tuple Nat2)
  (ifU: Nat2)
  (lowerBound: ↑t.length)
  (res: Nat2)
  (constantAbove:
    ∀ i: ↑t.length,
    lowerBound.val ≤ i → t.elements i = res)
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
        let geLbN: lbN.val ≤ lbMax := Ordinal.le_max_rite _ _
        let geLowerBound: lowerBound ≤ lbMax :=
          Ordinal.le_max_left _ _
        
        let cAboveMax := constantAbove lbMax geLowerBound
        let eqZero := lbN.property lbMax geLbN
        
        (congr cAboveMax.symm rfl).trans eqZero)
      (fun eqZero =>
        ⟨
          lowerBound,
          fun i geLb =>
            (congr (constantAbove i geLb) rfl).trans eqZero
        ⟩)


inductive Dir
| left
| right
| none

def Dir.shift: Dir → Nat → Option Nat
| Dir.left, 0 => Option.none
| Dir.left, x+1 => x
| Dir.right, x => x.succ
| Dir.none, x => x

structure HamkinsMachine.Move (State: Type) where
  nextState: State
  nextSymbol: Two
  dir: Dir

def HamkinsMachine.Move.eq {State: Type}:
  {m0 m1: HamkinsMachine.Move State} →
  m0.nextState = m1.nextState →
  m0.nextSymbol = m1.nextSymbol →
  m0.dir = m1.dir →
  m0 = m1
  
  | ⟨_,_,_⟩, ⟨_,_,_⟩, rfl, rfl, rfl => rfl

@[reducible] def HamkinsMachine.GetMove (State: Type) :=
  State → Two → HamkinsMachine.Move State

/-
  Also known as Infinite time Turing machine.
  
  Note: Unlike the original definition [0], here we only have one tape for
  simplicity. In "Infinite time Turing machines with only one tape" [1],
  the authors claim one-tape machines are [TL;DR: bad]. I believe this to
  be a consequence of a non-ideal definition of the move-left instruction
  while the head is at the zeroth cell (the proper reaction is not to
  stay at the cell and keep computing, but to crash and burn). TODO to be
  proven.
  
  0. https://arxiv.org/abs/math/9808093
  1. https://arxiv.org/abs/math/9907044
-/
structure HamkinsMachine where
  State: Type
  
  isFinite: Finite State
  
  initialState: State
  haltState: State
  limitState: State
  
  getMove: HamkinsMachine.GetMove State
  
  haltHalts (two: Two): getMove haltState two = {
    nextState := haltState
    nextSymbol := two
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
  
  def nextMove
    (hm: HamkinsMachine)
    (config: Configuration hm)
  :
    HamkinsMachine.Move hm.State
  :=
    hm.getMove config.state (config.tape config.head)
  
  def step
    (hm: HamkinsMachine)
    (config: Configuration hm)
  :
    Configuration hm
  :=
    let move := nextMove hm config
    let newHead := move.dir.shift config.head
    
    match newHead with
    | none => config
    | some nh => {
        state := move.nextState
        tape :=
          Function.update
            config.tape
            config.head
            move.nextSymbol
        head := nh
      }
  
  def step.eqHalted
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (move: Move hm.State)
    (moveEq: move = nextMove hm config)
    (newHeadEq: none = move.dir.shift config.head)
  :
    hm.step config = config
  := by
    unfold step
    simp only []
    rw [moveEq.symm, newHeadEq.symm]
  
  def step.eqRunning
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    {move: Move hm.State}
    (moveEq: move = nextMove hm config)
    (newHeadEq: some newHead = move.dir.shift config.head)
  :
    hm.step config = {
      state := move.nextState
      tape :=
        Function.update
          config.tape
          config.head
          move.nextSymbol
      head := newHead
    }
  := by
    unfold step
    simp only []
    rw [moveEq.symm, newHeadEq.symm]
  
  def haltStepIsId
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (isHalt: config.state = hm.haltState)
  :
    hm.step config = config
  :=
    let symbol := config.tape config.head
    
    let move: HamkinsMachine.Move hm.State := {
      nextState := hm.haltState
      nextSymbol := symbol
      dir := Dir.none
    }
    
    let nextConfig: HamkinsMachine.Configuration hm := {
      state := move.nextState
      tape :=
        Function.update
          config.tape
          config.head
          move.nextSymbol
      head := config.head
    }
    
    let nextSteTapeEq: nextConfig.tape = config.tape :=
      Function.update_eq_iff.mpr ⟨rfl, fun _ _ => rfl⟩
    
    let moveEq: hm.getMove hm.haltState symbol = move :=
      hm.haltHalts symbol
    
    let configEq:
      config = ⟨hm.haltState, config.tape, config.head⟩
    :=
      HamkinsMachine.Configuration.eq isHalt rfl rfl
    
    let stepEq: hm.step config = nextConfig :=
      HamkinsMachine.step.eqRunning
        hm
        config
        (move := move)
        (configEq ▸ moveEq.symm)
        (newHead := config.head)
        rfl
    
    stepEq.trans
      (HamkinsMachine.Configuration.eq
        isHalt.symm
        nextSteTapeEq
        rfl)
  
  noncomputable def stage
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    Configuration hm
  :=
    if h: n.IsSuccPrelimit then
      let prevTapes: Tuple Nat2 := {
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
        -- Note: Even if the machine halted, limSup is safe.
        tape := Tuple.Nat2.limSup prevTapes input
        head := 0
      }
    else
      have: n.pred < n := Ordinal.predLtOfNotPrelimit h
      hm.step (hm.stage input n.pred)
    termination_by n
  
  noncomputable def stagesUpTo
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
    (nl: ¬n.IsSuccPrelimit)
  :
    hm.stage input n = hm.step (hm.stage input n.pred)
  :=
    by conv => lhs; unfold stage; rw [dif_neg nl]
  
  @[reducible]
  def stage.IsHaltedAt
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  : Prop :=
    (stage hm input n).state = hm.haltState
  
  structure stage.EqAtLimit
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  where
    (tapeEq:
      (hm.stage input n).tape =
        Tuple.Nat2.limSup (stagesUpTo hm input n) input)
    
    (stateHalt: (∃ nn: ↑n, stage.IsHaltedAt hm input nn)
      → (hm.stage input n).state = hm.haltState)
    
    (stateLimit: n = 0 ∨
      (¬(∃ nn: ↑n, stage.IsHaltedAt hm input nn)
        → (hm.stage input n).state = hm.limitState))
    
    (headEq: (hm.stage input n).head = 0)
  
  def stage.eqAtLimit
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
    (nl: n.IsSuccPrelimit)
  :
    EqAtLimit hm input n
  :=
    {
      tapeEq :=
        by unfold HamkinsMachine.stage; exact dif_pos nl ▸ rfl
      stateHalt := fun ex =>
        by
          unfold HamkinsMachine.stage
          rw [dif_pos nl, if_pos ex]
      stateLimit :=
        if h: n = 0 then
          Or.inl h
        else
          Or.inr fun nex => by
            unfold HamkinsMachine.stage
            rw [dif_pos nl, if_neg nex, if_neg h]
      headEq :=
        by unfold HamkinsMachine.stage; exact dif_pos nl ▸ rfl
    }
  
  structure stage.EqAtZero
    (hm: HamkinsMachine)
    (input: Nat2)
  where
    (tapeEq: (hm.stage input 0).tape = input)
    (stateEq: (hm.stage input 0).state = hm.initialState)
    (headEq: (hm.stage input 0).head = 0)
  
  def stage.eqAtZero
    (hm: HamkinsMachine)
    (input: Nat2)
  :
    EqAtZero hm input
  := {
    tapeEq :=
      let isLimZ := Ordinal.isSuccPrelimit_zero
      let prevStages := stagesUpTo hm input 0
      
      let eqLim:
        (hm.stage input 0).tape
          =
        Tuple.Nat2.limSup prevStages input
      :=
        (eqAtLimit hm input 0 isLimZ).tapeEq
      
      eqLim.trans
        (Tuple.Nat2.limSup.eqZeroLength prevStages input rfl)
    stateEq :=
      let nexHaltState := all.notEx
        (fun _ => trivial)
        (fun (nLe0: { nn // nn < 0 }) _ =>
          False.elim (Ordinal.not_lt_zero nLe0.val nLe0.property))
      
      by
        unfold HamkinsMachine.stage
        rw [
          dif_pos Ordinal.isSuccPrelimit_zero,
          if_neg nexHaltState,
          if_pos rfl,
        ]
    headEq := 
      by
        unfold HamkinsMachine.stage;
        rw [dif_pos Ordinal.isSuccPrelimit_zero]
  }
  
  def stage.eq_step_succ
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    hm.stage input n.succ = hm.step (hm.stage input n)
  :=
    let nSuccNotLimit := Ordinal.succ_not_prelimit n
    let nSuccPredEq: n.succ.pred = n := Ordinal.pred_succ n
    
    let eqSucc:
      hm.stage input n.succ = hm.step (hm.stage input n.succ.pred)
    :=
      stage.eq.step hm input n.succ nSuccNotLimit
    
    let eq: hm.stage input n.succ.pred = hm.stage input n :=
      congr rfl nSuccPredEq
    
    eq ▸ eqSucc
  
  def stage.isHaltedAtGe
    (hAt: stage.IsHaltedAt hm input n)
    {ng: Ordinal}
    (ngGe: n ≤ ng)
  :
    stage.IsHaltedAt hm input ng
  :=
    if hEq: n = ng then
      hEq ▸ hAt
    else
      let ngGt: n < ng := lt_of_le_of_ne ngGe hEq
      let ngNotZero: ng ≠ 0 := Ordinal.ne_zero_of_lt ngGt
      
      if hLim: ng.IsSuccPrelimit then
        let lim := stage.eqAtLimit hm input ng hLim
        lim.stateHalt ⟨⟨n, ngGt⟩, hAt⟩
      else
        have: ng.pred < ng := Ordinal.predLtOfNotPrelimit hLim
        
        let ngGtN: n < ng := lt_of_le_of_ne ngGe hEq
        let ngGePred: n ≤ ng.pred := Ordinal.le_pred_of_lt ngGtN
        
        let haltsAtPred := stage.isHaltedAtGe hAt ngGePred
        
        let stepConstant :=
          haltStepIsId hm (stage hm input ng.pred) haltsAtPred
        
        let stageNgEqStep := stage.eq.step hm input ng hLim
        
        let stageEq := stepConstant.symm.trans stageNgEqStep.symm
        
        by unfold IsHaltedAt; exact stageEq ▸ haltsAtPred
  
  termination_by ng
  
  def stage.isHaltedAtGt
    (hAt: stage.IsHaltedAt hm input n)
    {ng: Ordinal}
    (ngGt: n < ng)
  :
    stage.IsHaltedAt hm input ng
  :=
    stage.isHaltedAtGe hAt (le_of_lt ngGt)
  
  structure stage.IsHaltedAtWith
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal)
  :
    Prop
  where
    isHaltedAt: stage.IsHaltedAt hm input n
    tapeEq: (stage hm input n).tape = output
  
  def stage.haltsConsistent.step
    (hw0: stage.IsHaltedAtWith hm input output0 n)
    (hw1: stage.IsHaltedAtWith hm input output1 n.succ)
  :
    output0 = output1
  :=
    let stage0 := hm.stage input n
    let stage1 := hm.stage input n.succ
    
    let stage0IsHalted: stage0.state = hm.haltState := hw0.isHaltedAt
    
    let stageEqL: stage1 = hm.step stage0 :=
      stage.eq_step_succ hm input n
    
    let stageEqR: hm.step stage0 = stage0 :=
      haltStepIsId hm stage0 stage0IsHalted
    
    let stageEq: hm.stage input n = hm.stage input n.succ :=
      (stageEqL.trans stageEqR).symm
    
    hw0.tapeEq.symm.trans (stageEq ▸ hw1.tapeEq)
  
  def stage.haltsConsistent.le
    (hw0: stage.IsHaltedAtWith hm input output0 n0)
    (hw1: stage.IsHaltedAtWith hm input output1 n1)
    (nLe: n0 ≤ n1)
  :
    output0 = output1
  :=
    if hEq: n0 = n1 then
      hw0.tapeEq.symm.trans (hEq ▸ hw1.tapeEq)
    else
      let n1Lt: n0 < n1 := lt_of_le_of_ne nLe hEq
      
      if h: n1.IsSuccPrelimit then
        let prev := stagesUpTo hm input n1
        
        let lim := stage.eqAtLimit hm input n1 h
        let limTape := lim.tapeEq
        
        let limEq0 :=
          Tuple.Nat2.limSup.eqOfEventuallyConstant
            prev input ⟨n0, n1Lt⟩ output0
          fun nn1 n0LB =>
            have: nn1 < n1 := nn1.property
            
            let outputMid := (hm.stage input nn1).tape
            
            let hwMid:
              stage.IsHaltedAtWith hm input outputMid nn1
            := {
              isHaltedAt := stage.isHaltedAtGe hw0.isHaltedAt n0LB
              tapeEq := rfl
            }
            
            (stage.haltsConsistent.le hw0 hwMid n0LB).symm
        
        limEq0.symm.trans (limTape.symm.trans hw1.tapeEq)
      else
        have := Ordinal.predLtOfNotPrelimit h
        
        let predSuccEq: n1.pred.succ = n1 :=
          Ordinal.succ_pred_of_not_prelimit h
        
        let lt: n0 < n1 := lt_of_le_of_ne nLe hEq
        let lePred: n0 ≤ n1.pred := Ordinal.le_pred_of_lt lt
        
        let tapeAtPred := (hm.stage input n1.pred).tape
        
        let hwPred:
          stage.IsHaltedAtWith hm input tapeAtPred n1.pred
        := {
          isHaltedAt := stage.isHaltedAtGe hw0.isHaltedAt lePred
          tapeEq := rfl
        }
        
        lePred.lt_or_eq.elim
          (fun nLtPred =>
            let eqR :=
              stage.haltsConsistent.le hw0 hwPred nLtPred.le
            
            eqR.trans (stage.haltsConsistent.step
              hwPred (predSuccEq.symm ▸ hw1)))
          (fun nEqPred =>
            stage.haltsConsistent.step
              (nEqPred ▸ hw0)
              (predSuccEq.symm ▸ hw1))
  termination_by n1

  def stage.haltsConsistent
    {n0 n1: Ordinal.{u}}
    (hw0: stage.IsHaltedAtWith hm input output0 n0)
    (hw1: stage.IsHaltedAtWith hm input output1 n1)
  :
    output0 = output1
  :=
    (lt_or_ge n0 n1).elim
      (fun lt => stage.haltsConsistent.le hw0 hw1 lt.le)
      (fun ge => (stage.haltsConsistent.le hw1 hw0 ge).symm)
  
  def Computes.{u}
    (hm: HamkinsMachine)
    (input output: Nat2)
  :
    Prop
  :=
    ∃ (n: Ordinal.{u})
    ,
      stage.IsHaltedAtWith hm input output n
  
  noncomputable def fn.{u}
    (hm: HamkinsMachine)
    (input: Nat2)
  :
    Option Nat2
  :=
    if h: ∃ output, Computes.{u} hm input output
    then some h.unwrap
    else none
  
  def haltsConsistent
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal.{u})
    (hw: stage.IsHaltedAtWith hm input output n)
  :
    fn.{u} hm input = output
  :=
    let computes: hm.Computes input output := ⟨n, hw⟩
    
    -- This ought to work. :/
    -- (The above is a normative, not descriptive, statement.)
    -- let ⟨out, ⟨n1, hw1⟩⟩: ∃ out, hm.computes input out :=
    --   ⟨output, computes⟩
    let exOut: ∃ out, hm.Computes input out := ⟨output, computes⟩
    let out := exOut.unwrap
    let hw1 := out.property.unwrap.property
    
    let eqR: out = output := stage.haltsConsistent hw1 hw
    let eqL: fn hm input = some out.val := by
      unfold fn
      rw [dif_pos exOut]
    
    eqL.trans (congr rfl eqR)
  
  def Halts.{u} (hm: HamkinsMachine) (input: Nat2): Prop :=
    ∃ n: Ordinal.{u}, (hm.stage input n).state = hm.haltState
  
  def Loops.{u} (hm: HamkinsMachine) (input: Nat2): Prop :=
    fn.{u} hm input = none
  
  def IsComputable.{u} (fn: Nat2 → Option Nat2): Prop :=
    ∃ hm: HamkinsMachine,
    ∀ arg: Nat2,
    fn arg = HamkinsMachine.fn.{u} hm arg
  
  def trivialMachine: HamkinsMachine := {
    State := Null
    isFinite := Null.isFinite
    initialState := Null.null
    haltState := Null.null
    limitState := Null.null
    getMove := fun state symbol => {
      nextState := state
      nextSymbol := symbol
      dir := Dir.none
    }
    haltHalts := fun _ => rfl
  }
  
  
  -- def encoding: HamkinsMachine → Nat :=
  --   sorry
  -- 
  -- noncomputable def enumeration (n: Nat): HamkinsMachine :=
  --   if h: ∃ hm: HamkinsMachine, hm.label = nat2 then
  --     h.unwrap
  --   else trivialMachine
end HamkinsMachine
