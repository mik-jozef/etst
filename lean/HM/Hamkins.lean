import Fixpoint

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

def Nat2.fromNat (n: Nat) :=
  if h: n = 0 then
    Nat2.zeros
  else
    let nGtZero: 0 < n :=
      match n with
        | Nat.zero => False.elim (h rfl)
        | Nat.succ n => Nat.succ_pos n
    
    fun i =>
      match i with
      | Nat.zero => if n % 2 = 0 then Two.zero else Two.one
      | Nat.succ iPrev =>
          have: n / 2 < n := Nat.div_lt_self nGtZero Nat.le.refl
          Nat2.fromNat (n / 2) iPrev


noncomputable def limSup (t: Tuple Nat2) (ifUndefined: Nat2): Nat2 :=
  if t.length = Ordinal.zero then
    ifUndefined
  else
    fun n: Nat =>
      let eventuallyZero :=
        ∃ lowerBound: ↑t.length,
          ∀ i: ↑t.length,
            lowerBound.val ≤ i.val → t.elements i n = Two.zero
      
      if eventuallyZero then Two.zero else Two.one


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

-- TODO do I need this?
-- def Type.finite.cardinality (isF: Type.isFinite T):
--   Least (fun n: Nat => ∃ list: List T, list.hasAll ∧ list.length = n)
-- :=
--   sorry

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
  
  isFinite: Type.isFinite State
  
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
  
  def step (hm: HamkinsMachine) (config: Configuration hm): Configuration hm :=
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
    by unfold step rw [moveEq.symm] rw [newHeadEq.symm]
  
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
    by unfold step rw [moveEq.symm] rw [newHeadEq.symm]
  
  noncomputable def stage (hm: HamkinsMachine) (initial: Nat2) (n: Ordinal):
    Configuration hm
  :=
    if h: n.isLimit then
      let prevStages: Tuple Nat2 := {
        length := n,
        elements :=
          fun nn =>
            have: nn < n := nn.property
            (stage hm initial nn).tape
      }
      
      {
        state :=
          if ∃ nn: ↑n,
            have: nn < n := nn.property
            (hm.stage initial nn).state = hm.haltState
          then
            hm.haltState
          else
            hm.limitState
        -- If the machine halted, limSup is safe.
        tape := limSup prevStages initial
        head := 0
      }
    else
      let nPred := Ordinal.nLimit.pred n h
      
      have := Ordinal.nLimit.pred.lt n h
      hm.step (hm.stage initial nPred)
    termination_by stage hm n => n
  
  def stage.eq.step
    (hm: HamkinsMachine)
    (initial: Nat2)
    (n: Ordinal)
    (nl: ¬n.isLimit)
  :
    hm.stage initial n = hm.step (hm.stage initial (Ordinal.nLimit.pred n nl))
  :=
    by conv =>
      lhs
      unfold stage
      rw [dif_neg nl]
  
  def computes (hm: HamkinsMachine) (input output: Nat2): Prop :=
    ∃ n: Ordinal,
      (stage hm input n).state = hm.haltState ∧
      (stage hm input n).tape = output
  
  noncomputable def fn (hm: HamkinsMachine) (input: Nat2): Option Nat2 :=
    if h: ∃ output: Nat2, hm.computes input output then
      some (choiceEx h)
    else
      none
  
  def halts (hm: HamkinsMachine) (input: Nat2): Prop := hm.fn input ≠ none
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
      choiceEx h
    else trivialMachine
end HamkinsMachine


namespace Program
  -- Memory layout. Allows storing multiple variables on
  -- a single tape.
  inductive Layout
    | tape
    | pair (a b: Layout)
    | seq (f: Nat → Layout)
  
  namespace Layout
    inductive Location: (layout: Layout) → Type
      | tape (index: Nat): Location Layout.tape
      | left (_: Location a): Location (Layout.pair a b)
      | rite (_: Location b): Location (Layout.pair a b)
      | seq (n: Nat) (_: Location (f n)): Location (Layout.seq f)
    
    namespace Location
      def index: (l: Location Layout.tape) → Nat
        | Location.tape n => n
      
      def isLeft: (l: Location (Layout.pair a b)) → Bool
        | Location.left _ => true
        | Location.rite _ => false
      
      def seqN: (l: Location (Layout.seq f)) → Nat
        | Location.seq i _ => i
      
      def seqLoc: (l: Location (Layout.seq f)) → Location (f (l.seqN))
        | Location.seq _ loc => loc
      
      -- TODO feel free to replace with any other bijection
      -- if it makes your life more comfortable.
      def seqIndex (tapeIndex indexInTape: Nat): Nat :=
        if tapeIndex = 0 then
          2 * indexInTape
        else
          2 * (seqIndex (tapeIndex - 1) indexInTape) + 1
      
      def address {layout: Layout} (location: layout.Location): Nat :=
        match layout with
          | Layout.tape => location.index
          | pair _ _ =>
              match location with
              | Location.left loc => 2 * loc.address
              | Location.rite loc => 2 * loc.address + 1
          | Layout.seq _ =>
              seqIndex location.seqN location.seqLoc.address
    end Location
    
    -- TODO do I need this?
    -- Typing in a bus is hard and weird.
    def toLocation: (layout: Layout) → (i: Nat) → layout.Location
      | Layout.tape, i => Layout.Location.tape i
      | Layout.pair a b, i => sorry
      | Layout.seq f, i => sorry
    
    def pop: Layout → Layout
      | tape => tape
      | pair a _ => a
      | seq f => f 0
    
    def Memory (layout: Layout) := layout.Location → Two
    
    -- TODO do I need this?
    def Memory.toTape {layout: Layout} (m: layout.Memory): Nat2 :=
      fun i => m (layout.toLocation i)
    
    structure MemSeq
      (layout: Layout)
      (cond: layout.Location)
      {domain: Set layout.Memory}
      {codomain: Set layout.Memory}
      (seqZero: layout.Memory)
      (loopCompatible: ∀ m: ↑codomain, m.val cond = Two.one → m.val ∈ domain)
      (stepFn: ↑domain → Set layout.Memory)
    where
      
      seq: Nat → ↑codomain
      
      seqZeroEq: seq 0 = seqZero
      
      condT: ∀ (n: Nat) (ct: (seq n).val cond = Two.one),
        (seq (n + 1)).val ∈ stepFn ⟨seq n, loopCompatible (seq n) ct⟩
      
      condF: ∀ n, (seq n).val cond = Two.zero → seq (n + 1) = (seq n)
    
    -- Why not just extend Tuple in MemSeq? And use the already defined limsup?
    -- Well, you deal with all the typecasts between Ordinal.omega and .length!
    -- Also, who wants to convert between Nat and Ordinal? Not me.
    noncomputable def MemSeq.limSup (m: MemSeq layout c s lC sF): layout.Memory :=
      fun loc =>
        if h: ∃ lowerBound: Nat, ∀ n: Nat,
          lowerBound ≤ n → (m.seq lowerBound).val loc = (m.seq n).val loc
        then
          (m.seq (choiceEx h)).val loc
        else
          Two.one
    
    noncomputable def Memory.assign
      {l: Layout}
      (src dest: l.Location)
      (m: l.Memory)
    :
      l.Memory
    :=
      fun loc => if loc = dest then m src else m loc
  end Layout
end Program

def Nat2.toMemory (tape: Nat2) {layout: Program.Layout}: layout.Memory :=
  fun loc => tape loc.address


inductive Program:
  (lIn lOut: Program.Layout) →
  (terminatesIf: Set lIn.Memory) →
  (precond: Set lIn.Memory) →
  (postcond: ↑precond → Set lOut.Memory) →
  Type
where
  | assign
      (src dest: layout.Location)
      
      (precond: Set layout.Memory)
      (postcond: ↑precond → Set layout.Memory)
      
      (isSound: ∀ m: ↑precond, m.val.assign src dest ∈ postcond m)
    :
      Program layout layout terminatesIf precond postcond
  | ite
      (cond: layout.Location)
      (a: Program layout layout aTerminates aPrecond aPostcond)
      (b: Program layout layout bTerminates bPrecond bPostcond)
      
      (precond: Set layout.Memory)
      (postcond: ↑precond → Set layout.Memory)
      
      (terminatesIf: Set layout.Memory)
      
      (isSoundPrecond:
        ∀ m: ↑precond,
          (m.val cond = Two.one → aPrecond m) ∧
          (m.val cond = Two.zero → bPrecond m))
      
      (isSoundPostcondA:
        ∀ m: ↑precond,
          (condTrue: m.val cond = Two.one) →
            let apr: aPrecond m := (isSoundPrecond m).left condTrue
            aPostcond ⟨m, apr⟩ ⊆ postcond m)
      
      (isSoundPostcondB:
        ∀ m: ↑precond,
          (condFalse: m.val cond = Two.zero) →
            let bpr: bPrecond m := (isSoundPrecond m).right condFalse
            bPostcond ⟨m, bpr⟩ ⊆ postcond m)
      
      (isSoundTerminatesA: ∀ m: ↑precond,
        terminatesIf m → m.val cond = Two.one → aTerminates m)
      
      (isSoundTerminatesB: ∀ m: ↑precond,
        terminatesIf m → m.val cond = Two.zero → bTerminates m)
    :
      Program layout layout terminatesIf precond postcond
  | while
      (cond: layout.Location)
      (body: Program layout layout bTerminates bPrecond bPostcond)
      
      (precond: Set layout.Memory)
      (postcond: ↑precond → Set layout.Memory)
      
      (terminatesIf: Set layout.Memory)
      
      (variant: (a b: layout.Memory) → Prop)
      (variantTransitive:
        (ab: variant a b) →
        (bc: variant b c) →
        variant a c)
      
      (isSoundPrecond: ∀ m: ↑precond, m.val cond = Two.one → bPrecond m)
      
      (isSoundPostcondStep:
        ∀ m: ↑precond,
          (condTrue: m.val cond = Two.one) →
          let bpr := isSoundPrecond m condTrue
          bPostcond ⟨m, bpr⟩ ⊆ precond)
      
      (isSoundPostcondLim:
        ∀ (m: ↑precond)
          (seq: layout.MemSeq cond m.val isSoundPrecond bPostcond)
        ,
          (seq.limSup ∈ precond))
      
      (isSoundTerminates:
        ∀ (mIn: ↑precond)
           (condT: mIn.val cond = Two.one)
           (mOut: ↑(bPostcond ⟨mIn, isSoundPrecond mIn condT⟩))
          ,
           variant mIn mOut)
    :
      Program layout layout terminatesIf precond postcond
  | seq
      (a: Program lIn lMid aTerminates aPrecond aPostcond)
      (b: Program lMid lOut bTerminates bPrecond bPostcond)
      
      (precond: Set lIn.Memory)
      (postcond: ↑precond → Set lOut.Memory)
      
      (terminatesIf: Set lIn.Memory)
      
      (isSoundPrecondA: ∀ m: ↑precond, aPrecond m)
      
      (isSoundPrecondB:
        ∀ (m: ↑precond) (mid: lMid.Memory),
          mid ∈ aPostcond ⟨m, isSoundPrecondA m⟩ → bPrecond mid)
      
      (isSoundPostcond:
        ∀ (mA: ↑precond) (mB: ↑(aPostcond ⟨mA, isSoundPrecondA mA⟩)),
          bPostcond ⟨mB, isSoundPrecondB mA mB mB.property⟩ ⊆ postcond mA)
      
      (isSoundTerminatesA:
        ∀ m: ↑precond, terminatesIf m → aTerminates m)
      
      (isSoundTerminatesB:
        ∀ (m: ↑precond) (mid: lMid.Memory), terminatesIf m →
          mid ∈ aPostcond ⟨m, isSoundPrecondA m⟩ → bTerminates mid)
    :
      Program lIn lOut terminatesIf precond postcond
  | addPair
      (additionalLayout: Program.Layout)
      
      (precond: Set lIn.Memory)
    :
      Program lIn (lIn.pair additionalLayout) terminatesIf precond
        (fun mIn mOut =>
          (∀ loc: lIn.Location,
            mOut (Program.Layout.Location.left loc) = mIn.val loc) ∧
          (∀ loc: additionalLayout.Location,
            mOut (Program.Layout.Location.rite loc) = Two.zero))
  | pop
    : Program lIn lIn.pop terminatesIf precond (fun mIn mOut =>
        match lIn with
          | Program.Layout.tape => mOut = mIn.val
          | Program.Layout.pair a b =>
              ∀ loc, mOut loc = mIn.val (Program.Layout.Location.left loc)
          | Program.Layout.seq f =>
              ∀ loc, mOut loc = mIn.val (Program.Layout.Location.seq 0 loc))


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
    | Un (n: Nat) (expr: PosExpr Var)
      -- Arbitrary intersection / universal quantifier.
    | Ir (n: Nat) (expr: PosExpr Var)
  
  structure DefList
    (Var: Type)
    (fin: Type.isFinite Var)
  where
    rules: ↑Var → PosExpr Var
    isFinite: ∃ list: List Var, ∀ v: ↑Var, v ∈ list
  
  structure Valuation (Var: Type) :=
    var: ↑Var → HamkinsMachine
    nat: Nat → HamkinsMachine
  
  def I (vlt: Valuation Var): PosExpr Var → HamkinsMachine
    | PosExpr.varVar v => vlt.var v
    | PosExpr.varNat v => vlt.nat v
    | PosExpr.subs a => sorry
    | PosExpr.meet a => sorry
    | PosExpr.cond cond expr => sorry
    | PosExpr.un a b => sorry
    | PosExpr.ir a b => sorry
    | PosExpr.Un var body => sorry
    | PosExpr.Ir var body => sorry
end HM
