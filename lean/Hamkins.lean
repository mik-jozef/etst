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

def List.has (list: List T) (t: T): Prop :=
  ∃ n: Fin list.length, list.get n = t

def List.hasAll (list: List T): Prop :=
  ∀ t: T, list.has t

def Type.isFinite (T: Type): Prop :=
  ∃ list: List T, list.hasAll

def Type.IsFinite := { T: Type // Type.isFinite T }

-- TODO do I need this?
-- def Type.finite.cardinality (isF: Type.isFinite T):
--   Least (fun n: Nat => ∃ list: List T, list.hasAll ∧ list.length = n)
-- :=
--   sorry

structure HamkinsMachine where
  State: Type
  
  isFinite: Type.isFinite State
  
  haltState: State
  limitState: State
  
  getMove: State → Two → HamkinsMachine.Move State
  
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
  
  def step (hm: HamkinsMachine) (config: Configuration tm): Configuration tm :=
    let move := tm.getMove (config.state) (config.tape config.head)
    let newHead := move.dir.shift config.head
    
    match newHead with
      | none => config
      | some nh =>
          {
            state := move.state
            tape := fun n => if n = config.head then move.symbol else config.tape n
            head := nh
          }
  
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
        tape := limSup prevStages initial
        head := 0
      }
    else
      match hh: n.pred with
        | none => False.elim (h hh)
        | some pred =>
            have: pred < n := n.predLt pred hh
            step hm (stage hm initial pred)
    termination_by stage hm n => n
  
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
  
  
  def label: HamkinsMachine → Nat2 :=
    sorry
  
  
  noncomputable def enumeration (nat2: Nat2): HamkinsMachine :=
    if h: ∃ hm: HamkinsMachine, hm.label = nat2 then
      choiceEx h
    else {
      State := Null
      isFinite := ⟨[Null.null], fun n => ⟨⟨0, by simp⟩, by simp⟩⟩
      haltState := Null.null
      limitState := Null.null
      getMove := fun state symbol => {
        state := state
        symbol := symbol
        dir := Dir.none
      }
      haltHalts := by simp
    }
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
      
      -- TODO do I mneed this?
      -- Typing in a bus is hard and weird.
      def fromAddress: (layout: Layout) → (i: Nat) → layout.Location
        | Layout.tape, i => Layout.Location.tape i
        | Layout.pair a b, i => sorry
        | Layout.seq f, i => sorry
    end Location
    
    def pop: Layout → Layout
      | tape => tape
      | pair a _ => a
      | seq f => f 0
    
    def Memory (layout: Layout) := layout.Location → Two
    
    -- TODO do I need this?
    def Memory.toTape {layout: Layout} (m: layout.Memory): Nat2 :=
      fun i =>
        match layout with
        | Layout.tape => sorry
        | Layout.pair a b => sorry
        | Layout.seq f => sorry
    
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
      (dest src: l.Location)
      (m: l.Memory)
    :
      l.Memory
    :=
      fun loc => if loc = dest then m src else m loc
  end Layout

def Nat2.toMemory (tape: Nat2) {layout: Layout}: layout.Memory :=
  fun loc => tape loc.address


inductive Program:
  (lIn lOut: Layout) →
  (terminatesIf: Set lIn.Memory) →
  (precond: Set lIn.Memory) →
  (postcond: ↑precond → Set lOut.Memory) →
  Type
where
  | assign
      (dest src: layout.Location)
      
      (precond: Set layout.Memory)
      (postcond: ↑precond → Set layout.Memory)
      
      (isSound: ∀ m: ↑precond, m.val.assign dest src ∈ postcond m)
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
      (additionalLayout: Layout)
      
      (precond: Set lIn.Memory)
    :
      Program lIn (lIn.pair additionalLayout) terminatesIf precond
        (fun mIn mOut =>
          (∀ loc: lIn.Location,
            mOut (Layout.Location.left loc) = mIn.val loc) ∧
          (∀ loc: additionalLayout.Location,
            mOut (Layout.Location.rite loc) = Two.zero))
  | pop
    : Program lIn lIn.pop terminatesIf precond (fun mIn mOut =>
        match lIn with
          | Layout.tape => mOut = mIn.val
          | Layout.pair a b =>
              ∀ loc, mOut loc = mIn.val (Layout.Location.left loc)
          | Layout.seq f =>
              ∀ loc, mOut loc = mIn.val (Layout.Location.seq 0 loc))

namespace Program
  def compile: Program lIn lOut terminatesIf precond postcond →
    {
      hm: HamkinsMachine
    //
      And
        (∀ (m: ↑terminatesIf)
          -- TODO perhaps would be better to implement m.toTape instead.
          (tape: Nat2)
          (tapeSound: ∀ locIn: lIn.Location, tape locIn.address = m.val l)
        ,
          ∃ tapeOut: Nat2, hm.fn tape = some tapeOut)
        (∀ (m: ↑precond)
          (tape: Nat2)
          (tapeSound: ∀ locIn: lIn.Location, tape locIn.address = m.val l)
          (locOut: lOut.Location)
        ,
          match hm.fn tape with
          | none => True
          | some tapeOut => Nat2.toMemory tapeOut ∈ postcond m)
    }
  
    | assign dest src precond postcond isSound => sorry
    | ite cond a b precond postcond terminatesIf isSoundPrecond
        isSoundPostcondA isSoundPostcondB
        isSoundTerminatesA isSoundTerminatesB => sorry
    | Program.while cond body precond postcond terminatesIf
        variant variantTransitive isSoundPrecond
        isSoundPostcondStep isSoundPostcondLim isSoundTerminates => sorry
    | seq a b precond postcond terminatesIf
        isSoundPrecondA isSoundPrecondB isSoundPostcond
        isSoundTerminatesA isSoundTerminatesB => sorry
    | addPair additionalLayout precond => sorry
    | pop => sorry
end Program


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
