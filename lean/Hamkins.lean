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

-- Infinite time Turing machine is too long. I hereby name
-- you Hamkins machine.
structure HamkinsMachine where
  State: Type
  
  finite: ∃ list: List State, ∀ s: State, list.has s
  
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
        state := hm.limitState
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
  
  noncomputable def compute (hm: HamkinsMachine) (input: Nat2): Option Nat2 :=
    if h: ∃ output: Nat2, hm.computes input output then
      some (choiceEx h)
    else
      none
  
  def halts (hm: HamkinsMachine) (input: Nat2): Prop := hm.compute input ≠ none
  def loops (hm: HamkinsMachine) (input: Nat2): Prop := hm.compute input = none
  
  def computable (fn: Nat2 → Nat2): Prop :=
    ∃ hm: HamkinsMachine, ∀ arg: Nat2, fn arg = hm.compute arg
end HamkinsMachine


namespace Program
  inductive MemoryLayout
    | tape
    | pair (a b: MemoryLayout)
    | seq (f: Nat → MemoryLayout)
  
  structure MemoryLocation.Pair where
    tape: Two
    index: Nat
  
  structure MemoryLocation.Seq where
    tape: Nat
    index: Nat
  
  -- Lean cannot do proper mutually recursive definitions.
  def MemoryLayout.Location: (layout: MemoryLayout) → Type
    | MemoryLayout.tape => Nat
    | MemoryLayout.pair a b =>
        (loc: MemoryLocation.Pair) ×
          (if loc.tape = Two.zero then a.Location else b.Location)
    | MemoryLayout.seq f =>
        (loc: MemoryLocation.Seq) × (f loc.tape).Location
  
  def MemoryLayout.address
    (layout: MemoryLayout)
    (location: layout.Location)
  :
    Nat
  :=
    match layout with
      | tape => location
      | pair a b =>
          match h: location.fst.tape with
            | Two.zero =>
                let aLoc: a.Location :=
                  (@dif_pos (location.fst.tape = Two.zero) _ h Type
                    (fun _ => a.Location) (fun _ => b.Location)) ▸ location.snd
                (a.address aLoc) + (2 * location.fst.index)
            | Two.one =>
                let bLoc: b.Location :=
                  (@dif_neg (location.fst.tape = Two.zero) _
                    (fun eq => Two.noConfusion (h ▸ eq)) Type
                    (fun _ => a.Location) (fun _ => b.Location)) ▸ location.snd
                (b.address bLoc) + (2 * location.fst.index) + 1
      | seq f => sorry
  
  inductive MemoryLayout.Update
    | none
    | toPair
    | toSeq
    | collapse
  
  def MemoryLayout.update (layout: MemoryLayout): MemoryLayout.Update → MemoryLayout
    | Update.none => layout
    | Update.toPair => MemoryLayout.pair layout tape
    | Update.toSeq => MemoryLayout.seq fun n => if n = 0 then layout else tape
    | Update.collapse =>
        match layout with
          | tape => tape
          | pair a _ => a
          | seq f => f 0
  
  inductive Instruction (layout: MemoryLayout) where
    | assign (dest src: layout.Location)
    | ite (cond: layout.Location) (a b: Instruction layout)
    | while (cond: layout.Location) (body: Instruction layout)
    | seq (a b: Instruction layout)
  
  def Instruction.computes
    {layout: MemoryLayout}
  :
    Instruction layout → Nat2 → Nat2
  | assign dest src => sorry
  | ite cond a b => if ()
  
  def MappingF.index (tape index: Nat): Nat :=
    2 ^ tape * (2 * index + 1) - 1
  def MappingG.index: Nat2 → State := sorry
  
  def MappingF: State → Nat2 := sorry
  def MappingG: Nat2 → State := sorry
  
  def computable (fn: Function): Prop := sorry
  
  namespace computable
    def const (fn: Nat2 → Nat2) (fnCmp: HamkinsMachine.computable fn := ⟨
      {},
      sorry
    ⟩
    
    def oneTape: Nat := sorry
  end computable
