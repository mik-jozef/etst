import Fixpoint

open Classical


inductive Two
  | zero
  | one

def Nat2 := Nat → Two
def Nat2.zeros: Nat2 := fun _ => Two.zero

noncomputable def limSup (t: Tuple Nat2) (ifZero: Nat2): Nat2 :=
  -- The limit is undefined in this case. (How convenient :P)
  if t.length = Ordinal.zero then
    ifZero
  else
    fun n: Nat =>
      let eventuallyZero :=
        ∃ inT: ↑t.length,
          ∀ inTGe: ↑t.length,
            inT.val = inTGe.val ∨ inT.val < inTGe.val →
              t.elements inTGe n = Two.zero
      
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

structure Ittm.Move (State: Type) where
  state: State
  symbol: Two
  dir: Dir

structure Ittm where
  State: Type
  
  haltState: State
  limitState: State
  
  getMove: State → Two → Ittm.Move State
  
  haltHalts (two: Two): getMove haltState two = {
    state := haltState
    symbol := two
    dir := Dir.none
  }


namespace Ittm
  structure Configuration (tm: Ittm) where
    state: tm.State
    tape: Nat2
    head: Nat
  
  def step (tm: Ittm) (config: Configuration tm): Configuration tm :=
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
  
  noncomputable def stage (tm: Ittm) (initial: Nat2) (n: Ordinal):
    Configuration tm
  :=
    if h: n.isLimit then
      let prevStages: Tuple Nat2 := {
        length := n,
        elements :=
          fun nn =>
            have: nn < n := nn.property
            (stage tm initial nn).tape
      }
      
      {
        state := tm.limitState
        tape := limSup prevStages initial
        head := 0
      }
    else
      match hh: n.pred with
        | none => False.elim (h hh)
        | some pred =>
            have: pred < n := n.predLt pred hh
            step tm (stage tm initial pred)
    termination_by stage tm n => n
  
  def computes (tm: Ittm) (input output: Nat2): Prop :=
    ∃ n: Ordinal,
      (stage tm input n).state = tm.haltState ∧
      (stage tm input n).tape = output
  
  noncomputable def compute (tm: Ittm) (input: Nat2): Option Nat2 :=
    if h: ∃ output: Nat2, tm.computes input output then
      some (choiceEx h)
    else
      none
  
  def halts (tm: Ittm) (input: Nat2): Prop := tm.compute input ≠ none
  def loops (tm: Ittm) (input: Nat2): Prop := tm.compute input = none
  
  def computable (fn: Nat2 → Nat2): Prop :=
    ∃ tm: Ittm, ∀ arg: Nat2, tm.compute arg = fn arg
end Ittm
