import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.SetTheory.Ordinal.Arithmetic

open Classical

universe u


inductive Two
| zero
| one
deriving DecidableEq, Repr

abbrev Nat2 := Nat → Two
def Nat2.zero: Nat2 := fun _ => Two.zero

instance: CoeSort Ordinal.{u} (Type (u+1)) := ⟨fun o => Set.Iio o⟩

structure Tuple (T: Type*) where
  length: Ordinal.{u}
  elements: length → T


namespace Tuple.Nat2
  /-
    A tape `index` is eventually zero in `tuple` if there is a stage
    beyond which all tapes of the tuple carry `Two.zero` at `index`.
  -/
  def IsEventuallyZeroAtIndex (tuple: Tuple Nat2) (index: Nat): Prop :=
    ∃ lowerBound: Ordinal,
      lowerBound < tuple.length ∧
      ∀ i: tuple.length,
        lowerBound ≤ i.val →
        tuple.elements i index = Two.zero

  /-
    The limit superior of a tuple of tapes: at each index it is
    `Two.zero` iff the index is eventually zero along the tuple.
  -/
  noncomputable def limSup (tuple: Tuple Nat2): Nat2 :=
    fun n =>
      if IsEventuallyZeroAtIndex tuple n then Two.zero else Two.one

  /-
    If a tuple is eventually constantly `res` (from `lowerBound` on),
    then its `limSup` is `res`.
  -/
  def limSup.eqOfEventuallyConstant
    (t: Tuple Nat2)
    (res: Nat2)
    (lowerBound: Ordinal)
    (lbLt: lowerBound < t.length)
    (constantAbove:
      ∀ i: t.length, lowerBound ≤ i.val → t.elements i = res)
  :
    limSup t = res
  :=
    funext fun n =>
      match hRes: res n with
      | Two.zero =>
        let isEv: IsEventuallyZeroAtIndex t n :=
          ⟨
            lowerBound,
            lbLt,
            fun i le => (congrFun (constantAbove i le) n).trans hRes,
          ⟩
        if_pos isEv
      | Two.one =>
        let notEv: ¬ IsEventuallyZeroAtIndex t n :=
          fun ⟨lb, lbLt', hZero⟩ =>
            let i: t.length := ⟨max lowerBound lb, max_lt lbLt lbLt'⟩
            let eqOne: t.elements i n = Two.one :=
              (congrFun (constantAbove i (le_max_left _ _)) n).trans hRes
            let eqZero: t.elements i n = Two.zero :=
              hZero i (le_max_right _ _)
            Two.noConfusion (eqOne.symm.trans eqZero)
        if_neg notEv
end Tuple.Nat2


inductive Dir
| left
| right
| none

/-
  The new head position after moving in a direction, or `none` if
  the machine crashes (moving left off the zeroth cell).
-/
def Dir.shift: Dir → Nat → Option Nat
| Dir.left, 0 => Option.none
| Dir.left, x + 1 => some x
| Dir.right, x => some (x + 1)
| Dir.none, x => some x


structure HamkinsMachine.Move (State: Type) where
  nextState: State
  nextSymbol: Two
  dir: Dir

abbrev HamkinsMachine.GetMove (State: Type) :=
  State → Two → HamkinsMachine.Move State

/-
  Also known as Infinite time Turing machine.
  
  Note: Unlike the original definition [0], here we only have one
  tape for simplicity. In "Infinite time Turing machines with only
  one tape" [1], the authors claim one-tape machines are [TL;DR: bad].
  I believe this to be a consequence of a non-ideal definition of the
  move-left instruction while the head is at the zeroth cell (the
  proper reaction is not to stay at the cell and keep computing, but
  to crash and burn (here implemented with entering an infinite loop)).
  
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

  def nextMove
    (hm: HamkinsMachine)
    (config: hm.Configuration)
  :
    HamkinsMachine.Move hm.State
  :=
    hm.getMove config.state (config.tape config.head)

  def step
    (hm: HamkinsMachine)
    (config: hm.Configuration)
  :
    hm.Configuration
  :=
    match (hm.nextMove config).dir.shift config.head with
    | Option.none => config -- Moving left off cell 0 gets us stuck.
    | some newHead => {
        state := (hm.nextMove config).nextState
        tape :=
          Function.update
            config.tape
            config.head
            (hm.nextMove config).nextSymbol
        head := newHead
      }

  -- Stepping a halted configuration leaves it unchanged.
  def haltStepIsId
    (hm: HamkinsMachine)
    (config: hm.Configuration)
    (isHalt: config.state = hm.haltState)
  :
    hm.step config = config
  := by
    have hmove:
      hm.nextMove config = {
        nextState := hm.haltState
        nextSymbol := config.tape config.head
        dir := Dir.none
      }
    := by
      unfold HamkinsMachine.nextMove
      rw [isHalt]
      exact hm.haltHalts _
    unfold HamkinsMachine.step
    rw [hmove]
    simp only [Dir.shift, Function.update_eq_self]
    rw [← isHalt]

  /-
    The configuration of `hm` on `input` at transfinite stage `n`.
    Defined by transfinite (limit) recursion:
    - at `0` the tape is the input and the state is initial;
    - at a successor we take a single `step`;
    - at a limit the tape is the `limSup` of the previous tapes, and
      the machine halts if it has halted at any earlier stage.
  -/
  noncomputable def stage
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    hm.Configuration
  :=
    Ordinal.limitRecOn n
      {
        state := hm.initialState
        tape := input
        head := 0
      }
      (fun _ prev => hm.step prev)
      (fun o _ ih => {
        state :=
          if ∃ nn: o, (ih nn.val nn.property).state = hm.haltState then
            hm.haltState
          else
            hm.limitState
        tape :=
          Tuple.Nat2.limSup {
            length := o
            elements := fun nn => (ih nn.val nn.property).tape
          }
        head := 0
      })

  noncomputable def stagesUpTo
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    Tuple Nat2
  := {
    length := n
    elements := fun nn => (hm.stage input nn.val).tape
  }

  theorem stage_zero
    (hm: HamkinsMachine)
    (input: Nat2)
  :
    hm.stage input 0 = {
      state := hm.initialState
      tape := input
      head := 0
    }
  :=
    Ordinal.limitRecOn_zero ..

  theorem stage_succ
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    hm.stage input (Order.succ n) = hm.step (hm.stage input n)
  :=
    Ordinal.limitRecOn_succ ..

  theorem stage_limit
    (hm: HamkinsMachine)
    (input: Nat2)
    {n: Ordinal}
    (h: Order.IsSuccLimit n)
  :
    hm.stage input n = {
      state :=
        if ∃ nn: n, (hm.stage input nn.val).state = hm.haltState then
          hm.haltState
        else
          hm.limitState
      tape := Tuple.Nat2.limSup (hm.stagesUpTo input n)
      head := 0
    }
  :=
    Ordinal.limitRecOn_limit n _ _ _ h

  def stage.IsHaltedAt
    (hm: HamkinsMachine)
    (input: Nat2)
    (n: Ordinal)
  :
    Prop
  :=
    (hm.stage input n).state = hm.haltState

  -- Halting is preserved by taking one more step.
  def stage.haltPreservedSucc
    {hm: HamkinsMachine}
    {input: Nat2}
    {n: Ordinal}
    (h: stage.IsHaltedAt hm input n)
  :
    stage.IsHaltedAt hm input (Order.succ n)
  := by
    show (hm.stage input (Order.succ n)).state = hm.haltState
    rw [hm.stage_succ, hm.haltStepIsId _ h]
    exact h

  -- Once halted, always halted.
  def stage.isHaltedAtGe
    {hm: HamkinsMachine}
    {input: Nat2}
    {n: Ordinal}
    (hAt: stage.IsHaltedAt hm input n)
  :
    ∀ ng: Ordinal, n ≤ ng → stage.IsHaltedAt hm input ng
  := by
    intro ng
    induction ng using Ordinal.limitRecOn with
    | zero =>
      intro le
      have hz: n = 0 := nonpos_iff_eq_zero.mp le
      exact hz ▸ hAt
    | succ o ih =>
      intro le
      rcases le.lt_or_eq with hlt | heq
      · exact stage.haltPreservedSucc (ih (Order.lt_succ_iff.mp hlt))
      · exact heq ▸ hAt
    | limit o hlim ih =>
      intro le
      rcases le.lt_or_eq with hlt | heq
      · show (hm.stage input o).state = hm.haltState
        rw [hm.stage_limit input hlim]
        exact if_pos ⟨⟨n, hlt⟩, hAt⟩
      · exact heq ▸ hAt

  structure stage.IsHaltedAtWith
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal)
  :
    Prop
  where
    isHaltedAt: stage.IsHaltedAt hm input n
    tapeEq: (hm.stage input n).tape = output

  -- Halting outputs are stable under one step.
  def stage.haltsConsistent.step
    {hm: HamkinsMachine}
    {input output0 output1: Nat2}
    {n: Ordinal}
    (hw0: stage.IsHaltedAtWith hm input output0 n)
    (hw1: stage.IsHaltedAtWith hm input output1 (Order.succ n))
  :
    output0 = output1
  := by
    have stepEq: hm.stage input (Order.succ n) = hm.stage input n := by
      rw [hm.stage_succ, hm.haltStepIsId _ hw0.isHaltedAt]
    rw [← hw0.tapeEq, ← hw1.tapeEq, stepEq]

  /-
    The output of a halted computation does not depend on the (large
    enough) stage at which we read it off.
  -/
  def stage.haltsConsistent.le
    {hm: HamkinsMachine}
    {input output0: Nat2}
    {n0: Ordinal}
    (hw0: stage.IsHaltedAtWith hm input output0 n0)
  :
    ∀ (n1: Ordinal) (output1: Nat2),
      stage.IsHaltedAtWith hm input output1 n1 → n0 ≤ n1 → output0 = output1
  := by
    intro n1
    induction n1 using Ordinal.limitRecOn with
    | zero =>
      intro output1 hw1 le
      have hz: n0 = 0 := nonpos_iff_eq_zero.mp le
      subst hz
      rw [← hw0.tapeEq, ← hw1.tapeEq]
    | succ o ih =>
      intro output1 hw1 le
      rcases le.lt_or_eq with hlt | heq
      · have leO: n0 ≤ o := Order.lt_succ_iff.mp hlt
        have hAtO: stage.IsHaltedAt hm input o :=
          stage.isHaltedAtGe hw0.isHaltedAt o leO
        have hwO: stage.IsHaltedAtWith hm input (hm.stage input o).tape o :=
          ⟨hAtO, rfl⟩
        exact (ih _ hwO leO).trans (stage.haltsConsistent.step hwO hw1)
      · subst heq
        rw [← hw0.tapeEq, ← hw1.tapeEq]
    | limit o hlim ih =>
      intro output1 hw1 le
      rcases le.lt_or_eq with hlt | heq
      · have tapeEq:
          (hm.stage input o).tape = Tuple.Nat2.limSup (hm.stagesUpTo input o)
        := by rw [hm.stage_limit input hlim]
        have limEq:
          Tuple.Nat2.limSup (hm.stagesUpTo input o) = output0
        := by
          apply Tuple.Nat2.limSup.eqOfEventuallyConstant _ _ n0 hlt
          intro i le'
          have hAtI: stage.IsHaltedAt hm input i.val :=
            stage.isHaltedAtGe hw0.isHaltedAt i.val le'
          have hwI:
            stage.IsHaltedAtWith hm input (hm.stage input i.val).tape i.val
          := ⟨hAtI, rfl⟩
          exact (ih i.val i.property _ hwI le').symm
        rw [← hw1.tapeEq, tapeEq, limEq]
      · subst heq
        rw [← hw0.tapeEq, ← hw1.tapeEq]

  def stage.haltsConsistent
    {hm: HamkinsMachine}
    {input output0 output1: Nat2}
    {n0 n1: Ordinal.{u}}
    (hw0: stage.IsHaltedAtWith hm input output0 n0)
    (hw1: stage.IsHaltedAtWith hm input output1 n1)
  :
    output0 = output1
  :=
    (le_total n0 n1).elim
      (fun le => stage.haltsConsistent.le hw0 n1 output1 hw1 le)
      (fun ge => (stage.haltsConsistent.le hw1 n0 output0 hw0 ge).symm)

  /-
    `hm` computes `output` from `input` if it halts with `output` on
    the tape at some transfinite stage.
  -/
  def Computes
    (hm: HamkinsMachine)
    (input output: Nat2)
  :
    Prop
  :=
    ∃ n: Ordinal.{u}, stage.IsHaltedAtWith hm input output n

  -- The partial function computed by `hm`.
  noncomputable def eval
    (hm: HamkinsMachine)
    (input: Nat2)
  :
    Option Nat2
  :=
    if h: ∃ output, Computes.{u} hm input output then
      some h.choose
    else
      Option.none

  theorem eval_of_isHaltedAtWith
    (hm: HamkinsMachine)
    (input output: Nat2)
    (n: Ordinal.{u})
    (hw: stage.IsHaltedAtWith hm input output n)
  :
    HamkinsMachine.eval.{u} hm input = some output
  := by
    have ex: ∃ output, Computes hm input output := ⟨output, n, hw⟩
    obtain ⟨n', hw'⟩ := ex.choose_spec
    exact (dif_pos ex).trans (congrArg some (stage.haltsConsistent hw' hw))

  def Halts (hm: HamkinsMachine) (input: Nat2): Prop :=
    ∃ n: Ordinal.{u}, stage.IsHaltedAt hm input n

  def Loops (hm: HamkinsMachine) (input: Nat2): Prop :=
    HamkinsMachine.eval.{u} hm input = Option.none

  def IsComputable (fn: Nat2 → Option Nat2): Prop :=
    ∃ hm: HamkinsMachine, ∀ input: Nat2, fn input = HamkinsMachine.eval.{u} hm input

  -- The machine that immediately halts, leaving the tape untouched.
  def trivialMachine: HamkinsMachine := {
    State := Unit
    isFinite := inferInstance
    initialState := ()
    haltState := ()
    limitState := ()
    getMove := fun state symbol => {
      nextState := state
      nextSymbol := symbol
      dir := Dir.none
    }
    haltHalts := fun _ => rfl
  }
end HamkinsMachine
