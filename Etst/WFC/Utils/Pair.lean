module
public import Etst.WFC.Ch2_Interpretation
import Mathlib.Order.MinMax

public section
namespace Etst


namespace Pair
  protected theorem eq {l0 l1 r0 r1}:
    l0 = l1 → r0 = r1 → pair l0 r0 = pair l1 r1
  | rfl, rfl => rfl
  
  /-
    `Pair.null` encodes the number zero, while `Pair.pair n zero`
    encodes the successor of `n`.
  -/
  def IsNatEncoding: Pair → Prop
  | null => True
  | pair a b => (IsNatEncoding a) ∧ b = null
  
  def NatEncoding := { p // IsNatEncoding p }
  
  
  exposed def nat: Nat → Pair
  | .zero => Pair.null
  | .succ n => Pair.pair (nat n) null
  
  instance nat.inst: Coe Nat Pair := ⟨nat⟩
  
  def depth: Pair → Nat
  | null => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  
  /-
    `Pair.null` encodes the empty list, while
    
        Pair.pair head tailEncoding
    
    encodes the list
    
        [ head, ...tail ] \,,
    
    where `tail` is the list encoded by `tailEncoding`.
  -/
  exposed def listEncoding: List Pair → Pair
  | [] => .null
  | p :: ps => .pair p (listEncoding ps)
  
  
  theorem nat_inj_eq {n m}
    (eq: nat n = nat m)
  :
    n = m
  :=
    match n, m with
    | Nat.zero, Nat.zero => rfl
    | Nat.zero, Nat.succ _ => Pair.noConfusion eq
    | Nat.succ _, Nat.zero => Pair.noConfusion eq
    | Nat.succ _nPred, Nat.succ _mPred =>
      let eqFromPred :=
        Pair.noConfusion eq fun predEq _ => predEq
      congrArg Nat.succ (nat_inj_eq eqFromPred)
  
  theorem nat_inj_neq {n m}:
    n ≠ m → nat n ≠ nat m
  :=
    not_imp_not.mpr nat_inj_eq
  
  
  theorem depth_cases_eq (a b: Pair):
    Or
      (And
        ((pair a b).depth = Nat.succ a.depth)
        (b.depth ≤ a.depth))
      (And
        ((pair a b).depth = Nat.succ b.depth)
        (a.depth < b.depth))
  :=
    (max_cases a.depth b.depth).elim
      (fun ⟨eq, le⟩ => Or.inl (And.intro (congr rfl eq) le))
      (fun ⟨eq, lt⟩ => Or.inr (And.intro (congr rfl eq) lt))
  
  theorem depth_null_left (a: Pair):
    depth (pair null a) = a.depth.succ
  :=
    Nat.succ_inj.mpr (Nat.zero_max a.depth)
  
  theorem depth_null_rite (a: Pair):
    depth (pair a null) = a.depth.succ
  :=
    Nat.succ_inj.mpr (Nat.max_zero a.depth)
  
  theorem nat_depth_eq: (n: Nat) → (Pair.nat n).depth = n
  | Nat.zero => rfl
  | Nat.succ pred =>
    (depth_cases_eq (nat pred) null).elim
      (fun ⟨eq, _⟩ =>
        eq ▸ congr rfl (nat_depth_eq pred))
      (fun ⟨_, ltZero⟩ =>
        False.elim (Nat.not_lt_zero _ ltZero))
  
  
  def pairS3
    (s0 s1: Set3 Pair)
  :
    Set3 Pair
  := {
    defMem := { p | ∃ p0 ∈ s0.defMem, ∃ p1 ∈ s1.defMem, p = Pair.pair p0 p1 },
    posMem := { p | ∃ p0 ∈ s0.posMem, ∃ p1 ∈ s1.posMem, p = Pair.pair p0 p1 },
    defLePos := fun _ ⟨p0, p0InDef, ⟨p1, p1InDef, pEq⟩⟩ =>
      ⟨p0, s0.defLePos p0InDef, p1, s1.defLePos p1InDef, pEq⟩
  }
  
  
  exposed def toExpr: Pair → BasicExpr
  | .null => .null
  | .pair l r => .prod l.toExpr r.toExpr
  
end Pair


/-
  `fn.call arg` is the triset of pairs `b` such that
  `(arg, b)` is in `fn`.
  
  You can think of `fn` as a set of input-output pairs representing
  a function `f: Pair → Set3 Pair`.
-/
exposed def Set3.call
  (fn: Set3 Pair)
  (arg: Pair)
:
  Set3 Pair
:= {
  defMem := { p | .pair arg p ∈ fn.defMem }
  posMem := { p | .pair arg p ∈ fn.posMem }
  defLePos _ := defToPos
}

exposed def Set3.flatCall (fn args: Set3 Pair): Set3 Pair := {
  defMem := { p | ∃ arg, arg ∈ args.defMem ∧ p ∈ (fn.call arg).defMem },
  posMem := { p | ∃ arg, arg ∈ args.posMem ∧ p ∈ (fn.call arg).posMem },
  defLePos _ :=
    fun ⟨arg, hp, hq⟩ => ⟨arg, defToPos hp, defToPos hq⟩
}

exposed def Set3.PairMem
  (s e: Set3 Pair)
:
  Prop
:=
  ∃ i: Pair, s.call i = e

instance Set3.pairInstMem:
  Membership (Set3 Pair) (Set3 Pair)
:=
  ⟨Set3.PairMem⟩


theorem Set3.inCall {s lane arg res}
  (inS: .pair arg res ∈ s.getLane lane)
:
  res ∈ (call s arg).getLane lane
:=
  match lane with
  | .defLane => inS
  | .posLane => inS

theorem Set3.inCallElim {s lane arg res}
  (inCall: res ∈ (call s arg).getLane lane)
:
  .pair arg res ∈ s.getLane lane
:=
  match lane with
  | .defLane => inCall
  | .posLane => inCall


theorem Set3.inFlatCall {fn args lane arg res}
  (inArg: arg ∈ args.getLane lane)
  (inFn: .pair arg res ∈ fn.getLane lane)
:
  res ∈ (flatCall fn args).getLane lane
:=
  match lane with
  | .defLane => ⟨arg, inArg, inFn⟩
  | .posLane => ⟨arg, inArg, inFn⟩

theorem Set3.inFlatCallElim {fn args lane res}
  (inFlat: res ∈ (flatCall fn args).getLane lane)
:
  ∃ arg, arg ∈ args.getLane lane ∧ .pair arg res ∈ fn.getLane lane
:=
  match lane with
  | .defLane => inFlat
  | .posLane => inFlat

theorem Set3.flatCall_just (fn: Set3 Pair) (p: Pair):
  flatCall fn (just p) = fn.call p
:=
  Set3.eq4
    (fun _ ⟨_, eq, inFn⟩ => eq ▸ inFn)
    (fun _ inFn => ⟨p, rfl, inFn⟩)
    (fun _ ⟨_, eq, inFn⟩ => eq ▸ inFn)
    (fun _ inFn => ⟨p, rfl, inFn⟩)
