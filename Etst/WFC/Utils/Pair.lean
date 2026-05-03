import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace Pair
  protected def eq {l0 l1 r0 r1}:
    l0 = l1 → r0 = r1 → pair l0 r0 = pair l1 r1
  | rfl, rfl => rfl
  
  /-
    `Pair.null` encodes the number zero, while `Pair.pair n zero`
    encodes the successor of `n`.
  -/
  def IsNatEncoding: Set Pair
  | null => True
  | pair a b => (IsNatEncoding a) ∧ b = null
  
  def NatEncoding := { p // IsNatEncoding p }
  
  
  def nat: Nat → Pair
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
  def listEncoding: List Pair → Pair
  | [] => .null
  | p :: ps => .pair p (listEncoding ps)
  
  
  def nat_inj_eq {n m}
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
  
  def nat_inj_neq {n m}:
    n ≠ m → nat n ≠ nat m
  :=
    not_imp_not.mpr nat_inj_eq
  
  
  def depth_cases_eq (a b: Pair):
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
  
  def depth_null_left (a: Pair):
    depth (pair null a) = a.depth.succ
  :=
    Nat.succ_inj.mpr (Nat.zero_max a.depth)
  
  def depth_null_rite (a: Pair):
    depth (pair a null) = a.depth.succ
  :=
    Nat.succ_inj.mpr (Nat.max_zero a.depth)
  
  def nat_depth_eq: (n: Nat) → (Pair.nat n).depth = n
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
  
  
  def toExpr: Pair → BasicExpr
  | .null => .null
  | .pair l r => .pair l.toExpr r.toExpr
  
end Pair


/-
  `fn.call arg` is the triset of pairs `b` such that
  `(arg, b)` is in `fn`.
  
  You can think of `fn` as a set of input-output pairs representing
  a function `f: Pair → Set3 Pair`.
-/
def Set3.call
  (fn: Set3 Pair)
  (arg: Pair)
:
  Set3 Pair
:= {
  defMem p := fn.defMem (Pair.pair arg p)
  posMem p := fn.posMem (Pair.pair arg p)
  defLePos _ pInDef := pInDef.toPos
}

def Set3.PairMem
  (s e: Set3 Pair)
:
  Prop
:=
  ∃ i: Pair, s.call i = e

instance Set3.pairInstMem:
  Membership (Set3 Pair) (Set3 Pair)
:=
  ⟨Set3.PairMem⟩


def Set3.inCall {s lane arg res}
  (inS: s.getLane lane (.pair arg res))
:
  (call s arg).getLane lane res
:=
  match lane with
  | .defLane => inS
  | .posLane => inS

def Set3.inCallElim {s lane arg res}
  (inCall: (call s arg).getLane lane res)
:
  s.getLane lane (.pair arg res)
:=
  match lane with
  | .defLane => inCall
  | .posLane => inCall
