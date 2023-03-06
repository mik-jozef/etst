/-
  Defines sets and related stuff. And kinda whatever.
-/

import PartialOrder

open Classical


inductive Null | null

noncomputable def choiceEx {P: T → Prop} (ex: ∃ t: T, P t): { t: T // P t } :=
  let nonempty: Nonempty { t: T // P t } :=
    match ex with
    | ⟨t, prop⟩ => ⟨t, prop⟩
  choice nonempty

def contra (impl: a → b): ¬b → ¬a :=
  fun nbProof => fun aProof => nbProof (impl aProof)


def Set.{u} (T : Type u) := T → Prop

instance: Membership T (Set T) where
  mem := fun (t: T) (s: Set T) => s t

instance: Coe (Set T) Type where
  coe s := { t: T // t ∈ s }

instance: LE (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

infix:50 " ⊆ " => LE.le


theorem Set.ext {a b : Set D} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


instance: PartialOrder (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  refl (_: Set D) := fun _: D => id
  
  antisymm (a b: Set D) :=
    fun (ab: a ≤ b) (ba: ∀ d: D, d ∈ b → d ∈ a) =>
      let abElem: ∀ d: D, d ∈ a ↔ d ∈ b := fun (s: D) => Iff.intro (ab s) (ba s);
      Set.ext abElem
  
  trans (a b c: Set D) := fun (ab: a ≤ b) (bc: b ≤ c) =>
    -- In general, do I prefer long and incremental and explicit proofs,
    -- or terse and unreadable monsters? I think I prefer the former.
    --
    -- fun (d: D) =>
    --   let abi: d ∈ a → d ∈ b := ab s
    --   let bci: d ∈ b → d ∈ c := bc s
    --   fun (sa: d ∈ a) => bci (abi sa)
    fun (d: D) (sa: d ∈ a) => (bc d) ((ab d) sa)
  
  ltToLeNeq := id
  leNeqToLt := id

namespace Set
  def empty {D: Type}: Set D := fun _ => False  
  def full  {D: Type}: Set D := fun _ => True
  def just  {D: Type} (d: D): Set D := fun x => x = d
  
  def isFinite (s: Set D): Prop := ∃ l: List D, ∀ t: D, t ∈ s → t ∈ l
  
  def isSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  def union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d
  
  theorem union.isWider
    (family: Index → Set D)
    (i: Index)
  :
    (family i) ⊆ (union family)
  :=
    fun (d: D) (dfi: d ∈ family i) => ⟨i, dfi⟩
  
  def binaryUnion (a b: Set D): Set D := fun d: D => a d ∨ b d
  def binaryIntersection (a b: Set D): Set D := fun d: D => a d ∧ b d
  def complement (a: Set D): Set D := fun d: D => ¬ a d
end Set

infix:60 " ∪ " => Set.binaryUnion
infix:60 " ∩ " => Set.binaryIntersection
prefix:100 "~ " => Set.complement

instance: Coe Nat Type where
  coe := fun n => { nn: Nat // nn < n }


-- Some things that (imho) should be a part of the standard library:

def Nat.lt.addNatRite (ab: a < b) (k: Nat): a < b + k :=
  match k with
  | 0 => ab
  | Nat.succ x =>
      let gtZero: 0 < Nat.succ x := Nat.succ_pos _
      Nat.lt_trans ab (Nat.add_lt_add_left gtZero b)

def Nat.lt.addNatLeft (ab: a < b) (k: Nat): a < k + b :=
  match k with
  | 0 => (Nat.zero_add _) ▸ ab
  | Nat.succ x =>
      let gtZero: 0 < Nat.succ x := Nat.succ_pos _
      let lt := by conv =>
        lhs rw [(Nat.zero_add b).symm] exact (Nat.add_lt_add_right gtZero b)
      Nat.lt_trans ab lt

def Nat.lt.addNat (ab: a < b) (left rite: Nat): a < left + b + rite :=
  Nat.lt.addNatRite (Nat.lt.addNatLeft ab left) rite

def Nat.lt.zero.ifNotZero {n: Nat} (nNotZero: n ≠ 0): 0 < n :=
  match n with
  | 0 => False.elim (nNotZero rfl)
  | Nat.succ n => Nat.succ_pos n

def Nat.letTrans {a b c: Nat} (ab: a ≤ b) (bc: b < c): a < c :=
  (Nat.eq_or_lt_of_le ab).elim
    (fun eq => eq ▸ bc)
    (fun lt => Nat.lt_trans lt bc)

def Nat.lteTrans {a b c: Nat} (ab: a < b) (bc: b ≤ c): a < c :=
  (Nat.eq_or_lt_of_le bc).elim
    (fun eq => eq ▸ ab)
    (fun lt => Nat.lt_trans ab lt)

def Nat.isTotalLt (a b: Nat): a < b ∨ b < a ∨ a = b :=
  (Nat.le_total a b).elim
    (fun ab =>
      (Nat.eq_or_lt_of_le ab).elim
        (fun eq => Or.inr (Or.inr eq))
        (fun ab => Or.inl ab))
    (fun ba =>
      (Nat.eq_or_lt_of_le ba).elim
        (fun eq => Or.inr (Or.inr eq.symm))
        (fun ba => Or.inr (Or.inl ba)))

def Nat.ltAntisymm {p: Prop} {a b: Nat} (ab: a < b) (ba: b < a): p :=
  False.elim (Nat.lt_irrefl a (Nat.lt_trans ab ba))


def List.has (list: List T) (t: T): Prop :=
  ∃ n: Fin list.length, list.get n = t

def List.hasAll (list: List T): Prop :=
  ∀ t: T, list.has t

def Type.isFinite (T: Type): Prop :=
  ∃ list: List T, list.hasAll

def Type.IsFinite := { T: Type // Type.isFinite T }

def List.has.toMem (lh: List.has list t): t ∈ list :=
  let tIndex := choiceEx lh
  
  match tIndex, hL: list with
  | ⟨⟨Nat.zero, fin⟩, tIn⟩, [] =>
      let finL: 0 < length [] := hL ▸ fin
      False.elim (Nat.not_lt_zero _ finL)
  | ⟨⟨Nat.zero, fin⟩, tIn⟩, a::la =>
      let tInAla: (a::la).get ⟨0, hL ▸ fin⟩ = t := hL ▸ tIn
      let taEq: t = a := tInAla.symm
      taEq ▸ Mem.head t la
  | ⟨⟨Nat.succ n, fin⟩, tIn⟩, [] =>
      let finL: Nat.succ n < length [] := hL ▸ fin
      False.elim (Nat.not_lt_zero _ finL)
  | ⟨⟨Nat.succ n, fin⟩, tIn⟩, a::la =>
      let tInAla: (a::la).get ⟨Nat.succ n, hL ▸ fin⟩ = t := hL ▸ tIn
      let laHasT: la.has t := ⟨⟨n, _⟩, tInAla⟩
      let laHas := List.has.toMem laHasT
      Mem.tail a laHas

def List.has.fromMem (tIn: t ∈ list): List.has list t :=
  match tIn with
  | Mem.head _head rest => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | Mem.tail _head memRest =>
      let restHas := List.has.fromMem memRest
      let i := choiceEx restHas
      ⟨i.val.succ, i.property⟩
