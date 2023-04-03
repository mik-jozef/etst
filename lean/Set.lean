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

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)


def Set.{u} (T : Type u) := T → Prop

instance: Membership T (Set T) where
  mem := fun (t: T) (s: Set T) => s t

instance: Coe (Set T) Type where
  coe s := { t: T // t ∈ s }

instance: LE (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

infix:50 " ⊆ " => LE.le


theorem Set.eq {a b : Set D} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


instance Set.ord: PartialOrder (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  refl (_: Set D) := fun _: D => id
  
  antisymm (a b: Set D) :=
    fun (ab: a ≤ b) (ba: ∀ d: D, d ∈ b → d ∈ a) =>
      let abElem: ∀ d: D, d ∈ a ↔ d ∈ b := fun (s: D) => Iff.intro (ab s) (ba s);
      Set.eq abElem
  
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


-- Some things that (imho) should be a part of the standard library.
-- (or are they?).

theorem Or.symm {a b: Prop} (aob: a ∨ b): b ∨ a :=
  aob.elim (fun a => Or.inr a) (fun b => Or.inl b)

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

def Nat.le.zero: (n: Nat) → 0 ≤ n
  | Nat.zero => Nat.le.refl
  | Nat.succ n => Nat.le_of_lt (Nat.succ_pos n)

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

def Nat.ltLeAntisymm {p: Prop} {a b: Nat} (ab: a < b) (ba: b ≤ a): p :=
  (Nat.eq_or_lt_of_le ba).elim
    (fun eq => False.elim (Nat.lt_irrefl a (eq ▸ ab)))
    (fun ba => Nat.ltAntisymm ab ba)

def Nat.leLtAntisymm {p: Prop} {a b: Nat} (ab: a ≤ b) (ba: b < a): p :=
  (Nat.eq_or_lt_of_le ab).elim
    (fun eq => False.elim (Nat.lt_irrefl a (eq ▸ ba)))
    (fun ab => Nat.ltAntisymm ab ba)


def Nat.isTotal (a b: Nat): a < b ∨ b < a ∨ a = b :=
  (Nat.lt_or_ge a b).elim
    (fun lt => Or.inl lt)
    (fun ge => Or.inr
      ((Nat.eq_or_lt_of_le ge).symm.elim
        (fun x => Or.inl x)
        (fun x => Or.inr x.symm)))


def Nat.abs (a b: Nat) := Nat.max (a - b) (b - a)

def Nat.abs.same (a: Nat): Nat.abs a a = 0 :=
  let aa: a - a = 0 := Nat.sub_self a
  (if_pos (aa ▸ Nat.le.zero _)).trans aa

def Nat.abs.eq.ltAB {a b: Nat} (ab: a < b): Nat.abs a b = b - a :=
  let eqZero: a - b = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt ab)
  if_pos (eqZero ▸ Nat.le.zero _)

def Nat.abs.eq.ltBA {a b: Nat} (ba: b < a): Nat.abs a b = a - b :=
  let eqZero: b - a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt ba)
  
  if h: a - b = 0 then
    (if_pos (h ▸ eqZero ▸ Nat.le.refl)).trans (eqZero.trans h.symm)
  else
    if_neg (eqZero ▸ (fun le => h (Nat.eq_zero_of_le_zero le)))

def Nat.abs.eq.leAB {a b: Nat} (ab: a ≤ b): Nat.abs a b = b - a :=
  (Nat.eq_or_lt_of_le ab).elim
    (fun eq => eq ▸ (Nat.abs.same a).trans (Nat.sub_self a).symm)
    (fun lt => Nat.abs.eq.ltAB lt)

def Nat.abs.eq.leBA {a b: Nat} (ba: b ≤ a): Nat.abs a b = a - b :=
  (Nat.eq_or_lt_of_le ba).elim
    (fun eq => eq ▸ (Nat.abs.same a).trans (Nat.sub_self a).symm)
    (fun lt => Nat.abs.eq.ltBA lt)

def Nat.abs.symm (a b: Nat): Nat.abs a b = Nat.abs b a :=
  (a.isTotal b).elim
    (fun lt => (Nat.abs.eq.ltAB lt).trans (Nat.abs.eq.ltBA lt).symm)
      (fun gtOrEq => gtOrEq.elim
        (fun gt => (Nat.abs.eq.ltBA gt).trans (Nat.abs.eq.ltAB gt).symm)
        (fun eq => eq ▸ rfl))


def Nat.ltle.subLt {a b c: Nat} (ab: a < b) (bc: b ≤ c): c - b < c - a :=
  let eqBB: c - b + b = c := Nat.sub_add_cancel bc
  let ltC: c - b + a < c :=
    by conv => rhs rw [eqBB.symm] exact Nat.add_lt_add_left ab (c - b)
  Nat.lt_sub_of_add_lt ltC

def Nat.lelt.ltSub {a b c: Nat} (ab: a ≤ b) (bc: b < c): b - a < c - a :=
  let bSubAdd: b - a + a = b := Nat.sub_add_cancel ab
  Nat.lt_sub_of_add_lt (bSubAdd.symm ▸ bc)

def Nat.abs.lelt.left {a b c: Nat} (ab: a ≤ b) (bc: b < c):
  Nat.abs a b < Nat.abs a c
:=
  let absBC: Nat.abs a b = b - a := Nat.abs.eq.leAB ab
  let absAC: Nat.abs a c = c - a := Nat.abs.eq.ltAB (Nat.letTrans ab bc)
  
  let lt: b - a < c - a := Nat.lelt.ltSub ab bc
  absBC ▸ absAC ▸ lt

def Nat.abs.ltle.rite {a b c: Nat} (ab: a < b) (bc: b ≤ c):
  Nat.abs b c < Nat.abs a c
:=
  let absBC: Nat.abs b c = c - b := Nat.abs.eq.leAB bc
  let absAC: Nat.abs a c = c - a := Nat.abs.eq.ltAB (Nat.lteTrans ab bc)
  
  let lt: c - b < c - a := Nat.ltle.subLt ab bc
  absBC ▸ absAC ▸ lt

def Nat.le_pred_of_lt {a b: Nat} (ab: a < b): a ≤ b.pred :=
  match b with
  | Nat.zero => Nat.le_of_lt ab -- No appeal to contradiction. Crazy!
  | Nat.succ _ => Nat.le_of_succ_le_succ ab


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

def Iff.not (iff: a ↔ b): ¬a ↔ ¬b :=
  Iff.intro
    (contra iff.mpr)
    (contra iff.mp)

noncomputable def Or.Elim
  (or: a ∨ b)
  (ifA: a → Ret)
  (ifB: b → Ret)
:
  Ret
:=
  if h: a then
    ifA h
  else
    ifB (or.elim (fun isA => False.elim (h isA)) id)

def notEx.all {p npi: T → Prop}
  (na: ¬(∃ t: T, p t))
  (nptImpl: ∀ t, ¬p t → npi t)
:
  ∀ t: T, npi t
:=
  fun t =>  nptImpl t (byContradiction fun nnpt => na ⟨t, dne nnpt⟩)

def notAll.ex {p npi: T → Prop}
  (na: ¬(∀ t: T, p t))
  (nptImpl: ∀ t, ¬p t → npi t)
:
  ∃ t: T, npi t
:=
  byContradiction fun nex =>
    na (fun t => byContradiction fun npt => nex ⟨t, nptImpl t npt⟩)

def all.notEx {p pi: T → Prop}
  (allP: ∀ t: T, p t)
  (ptImpl: ∀ t, p t → ¬pi t)
:
  ¬∃ t: T, pi t
:=
  fun ex =>
    let t := choiceEx ex
    ptImpl t (allP t) t.property

def ex.notAll {p pi: T → Prop}
  (exP: ∃ t: T, p t)
  (ptImpl: ∀ t, p t → ¬pi t)
:
  ¬∀ t: T, pi t
:=
  fun all =>
    let t := choiceEx exP
    ptImpl t t.property (all t)
