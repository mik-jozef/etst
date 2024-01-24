/-
  Defines sets and related stuff. And kinda whatever.
-/

import PartialOrder
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic

-- Mathlib.Data.Set.Basic exports 'em', so cannot `open Classical`. Fck this.
def byContradiction {P: Prop} := @Classical.byContradiction P
noncomputable instance propDecidable (P: Prop): Decidable P :=
  Classical.propDecidable P


inductive Null | null

noncomputable def Exists.unwrap
  {P: T → Prop}
  (ex: ∃ t: T, P t)
:
  { t: T // P t }
:=
  let nonempty: Nonempty { t: T // P t } :=
    match ex with
    | ⟨t, prop⟩ => ⟨t, prop⟩
  Classical.choice nonempty

def Function.contra (ab: A → B): ¬B → ¬A :=
  fun nb => fun a => nb (ab a)

theorem Not.dne {P: Prop} (h: ¬¬P): P :=
  Or.elim (em P)
    (fun p: P => p)
    (fun np: ¬P => absurd np h)


instance Set.ord: PartialOrder (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

  le_refl (_: Set D) := fun _: D => id

  le_antisymm (a b: Set D) :=
    fun (ab: a ≤ b) (ba: ∀ d: D, d ∈ b → d ∈ a) =>
      let abElem: ∀ d: D, d ∈ a ↔ d ∈ b :=
        fun (s: D) => Iff.intro (@ab s) (@ba s);
      Set.ext abElem

  le_trans (a b c: Set D) := fun (ab: a ≤ b) (bc: b ≤ c) =>
    fun (d: D) (da: d ∈ a) => (@bc d) ((@ab d) da)

namespace Set
  def empty {D: Type}: Set D := fun _ => False
  def full  {D: Type}: Set D := fun _ => True
  def just  {D: Type} (d: D): Set D := fun x => x = d

  def isFinite (s: Set D): Prop := ∃ l: List D, ∀ t: D, t ∈ s → t ∈ l

  def isSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

  def indexUnion {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d

  theorem indexUnion.isWider
    (family: Index → Set D)
    (i: Index)
  :
    (family i) ⊆ (indexUnion family)
  :=
    fun (d: D) (dfi: d ∈ family i) => ⟨i, dfi⟩
end Set

instance: Coe Nat Type where
  coe := fun n => { nn: Nat // nn < n }


-- Some things that (imho) should be a part of the standard library.
-- (or are they?).
-- Meh. I suppose I should look and replace, but ¯\_(ツ)_/¯
-- Note: If you wanna outdo Lean (pipe dreams hello!), efficient
-- search of already proven things could be a killer feature.

def Eq.transLe
  {_ord: PartialOrder T}
  {a b c: T}
  (ab: a = b)
  (bc: b ≤ c)
:
  a ≤ c
:=
  ab ▸ bc

def Nat.lt.addNatRite (ab: a < b) (k: Nat): a < b + k :=
  Nat.lt_add_right _ _ _ ab

def Nat.lt.addNatLeft (ab: a < b) (k: Nat): a < k + b :=
  (Nat.add_comm b k) ▸ (Nat.lt_add_right _ _ k ab)

def Nat.lt.addNat (ab: a < b) (left rite: Nat): a < left + b + rite :=
  Nat.lt.addNatRite (Nat.lt.addNatLeft ab left) rite

def Nat.lt.zero.ifNotZero {n: Nat} (nNotZero: n ≠ 0): 0 < n :=
  zero_lt_of_ne_zero nNotZero

def Nat.le.zero (n: Nat): 0 ≤ n := zero_le n

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
  let ltBB: c - b + a < c - b + b := Nat.add_lt_add_left ab (c - b)
  let ltCEq: (c - b + a < c) = (c - b + a < c - b + b) :=
    by conv =>
      rhs
      rw [eqBB]
      rfl
  let ltC: c - b + a < c := ltCEq ▸ ltBB
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


def List.Has (list: List T) (t: T): Prop :=
  ∃ n: Fin list.length, list.get n = t

def List.HasAll (list: List T): Prop :=
  ∀ t: T, list.Has t

def Type.IsFinite (T: Type u): Prop :=
  ∃ list: List T, list.HasAll

def Type.Finite := { T: Type // Type.IsFinite T }

def List.Has.toMem (lh: List.Has list t): t ∈ list :=
  let tIndex := lh.unwrap

  match tIndex, hL: list with
  | ⟨⟨Nat.zero, fin⟩, tIn⟩, [] =>
      let finL: 0 < length [] := hL ▸ fin
      False.elim (Nat.not_lt_zero _ finL)
  | ⟨⟨Nat.zero, fin⟩, tIn⟩, a::la =>
      let tInAla: (a::la).get ⟨0, hL ▸ fin⟩ = t := hL ▸ tIn
      let taEq: t = a := tInAla.symm
      taEq ▸ Mem.head la
  | ⟨⟨Nat.succ n, fin⟩, tIn⟩, [] =>
      let finL: Nat.succ n < length [] := hL ▸ fin
      False.elim (Nat.not_lt_zero _ finL)
  | ⟨⟨Nat.succ n, fin⟩, tIn⟩, a::la =>
      let tInAla: (a::la).get ⟨Nat.succ n, hL ▸ fin⟩ = t := hL ▸ tIn
      let laHasT: la.Has t := ⟨⟨n, _⟩, tInAla⟩
      let laHas := List.Has.toMem laHasT
      Mem.tail a laHas

def List.has.fromMem (tIn: t ∈ list): List.Has list t :=
  match tIn with
  | Mem.head rest => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | Mem.tail _head memRest =>
      let restHas := List.has.fromMem memRest
      let i := restHas.unwrap
      ⟨i.val.succ, i.property⟩


def Option.neqConfusion (neq: a ≠ b): some a ≠ some b :=
  fun eqSome => neq (Option.noConfusion eqSome id)


def Not.toAll {P ImpliedByNotP: T → Prop}
  (nEx: ¬(∃ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∀ t: T, ImpliedByNotP t
:=
  fun t =>  nptImpl t (byContradiction fun nnpt => nEx ⟨t, nnpt.dne⟩)

def Not.toEx {P ImpliedByNotP: T → Prop}
  (nAll: ¬(∀ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∃ t: T, ImpliedByNotP t
:=
  byContradiction fun nEx =>
    nAll (fun t => byContradiction fun npt => nEx ⟨t, nptImpl t npt⟩)

def all.notEx {P ContradictsP: T → Prop}
  (allP: ∀ t: T, P t)
  (ptImpl: ∀ t, P t → ¬ContradictsP t)
:
  ¬∃ t: T, ContradictsP t
:=
  fun ex =>
    let t := ex.unwrap
    ptImpl t (allP t) t.property

def ex.notAll {P ContradictsP: T → Prop}
  (exP: ∃ t: T, P t)
  (ptImpl: ∀ t, P t → ¬ContradictsP t)
:
  ¬∀ t: T, ContradictsP t
:=
  fun all =>
    let t := exP.unwrap
    ptImpl t t.property (all t)

def Not.implToAnd {A B: Prop} (ab: ¬(A → B)): A ∧ ¬B :=
  if hA: A then
    And.intro hA (if hB: B then False.elim (ab fun _ => hB) else hB)
  else
    False.elim (ab ((fun a => False.elim (hA a))))


noncomputable def existsDistinctOfNotInjective
  {f: A → B}
  (nInj: ¬f.Injective)
:
  { p: A × A // f p.fst = f p.snd ∧ p.fst ≠ p.snd }
:=
  let ex :=
    nInj.toEx fun _a0 a0In =>
      a0In.toEx fun _a1 a1In =>
        a1In.implToAnd

  let a0 := ex.unwrap
  let a1 := a0.property.unwrap

  ⟨⟨a0, a1⟩, a1.property⟩
