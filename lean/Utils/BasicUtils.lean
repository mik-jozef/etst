/-
  Things so basic that they ought to be in Lean's standard
  library, and <del>perhaps</del> most likely even are and
  I just didn't find them.
  
  Also some things that seemed basic but turned out to be
  a bit more complicated. And some stuff that just kinda
  doesn't fit anywhere else.
-/

import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card

import Utils.PartialOrder


def byContradiction {P: Prop} := @Classical.byContradiction P
noncomputable instance propDecidable (P: Prop): Decidable P :=
  Classical.propDecidable P

inductive Null: Type* | null

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
  Or.elim (Classical.em P)
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

noncomputable def List.pfilter
  (list: List D)
  (pred: D → Prop)
:
  { l: List D // ∀ d, d ∈ l ↔ d ∈ list ∧ pred d }
:=
  let decideEq d:
    (decide (pred d) = true) = pred d
  :=
    by simp
  
  ⟨
    list.filter pred,
    fun d => decideEq d ▸ List.mem_filter
  ⟩

namespace Set
  def empty: Set D := fun _ => False
  def full: Set D := fun _ => True
  def just (d: D): Set D := fun x => x = d

  def HasListOfAll (s: Set D): Prop := ∃ l: List D, ∀ t: s, t.val ∈ l
  
  namespace HasListOfAll
    noncomputable def inIff
      {s: Set D}
      (hasList: s.HasListOfAll)
    :
      { l: List D // ∀ t, t ∈ s ↔ t ∈ l }
    :=
      let ⟨l, allOfSIn⟩ := hasList.unwrap
      let ⟨lf, inIff⟩ := l.pfilter s
      
      ⟨
        lf,
        fun d =>
          Iff.intro
            (fun dInS =>
              (inIff d).mpr (And.intro (allOfSIn ⟨d, dInS⟩) dInS))
            (fun dInLf =>
              ((inIff d).mp dInLf).right),
      ⟩
    
    def toFinite
      {s: Set D}
      (hasList: s.HasListOfAll)
    :
      Finite s
    :=
      let ⟨list, inListIff⟩ := inIff hasList
      let typedList: List ↑s :=
        list.pmap
          (fun d h => ⟨d, h⟩)
          (fun e eIn => (inListIff e).mpr eIn)
      
      let inTypedList (e: ↑s): e ∈ typedList :=
        List.mem_pmap.mpr ⟨e, ⟨(inListIff e).mp e.property, rfl⟩⟩
      
      Fintype.finite (Fintype.ofList typedList inTypedList)
    
  end HasListOfAll

  def IsSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
end Set

instance: Coe Nat Type where
  coe := fun n => { nn: Nat // nn < n }


inductive IsComparable (rel: T → T → Prop) (a b: T): Prop
where
| IsLt: rel a b → IsComparable rel a b
| IsGt: rel b a → IsComparable rel a b
| IsEq: a = b → IsComparable rel a b

def IsConnected (rel: T → T → Prop): Prop :=
  ∀ a b: T, IsComparable rel a b

def LinearOrder.ltTotal
  (ord: LinearOrder T)
:
  IsConnected ord.lt
:=
  fun a b =>
    if h: a = b then
      IsComparable.IsEq h
    else
      (ord.le_total a b).elim
        (fun le => IsComparable.IsLt (le.lt_of_ne h))
        (fun ge => IsComparable.IsGt (ge.lt_of_ne (fun eq => h (eq.symm))))


def Nat.lt.addNatRite (ab: a < b) (k: Nat): a < b + k :=
  Nat.lt_add_right _ ab

def Nat.lt.addNatLeft (ab: a < b) (k: Nat): a < k + b :=
  (Nat.add_comm b k) ▸ (Nat.lt_add_right k ab)

def Nat.lt.addNat (ab: a < b) (left rite: Nat): a < left + b + rite :=
  Nat.lt.addNatRite (Nat.lt.addNatLeft ab left) rite

def Nat.letTrans {a b c: Nat} (ab: a ≤ b) (bc: b < c): a < c :=
  (Nat.eq_or_lt_of_le ab).elim
    (fun eq => eq ▸ bc)
    (fun lt => Nat.lt_trans lt bc)

def Nat.lteTrans {a b c: Nat} (ab: a < b) (bc: b ≤ c): a < c :=
  (Nat.eq_or_lt_of_le bc).elim
    (fun eq => eq ▸ ab)
    (fun lt => Nat.lt_trans ab lt)

def Nat.ltTotal: IsConnected Nat.lt :=
  LinearOrder.ltTotal Nat.instLinearOrder

def Nat.ltAntisymm {a b: Nat} (ab: a < b) (ba: b < a): P :=
  False.elim (Nat.lt_irrefl a (Nat.lt_trans ab ba))

def Nat.ltLeAntisymm {a b: Nat} (ab: a < b) (ba: b ≤ a): P :=
  (Nat.eq_or_lt_of_le ba).elim
    (fun eq => False.elim (Nat.lt_irrefl a (eq ▸ ab)))
    (fun ba => Nat.ltAntisymm ab ba)

def Nat.leLtAntisymm {a b: Nat} (ab: a ≤ b) (ba: b < a): P :=
  (Nat.eq_or_lt_of_le ab).elim
    (fun eq => False.elim (Nat.lt_irrefl a (eq ▸ ba)))
    (fun ab => Nat.ltAntisymm ab ba)


def Nat.abs (a b: Nat) := Nat.max (a - b) (b - a)

def Nat.abs.same (a: Nat): Nat.abs a a = 0 :=
  let aa: a - a = 0 := Nat.sub_self a
  (if_pos (aa ▸ zero_le _)).trans aa

def Nat.abs.eq.ltAB {a b: Nat} (ab: a < b): Nat.abs a b = b - a :=
  let eqZero: a - b = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt ab)
  if_pos (eqZero ▸ zero_le _)

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
  (a.ltTotal b).rec
    (fun lt => (Nat.abs.eq.ltAB lt).trans (Nat.abs.eq.ltBA lt).symm)
    (fun gt => (Nat.abs.eq.ltBA gt).trans (Nat.abs.eq.ltAB gt).symm)
    (fun eq => eq ▸ rfl)


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

def Nat.lt_left_of_add
  (eq: a + b = c)
  (lt: 0 < b)
:
  a < c
:=
  eq ▸ Nat.lt_add_of_pos_right lt

def Nat.eq_of_lt_of_le_succ
  {a b: Nat}
  (lt: a < b)
  (le: b ≤ a.succ)
:
  a.succ = b
:=
  (le_or_eq_of_le_succ le).elim
    (fun ba => Nat.leLtAntisymm ba lt)
    Eq.symm

def Nat.lt_of_lt_succ_of_ne
  {a b: Nat}
  (lt: a < b.succ)
  (neq: a ≠ b)
:
  a < b
:=
  (Nat.lt_or_eq_of_le (Nat.lt_succ.mp lt)).elim
    id
    (fun eq => (neq eq).elim)

def Nat.succ_sub_comm_of_lt
  {a b: Nat}
  (lt: a ≤ b)
:
  (b - a).succ = b.succ - a
:=
  match a, b, lt with
  | zero, zero, _ => rfl
  | zero, succ _bPred, _ => rfl
  | succ aPred, succ bPred, le =>
    let ih := Nat.succ_sub_comm_of_lt (Nat.le_of_succ_le_succ le)
    
    Nat.succ_sub_succ_eq_sub bPred aPred ▸
    Nat.succ_sub_succ_eq_sub bPred.succ aPred ▸
    ih


structure List.HasAll (list: List T): Prop where
  isIn: ∀ t: T, t ∈ list

def Type.IsFinite (T: Type u): Prop :=
  ∃ list: List T, list.HasAll

def Type.Finite := { T: Type // Type.IsFinite T }


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

def Not.toOr {L R: Prop}
  (nAnd: ¬(L ∧ R))
:
  ¬L ∨ ¬ R
:=
  if hL: L then
    if hR: R then
      False.elim (nAnd ⟨hL, hR⟩)
    else
      Or.inr hR
  else
    Or.inl hL

def Not.toAnd {L R: Prop}
  (nOr: ¬(L ∨ R))
:
  ¬L ∧ ¬ R
:=
  if hL: L then
    False.elim (nOr (Or.inl hL))
  else
    if hR: R then
      False.elim (nOr (Or.inr hR))
    else
      And.intro hL hR

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

def And.toNor (p: ¬L ∧ ¬R): ¬(L ∨ R) :=
  fun lr => lr.elim
    (fun l => p.left l)
    (fun r => p.right r)

def Or.toNand (p: ¬L ∨ ¬R): ¬(L ∧ R) :=
  fun lr => p.elim
    (fun nl => nl lr.left)
    (fun nr => nr lr.right)

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


def List.Mem.toOr
  {t head: T}
  (mem: List.Mem t (head::rest)) -- Cannot use "∈" bc.
:
  t = head ∨ t ∈ rest
:=
  match mem with
  | Mem.head a => Or.inl rfl
  | Mem.tail a b => Or.inr b

def List.Mem.elim
  {t head: T}
  (mem: List.Mem t (head::rest))
  (left: t = head → C)
  (rite: t ∈ rest → C)
:
  C
:=
  mem.toOr.elim left rite

def List.appendUnique [DecidableEq T] (list: List T) (t: T) :=
  if t ∈ list then
    list
  else
    list ++ [ t ]

def List.appendUnique.eqIfNotUnique
  [DecidableEq T]
  {list: List T}
  (tInList: t ∈ list)
:
  appendUnique list t = list
:=
  if_pos tInList

def List.appendUnique.eqIfUnique
  [DecidableEq T]
  {list: List T}
  (tInList: t ∉ list)
:
  appendUnique list t = list ++ [ t ]
:=
  if_neg tInList

def List.appendUnique.inToIn
  [DecidableEq T]
  (tToAppend: T)
  {list: List T}
  (tIn: tAlreadyIn ∈ list)
:
  tAlreadyIn ∈ appendUnique list tToAppend
:= by
  unfold appendUnique;
  exact
    if h: tToAppend ∈ list then
      if_pos h ▸ tIn
    else
      if_neg h ▸ (List.mem_append_left [ tToAppend ] tIn)

def List.appendUnique.eqToIn
  [DecidableEq T]
  (list: List T)
  (t: T)
:
  t ∈ appendUnique list t
:= by
  unfold appendUnique;
  exact
    if h: t ∈ list then
      if_pos h ▸ h
    else
      if_neg h ▸
        let tIn: t ∈ [ t ] := Mem.head []
        List.mem_append_right list tIn

def List.appendUnique.inToOrInEq
  [DecidableEq T]
  {list: List T}
  (isTIn: tIn ∈ appendUnique list t)
:
  tIn ∈ list ∨ tIn = t
:=
  if hIn: t ∈ list then
    Or.inl (eqIfNotUnique hIn ▸ isTIn)
  else
    let tInConcat: tIn ∈ list ++ [ t ] := eqIfUnique hIn ▸ isTIn
    let tInEq := mem_append_eq tIn list [ t ]
    let tInEither := tInEq ▸ tInConcat
    
    tInEither.elim
      (fun inList => Or.inl inList)
      (fun inArrOfT => Or.inr (eq_of_mem_singleton inArrOfT))
  

def List.concatUnique
  [DecidableEq T]
  (listL listR: List T)
:
  List T
:=
  match listR with
  | nil => listL
  | cons head tail =>
      concatUnique (appendUnique listL head) tail

def List.concatUnique.inLeftToIn
  [DecidableEq T]
  {listL: List T}
  (tInL: t ∈ listL)
  (listR: List T)
:
  t ∈ concatUnique listL listR
:=
  match listR with
  | nil => tInL
  | cons head tail =>
    by unfold concatUnique; exact
      let tInAppend := appendUnique.inToIn head tInL
      inLeftToIn tInAppend tail

def List.concatUnique.inRiteToIn
  [DecidableEq T]
  (listL: List T)
  {listR: List T}
  (tInR: t ∈ listR)
:
  t ∈ concatUnique listL listR
:=
  match listR with
  | cons head tail =>
    by unfold concatUnique; exact
      match tInR with
      | Mem.head rest =>
          let tInAppend := appendUnique.eqToIn listL t
          inLeftToIn tInAppend rest
      | Mem.tail head inTail =>
        inRiteToIn (appendUnique listL head) inTail

def List.flattenUnique: List (List T) → List T
| nil => []
| cons head tail => head ++ (flattenUnique tail)

namespace Set
  namespace HasListOfAll
    
    def ofIsLeFinite
      {a b: Set D}
      (hasList: a.HasListOfAll)
      (isLe: b ≤ a)
    :
      b.HasListOfAll
    :=
      let ⟨l, allOfAIn⟩ := hasList.unwrap
      let ⟨lf, inIff⟩ := l.pfilter b
      
      ⟨
        lf,
        fun ⟨d, dIn⟩ =>
          (inIff d).mpr (And.intro (allOfAIn ⟨d, isLe dIn⟩) dIn)
      ⟩
    
    def ofPairsOfFinite.combineLists
      (listA: List A)
      (listB: List B)
      (combine: A → B → C)
    :
      { lc: List C // ∀ ⦃a b⦄, a ∈ listA → b ∈ listB → combine a b ∈ lc }
    :=
      match listA with
      | List.nil => ⟨
        [],
        fun _a _b aIn _bIn => nomatch aIn
      ⟩
      | List.cons aHead aTail =>
        let ⟨lcTail, lcTailIn⟩ := combineLists aTail listB combine
        let lcHead := listB.map (combine aHead)
        let lc := lcHead ++ lcTail
        ⟨
          lc,
          fun _ _ aIn bIn =>
            aIn.toOr.elim
              (fun eqHead =>
                let inMapped :=
                  List.mem_map_of_mem (combine aHead) bIn
                
                eqHead ▸
                List.mem_append_left lcTail inMapped)
              (fun inTail =>
                List.mem_append_right lcHead (lcTailIn inTail bIn))
        ⟩
    
    def ofPairsOfFinite
      {sa: Set A}
      (hasListA: sa.HasListOfAll)
      {sb: Set B}
      (hasListB: sb.HasListOfAll)
      (combine: A → B → C)
      (sc: Set C)
      (finiteExtraElements:
        HasListOfAll
          { c | c ∈ sc ∧ ∀ ⦃a b⦄, a ∈ sa → b ∈ sb → c ≠ combine a b })
    :
      sc.HasListOfAll
    :=
      let ⟨la, allOfAIn⟩ := hasListA.unwrap
      let ⟨lb, allOfBIn⟩ := hasListB.unwrap
      let ⟨lc, allOfCIn⟩ := finiteExtraElements.unwrap
      
      let ⟨lab, labIn⟩ :=
        ofPairsOfFinite.combineLists la lb combine
      
      ⟨
        lab ++ lc,
        fun ⟨c, inL⟩ =>
          if h: ∃ a b, a ∈ la ∧ b ∈ lb ∧ c = combine a b then
            let ⟨a, b, aIn, bIn, eq⟩ := h
            
            List.mem_append_left lc (eq ▸ labIn aIn bIn)
          else
            let al: ∀ ⦃a b⦄, a ∈ la → b ∈ lb → c ≠ combine a b :=
              fun a b aIn bIn cEq =>
                h ⟨a, b, aIn, bIn, cEq⟩
            
            let inLc := allOfCIn ⟨
              c,
              And.intro
                inL
                fun _ _ inSa inSb =>
                  al (allOfAIn ⟨_, inSa⟩) (allOfBIn ⟨_, inSb⟩)
            ⟩
            
            List.mem_append_right lab inLc
      ⟩
    
  end HasListOfAll
end Set

def Nat.imageNotFiniteOfInjecive
  {f: Nat → T}
  (inj: f.Injective)
:
  ¬Set.HasListOfAll (fun t => ∃ n, f n = t)
:=
  let image: Set T := { t | ∃ n, f n = t }
  
  fun list =>
    have: Finite image :=
      Set.HasListOfAll.toFinite list
    
    let toFun (t: ↑image): Nat := t.property.unwrap
    let invFun (n: Nat): ↑image := ⟨f n, ⟨n, rfl⟩⟩
    
    let equiv: image ≃ Nat := {
      toFun,
      invFun,
      left_inv := fun t => Subtype.eq t.property.unwrap.property
      right_inv := fun n =>
        inj (invFun n).property.unwrap.property
    }
    
    let natIsFinite := Finite.of_equiv _ equiv
    instInfiniteNat.not_finite natIsFinite

def congrBin
  {fn0 fn1: A → B → C}
  (eqFn: fn0 = fn1)
  (eqArg0: arg0A = arg0B)
  (eqArg1: arg1A = arg1B)
:
  fn0 arg0A arg1A = fn1 arg0B arg1B
:=
  eqFn ▸ eqArg0 ▸ eqArg1 ▸ rfl

def Subtype.val_eq_val
  {P: T → Prop}
  {a b: { t // P t }}
  (eq: a = b)
:
  a.val = b.val
:=
  congr rfl eq

def Subtype.val_eq
  {P: T → Prop}
  (t: T)
  (pt: P t)
:
  (Subtype.mk t pt).val = t
:=
  rfl
