import Mathlib.Order.FixedPoints

import Etst.WFC.Utils.General.IsLfp
import Etst.WFC.Utils.General.Ordinal
import Etst.WFC.Utils.General.PointwiseOrder

universe u

noncomputable def OrderHom.lfpStageCc
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (n: Ordinal)
:
  T
:=
  if h: n.IsSuccPrelimit then
    let previous: ↑n → T := fun ⟨n, _⟩ => f.lfpStageCc isCc n
    if hCh: IsChain ord.le (Set.range previous) then
      (isCc hCh).choose
    else
      default
  else
    have: n.pred < n := Ordinal.pred_lt_iff_not_isSuccPrelimit.mpr h
    f (f.lfpStageCc isCc n.pred)
termination_by n

noncomputable abbrev OrderHom.lfpStageCcPrevious
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (n: Ordinal)
:
  ↑n → T
:=
  fun ⟨m, _⟩ => f.lfpStageCc isCc m

def OrderHom.lfpStageCcPrevious_eq_iUnion
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  {n: Ordinal}
  (isLimit: n.IsSuccPrelimit)
:
  Eq
    (Set.range (f.lfpStageCcPrevious isCc n))
    (⋃ m: ↑n, Set.range (f.lfpStageCcPrevious isCc m))
:=
  Set.ext fun _t => ⟨
    fun ⟨⟨m, mLt⟩, eq⟩ => ⟨
      _,
      ⟨⟨m.succ, isLimit.succ_lt_iff.mpr mLt⟩, rfl⟩,
      eq ▸ ⟨⟨m, Order.lt_succ m⟩, rfl⟩,
    ⟩,
    fun ⟨_s, ⟨⟨_m, mLt⟩, (eq: Set.range _ = _)⟩, tInS⟩ =>
      let ⟨⟨mm, mmLt⟩, eqMm⟩ := eq ▸ tInS
      ⟨⟨mm, mmLt.trans mLt⟩, eqMm⟩,
  ⟩

def OrderHom.lfpStageCc_eq_succ
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  {n: Ordinal}
  (isSucc: ¬ n.IsSuccPrelimit)
:
  f.lfpStageCc isCc n = f (f.lfpStageCc isCc n.pred)
:= by
  rw [lfpStageCc, dif_neg isSucc]

def OrderHom.lfpStageCc_apply_eq_succ
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (n: Ordinal)
:
  f (f.lfpStageCc isCc n) = f.lfpStageCc isCc n.succ
:= by
  apply Eq.symm
  let ret := f.lfpStageCc_eq_succ isCc (Order.not_isSuccPrelimit_succ n)
  rw [Ordinal.pred_succ] at ret
  exact ret


def OrderHom.lfpStageCc_isChain_of_mono
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (n: Ordinal)
  (isMono:
    ∀ {a b: ↑n},
      a ≤ b →
      f.lfpStageCc isCc a ≤ f.lfpStageCc isCc b)
:
  IsChain ord.le (Set.range (f.lfpStageCcPrevious isCc n))
:=
  fun _ ⟨⟨m0, m0Lt⟩, eq0⟩ _ ⟨⟨m1, m1Lt⟩, eq1⟩ _ =>
    (le_total m0 m1).elim
      (fun m0Le => eq0 ▸ eq1 ▸
        Or.inl (@isMono ⟨m0, m0Lt⟩ ⟨m1, m1Lt⟩ m0Le))
      (fun m1Le => eq0 ▸ eq1 ▸
        Or.inr (@isMono ⟨m1, m1Lt⟩ ⟨m0, m0Lt⟩ m1Le))

def OrderHom.lfpStageCc_mono
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  {a b} (ab: a ≤ b)
:
  f.lfpStageCc isCc a ≤ f.lfpStageCc isCc b
:=
  if hEq: a = b then
    hEq ▸ le_rfl
  else by
  let lt := lt_of_le_of_ne ab hEq
  conv => rhs; unfold lfpStageCc
  if hLim: b.IsSuccPrelimit then
    let isChain :=
      f.lfpStageCc_isChain_of_mono isCc b (fun {a b} (ab: a ≤ b) =>
        have := b.property
        f.lfpStageCc_mono isCc ab)
    rw [dif_pos hLim, dif_pos isChain]
    exact (isCc isChain).choose_spec.left ⟨⟨a, lt⟩, rfl⟩
  else
    rw [dif_neg hLim]
    let predLt := Ordinal.pred_lt hLim
    let ih := f.lfpStageCc_mono isCc (Ordinal.le_pred_of_lt lt)
    let predStageLe: lfpStageCc isCc f b.pred ≤ f (lfpStageCc isCc f b.pred) :=
      if hPredLim: b.pred.IsSuccPrelimit then by
        let ihPred {a b: ↑b.pred} (ab: a ≤ b) :=
          have := b.property.trans predLt
          f.lfpStageCc_mono isCc ab
        let isChainPred := f.lfpStageCc_isChain_of_mono isCc b.pred ihPred
        conv => lhs; rw [lfpStageCc, dif_pos hPredLim, dif_pos isChainPred]
        apply (isCc isChainPred).choose_spec.right
        intro t ⟨⟨m, mLtBPred⟩, eq⟩
        rw [←eq]
        let fMLe := f.monotone (f.lfpStageCc_mono isCc mLtBPred.le)
        rw [lfpStageCc_apply_eq_succ] at fMLe
        have := (hPredLim.succ_lt_iff.mpr mLtBPred).trans predLt
        let mLeSucc := f.lfpStageCc_mono isCc (Order.le_succ m)
        exact mLeSucc.trans fMLe
      else by
        conv => lhs; rw [lfpStageCc, dif_neg hPredLim]
        apply f.monotone
        exact f.lfpStageCc_mono isCc (Ordinal.pred_le_self b.pred)
    exact ih.trans predStageLe
termination_by b

def OrderHom.lfpStageCc_isChain
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (n: Ordinal)
:
  IsChain ord.le (Set.range (f.lfpStageCcPrevious isCc n))
:=
  f.lfpStageCc_isChain_of_mono isCc n (f.lfpStageCc_mono isCc)


def OrderHom.lfpStageCc_eq_limit
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  {n: Ordinal}
  (isLimit: n.IsSuccPrelimit)
:
  f.lfpStageCc isCc n = (isCc (f.lfpStageCc_isChain isCc n)).choose
:= by
  rw [
    lfpStageCc,
    dif_pos isLimit,
    dif_pos (f.lfpStageCc_isChain isCc n)
  ]


def OrderHom.lfpStageCc_le_fp
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  {fp} (isFp: fp ∈ (Function.fixedPoints f))
  (n: Ordinal)
:
  f.lfpStageCc isCc n ≤ fp
:=
  if h: n.IsSuccPrelimit then
    f.lfpStageCc_eq_limit isCc h ▸
    (isCc (f.lfpStageCc_isChain isCc n)).choose_spec.right
      (fun t ⟨⟨m, _⟩, eq⟩ =>
        eq ▸ f.lfpStageCc_le_fp isCc isFp m)
  else
    have := Ordinal.pred_lt h
    f.lfpStageCc_eq_succ isCc h ▸
    isFp ▸
    f.monotone (f.lfpStageCc_le_fp isCc isFp n.pred)
termination_by n

-- I wish Lean had anonymous structures.
inductive DistinctOrdinalsEqualStageCc
  {T} [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
:
  Prop
|
  intro
    (n0: Ordinal)
    (n1: Ordinal)
    (nLt: n0 < n1)
    (eqAt: f.lfpStageCc isCc n0 = f.lfpStageCc isCc n1)

def OrderHom.lfpStageCc_ex_fp
  {T: Type u}
  [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
:
  ∃ n: Ordinal.{u},
  ∀ m: Ordinal.{u},
    n ≤ m →
    IsLfp ord.le f (f.lfpStageCc isCc m)
:=
  let ⟨nUnord0, nUnord1, eqAt, nNeq⟩ :=
    (not_injective_of_ordinal (f.lfpStageCc isCc)).toEx
      fun _ p => p.toEx fun _ => Classical.not_imp.mp
  
  -- WLOG, nUnord0 < nUnord1.
  let ⟨n0, _n1, nLt, eqAt⟩ :=
    show DistinctOrdinalsEqualStageCc isCc f from
    (le_or_gt nUnord0 nUnord1).elim
      (fun le =>
        (lt_or_eq_of_le le).elim
          (fun lt => ⟨nUnord0, nUnord1, lt, eqAt⟩)
          (False.elim ∘ nNeq))
      (fun gt => ⟨nUnord1, nUnord0, gt, eqAt.symm⟩)
  
  let isLeastN0: IsLfp ord.le f (f.lfpStageCc isCc n0) := ⟨
    ord.le_antisymm _ _
      (f.lfpStageCc_apply_eq_succ isCc n0 ▸
      eqAt ▸
      f.lfpStageCc_mono isCc (Order.succ_le_of_lt nLt))
      (f.lfpStageCc_apply_eq_succ isCc n0 ▸
      f.lfpStageCc_mono isCc (Order.le_succ n0)),
    fun _fp isFp => f.lfpStageCc_le_fp isCc isFp n0,
  ⟩
  
  let eqN0 {m} (n0LeM: n0 ≤ m):
    f.lfpStageCc isCc n0 = f.lfpStageCc isCc m
  :=
    ord.le_antisymm _ _
      (f.lfpStageCc_mono isCc n0LeM)
      (f.lfpStageCc_le_fp isCc isLeastN0.left m)
  
  ⟨n0, fun _m n0LeM => (eqN0 n0LeM) ▸ isLeastN0⟩

noncomputable def OrderHom.lfpCc
  {T: Type u}
  [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
:
  T
:=
  f.lfpStageCc isCc (f.lfpStageCc_ex_fp isCc).choose

noncomputable def OrderHom.lfpCc_isLfp
  {T: Type u}
  [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
:
  IsLfp ord.le f (f.lfpCc isCc)
:=
  let n := (f.lfpStageCc_ex_fp isCc).choose
  (f.lfpStageCc_ex_fp isCc).choose_spec n le_rfl

def OrderHom.lfpStageCc_induction
  {T: Type u}
  [Inhabited T]
  {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  (f: T →o T)
  (P: T → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f.lfpStageCc isCc m)) →
      (isChain:
        IsChain ord.le (Set.range (f.lfpStageCcPrevious isCc n))) →
      P (isCc isChain).choose)
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f.lfpStageCc isCc m)) →
      P (f (f.lfpStageCc isCc n.pred)))
:
  P (f.lfpCc isCc)
:=
  let rec p (n: Ordinal): P (lfpStageCc isCc f n) :=
    let ih := fun ⟨m, _⟩ => p m
    if h: n.IsSuccPrelimit then
      f.lfpStageCc_eq_limit isCc h ▸
      hLim n h ih (f.lfpStageCc_isChain isCc n)
    else
      f.lfpStageCc_eq_succ isCc h ▸
      hSucc n h (Ordinal.pred_lt h) ih
  termination_by n
  
  p _

def OrderHom.lfpStageCc_induction2
  {T0 T1: Type u}
  [Inhabited T0]
  [Inhabited T1]
  {ord0: PartialOrder T0}
  {ord1: PartialOrder T1}
  (isCc0: IsChainComplete ord0)
  (isCc1: IsChainComplete ord1)
  (f0: T0 →o T0)
  (f1: T1 →o T1)
  (P: T0 → T1 → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f0.lfpStageCc isCc0 m) (f1.lfpStageCc isCc1 m)) →
      (isChain0: IsChain ord0.le (Set.range (f0.lfpStageCcPrevious isCc0 n))) →
      (isChain1: IsChain ord1.le (Set.range (f1.lfpStageCcPrevious isCc1 n))) →
      P
        (isCc0 isChain0).choose
        (isCc1 isChain1).choose)
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f0.lfpStageCc isCc0 m) (f1.lfpStageCc isCc1 m)) →
      P (f0 (f0.lfpStageCc isCc0 n.pred)) (f1 (f1.lfpStageCc isCc1 n.pred)))
:
  P (f0.lfpCc isCc0) (f1.lfpCc isCc1)
:=
  let rec p (n: Ordinal): P (lfpStageCc isCc0 f0 n) (lfpStageCc isCc1 f1 n) :=
    let ih := fun ⟨m, _⟩ => p m
    if h: n.IsSuccPrelimit then
      f0.lfpStageCc_eq_limit isCc0 h ▸
      f1.lfpStageCc_eq_limit isCc1 h ▸
      let isChain0 := f0.lfpStageCc_isChain isCc0 n
      let isChain1 := f1.lfpStageCc_isChain isCc1 n
      hLim n h ih isChain0 isChain1
    else
      f0.lfpStageCc_eq_succ isCc0 h ▸
      f1.lfpStageCc_eq_succ isCc1 h ▸
      hSucc n h (Ordinal.pred_lt h) ih
  termination_by n
  
  let ⟨n0, isLeast0⟩ := f0.lfpStageCc_ex_fp isCc0
  let ⟨n1, isLeast1⟩ := f1.lfpStageCc_ex_fp isCc1
  
  (le_or_gt n0 n1).elim
    (fun le =>
      let eq0 :=
        IsLeast.unique
          (isLeast0 n1 le)
          (f0.lfpCc_isLfp isCc0)
      let eq1 :=
        IsLeast.unique
          (isLeast1 n1 le_rfl)
          (f1.lfpCc_isLfp isCc1)
      eq0 ▸ eq1 ▸ p n1)
    (fun gt => 
      let eq0 :=
        IsLeast.unique
          (isLeast0 n0 le_rfl)
          (f0.lfpCc_isLfp isCc0)
      let eq1 :=
        IsLeast.unique
          (isLeast1 n0 gt.le)
          (f1.lfpCc_isLfp isCc1)
      eq0 ▸ eq1 ▸ p n0)
