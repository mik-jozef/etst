import Mathlib.Order.FixedPoints

import Etst.WFC.Utils.General.IsLfp
import Etst.WFC.Utils.General.Ordinal


noncomputable def OrderHom.lfpStage
  {ord: CompleteLattice T}
  (f: T →o T)
  (n: Ordinal)
:
  T
:=
  if h: n.IsSuccPrelimit then
    let previous: ↑n → T := fun ⟨n, _⟩ => f.lfpStage n
    iSup previous
  else
    have: n.pred < n := Ordinal.pred_lt_iff_not_isSuccPrelimit.mpr h
    f (f.lfpStage n.pred)
termination_by n

noncomputable abbrev OrderHom.lfpStagePrevious
  {ord: CompleteLattice T}
  (f: T →o T)
  (n: Ordinal)
:
  ↑n → T
:=
  fun ⟨m, _⟩ => f.lfpStage m

def OrderHom.lfpStage_eq_limit
  {ord: CompleteLattice T}
  (f: T →o T)
  {n: Ordinal}
  (isLimit: n.IsSuccPrelimit)
:
  f.lfpStage n = iSup (f.lfpStagePrevious n)
:= by
  rw [lfpStage, dif_pos isLimit]

def OrderHom.lfpStage_eq_succ
  {ord: CompleteLattice T}
  (f: T →o T)
  {n: Ordinal}
  (isSucc: ¬ n.IsSuccPrelimit)
:
  f.lfpStage n = f (f.lfpStage n.pred)
:= by
  rw [lfpStage, dif_neg isSucc]

def OrderHom.lfpStage_apply_eq_succ
  {ord: CompleteLattice T}
  (f: T →o T)
  (n: Ordinal)
:
  f (f.lfpStage n) = f.lfpStage n.succ
:= by
  apply Eq.symm
  let ret := f.lfpStage_eq_succ (Order.not_isSuccPrelimit_succ n)
  rw [Ordinal.pred_succ] at ret
  exact ret


def OrderHom.lfpStage_mono
  {ord: CompleteLattice T}
  (f: T →o T)
  {a b: Ordinal}
  (ab: a ≤ b)
:
  f.lfpStage a ≤ f.lfpStage b
:=
  if hEq: a = b then
    hEq ▸ le_rfl
  else
  let lt := lt_of_le_of_ne ab hEq
  if hLim: b.IsSuccPrelimit then
    f.lfpStage_eq_limit hLim ▸
    le_sSup ⟨⟨a, lt⟩, rfl⟩
  else
    f.lfpStage_eq_succ hLim ▸
    let predLt := Ordinal.pred_lt hLim
    let ih := f.lfpStage_mono (Ordinal.le_pred_of_lt lt)
    let predStageLe :=
      if hPredLim: b.pred.IsSuccPrelimit then by
        conv => lhs; rw [lfpStage_eq_limit f hPredLim]
        apply sSup_le
        intro t ⟨⟨m, mLtBPred⟩, eq⟩
        rw [←eq]
        let fMLe := f.monotone (f.lfpStage_mono mLtBPred.le)
        rw [lfpStage_apply_eq_succ] at fMLe
        have := (hPredLim.succ_lt_iff.mpr mLtBPred).trans predLt
        let mLeSucc := f.lfpStage_mono (Order.le_succ m)
        exact mLeSucc.trans fMLe
      else by
        conv => lhs; rw [lfpStage_eq_succ f hPredLim]
        apply f.monotone
        exact f.lfpStage_mono (Ordinal.pred_le_self b.pred)
    ih.trans predStageLe
termination_by b

def OrderHom.lfpStage_le_lfp
  {ord: CompleteLattice T}
  (f: T →o T)
  (n: Ordinal)
:
  f.lfpStage n ≤ f.lfp
:=
  if h: n.IsSuccPrelimit then
    f.lfpStage_eq_limit h ▸
    f.le_lfp fun t ftLe =>
      iSup_le fun ⟨m, _⟩ =>
        (f.lfpStage_le_lfp m).trans (f.lfp_le ftLe)
  else
    have := Ordinal.pred_lt h
    f.lfpStage_eq_succ h ▸
    f.map_le_lfp (f.lfpStage_le_lfp n.pred)
termination_by n

-- I wish Lean had anonymous structures.
inductive DistinctOrdinalsEqualStage
  {ord: CompleteLattice T}
  (f: T →o T)
:
  Prop
|
  intro
    (n0: Ordinal)
    (n1: Ordinal)
    (nLt: n0 < n1)
    (eqAt: f.lfpStage n0 = f.lfpStage n1)

def OrderHom.lfpStage_ex_fp
  {T: Type u}
  {ord: CompleteLattice T}
  (f: T →o T)
:
  ∃ n: Ordinal.{u},
  ∀ m: Ordinal.{u},
    n ≤ m →
    f.lfpStage m = f.lfp
:=
  let ⟨nUnord0, nUnord1, eqAt, nNeq⟩ :=
    (not_injective_of_ordinal f.lfpStage).toEx
      fun _ p => p.toEx fun _ => Classical.not_imp.mp
  
  -- WLOG, nUnord0 < nUnord1.
  let ⟨n0, _n1, nLt, eqAt⟩ :=
    show DistinctOrdinalsEqualStage f from
    (le_or_gt nUnord0 nUnord1).elim
      (fun le =>
        (lt_or_eq_of_le le).elim
          (fun lt => ⟨nUnord0, nUnord1, lt, eqAt⟩)
          (False.elim ∘ nNeq))
      (fun gt => ⟨nUnord1, nUnord0, gt, eqAt.symm⟩)
  
  let isLeastN0: IsLfp ord.le f (f.lfpStage n0) := ⟨
    ord.le_antisymm _ _
      (f.lfpStage_apply_eq_succ n0 ▸
      eqAt ▸
      f.lfpStage_mono (Order.succ_le_of_lt nLt))
      (f.lfpStage_apply_eq_succ n0 ▸
      f.lfpStage_mono (Order.le_succ n0)),
    fun _fp isFp =>
      (f.lfpStage_le_lfp n0).trans (f.isLeast_lfp.right isFp),
  ⟩
  
  let eqLfp := IsLeast.unique isLeastN0 f.isLeast_lfp
  
  let eqN0 {m} (n0LeM: n0 ≤ m): f.lfpStage n0 = f.lfpStage m :=
    ord.le_antisymm _ _
      (f.lfpStage_mono n0LeM)
      (eqLfp ▸ f.lfpStage_le_lfp m)
  
  ⟨n0, fun _m n0LeM => (eqN0 n0LeM).symm.trans eqLfp⟩

def OrderHom.lfpStage_induction_stages
  {T: Type u}
  {ord: CompleteLattice T}
  (f: T →o T)
  (P: T → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f.lfpStage m)) →
      P (iSup (f.lfpStagePrevious n)))
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f.lfpStage m)) →
      P (f (f.lfpStage n.pred)))
  (n: Ordinal.{u})
:
  P (f.lfpStage n)
:=
  let ih := fun ⟨m, _⟩ => lfpStage_induction_stages f P hLim hSucc m
  if h: n.IsSuccPrelimit then
    f.lfpStage_eq_limit h ▸
    hLim n h ih
  else
    f.lfpStage_eq_succ h ▸
    hSucc n h (Ordinal.pred_lt h) ih
termination_by n

def OrderHom.lfpStage_induction
  {T: Type u}
  {ord: CompleteLattice T}
  (f: T →o T)
  (P: T → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f.lfpStage m)) →
      P (iSup (f.lfpStagePrevious n)))
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f.lfpStage m)) →
      P (f (f.lfpStage n.pred)))
:
  P f.lfp
:=
  let ⟨n, eqAt⟩ := f.lfpStage_ex_fp
  eqAt n le_rfl ▸ lfpStage_induction_stages f P hLim hSucc n

def OrderHom.lfpStage_induction_stages2
  {T0 T1: Type u}
  {ord: CompleteLattice T0}
  {ord: CompleteLattice T1}
  (f0: T0 →o T0)
  (f1: T1 →o T1)
  (P: T0 → T1 → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f0.lfpStage m) (f1.lfpStage m)) →
      P
        (iSup (f0.lfpStagePrevious n))
        (iSup (f1.lfpStagePrevious n)))
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f0.lfpStage m) (f1.lfpStage m)) →
      P (f0 (f0.lfpStage n.pred)) (f1 (f1.lfpStage n.pred)))
  (n: Ordinal.{u})
:
  P (f0.lfpStage n) (f1.lfpStage n)
:=
  let ih := fun ⟨m, _⟩ => lfpStage_induction_stages2 f0 f1 P hLim hSucc m
  if h: n.IsSuccPrelimit then
    f0.lfpStage_eq_limit h ▸
    f1.lfpStage_eq_limit h ▸
    hLim n h ih
  else
    f0.lfpStage_eq_succ h ▸
    f1.lfpStage_eq_succ h ▸
    hSucc n h (Ordinal.pred_lt h) ih
termination_by n

def OrderHom.lfpStage_induction2
  {T0 T1: Type u}
  {ord: CompleteLattice T0}
  {ord: CompleteLattice T1}
  (f0: T0 →o T0)
  (f1: T1 →o T1)
  (P: T0 → T1 → Prop)
  (hLim:
    ∀ n: Ordinal.{u},
      n.IsSuccPrelimit →
      (∀ m: ↑n, P (f0.lfpStage m) (f1.lfpStage m)) →
      P
        (iSup (f0.lfpStagePrevious n))
        (iSup (f1.lfpStagePrevious n)))
  (hSucc:
    ∀ n: Ordinal.{u},
      ¬ n.IsSuccPrelimit →
      n.pred < n →
      (∀ m: ↑n, P (f0.lfpStage m) (f1.lfpStage m)) →
      P (f0 (f0.lfpStage n.pred)) (f1 (f1.lfpStage n.pred)))
:
  P f0.lfp f1.lfp
:=
  let ⟨n0, eqAt0⟩ := f0.lfpStage_ex_fp
  let ⟨n1, eqAt1⟩ := f1.lfpStage_ex_fp
  
  (le_or_gt n0 n1).elim
    (fun le =>
      eqAt0 n1 le ▸
      eqAt1 n1 le_rfl ▸
      lfpStage_induction_stages2 f0 f1 P hLim hSucc n1)
    (fun gt =>
      eqAt0 n0 le_rfl ▸
      eqAt1 n0 gt.le ▸
      lfpStage_induction_stages2 f0 f1 P hLim hSucc n0)
