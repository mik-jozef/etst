import Etst.WFC.Utils.RulesOfInference

namespace Etst


namespace Expr
  def inter_bvar_eq_empty
    (nlt: ¬ x < bv.length)
  :
    (bvar x).interpretation salg bv b c = Set3.empty
  := by
    unfold interpretation
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def inter_none_eq_empty:
    interpretation salg bv b c none = Set3.empty
  :=
    Set3.eq4
      (fun _ => ninsNone)
      nofun
      (fun _ => ninwNone)
      nofun
  
  def inter_mono_std_op_defMem
    {sig: Signature}
    {salg: Salgebra sig}
    {o: sig.Op}
    {args0 args1: sig.Params o → Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ param: sig.Params o,
        ((args0 param).interpretation salg bv0 b0 c0).defMem
          ≤
        ((args1 param).interpretation salg bv1 b1 c1).defMem)
  :
    ((op o args0).interpretation salg bv0 b0 c0).defMem
      ⊆
    ((op o args1).interpretation salg bv1 b1 c1).defMem
  :=
    fun _ dIn => salg.isMonotonic o _ _ le dIn
  
  def inter_mono_std_op_posMem
    {sig: Signature}
    {salg: Salgebra sig}
    {o: sig.Op}
    {args0 args1: sig.Params o → Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ param: sig.Params o,
        ((args0 param).interpretation salg bv0 b0 c0).posMem
          ≤
        ((args1 param).interpretation salg bv1 b1 c1).posMem)
  :
    ((op o args0).interpretation salg bv0 b0 c0).posMem
      ⊆
    ((op o args1).interpretation salg bv1 b1 c1).posMem
  :=
    fun _ dIn => salg.isMonotonic o _ _ le dIn
  
  def inter_mono_std_op
    {sig: Signature}
    {salg: Salgebra sig}
    {o: sig.Op}
    {args0 args1: sig.Params o → Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ param: sig.Params o,
        ((args0 param).interpretation salg bv0 b0 c0)
          ≤
        ((args1 param).interpretation salg bv1 b1 c1))
  :
    ((op o args0).interpretation salg bv0 b0 c0)
      ≤
    ((op o args1).interpretation salg bv1 b1 c1)
  := {
    defLe := inter_mono_std_op_defMem (fun param => (le param).defLe)
    posLe := inter_mono_std_op_posMem (fun param => (le param).posLe)
  }
  
  def eq_op_of_eq
    {sig: Signature}
    {salg: Salgebra sig}
    {o: sig.Op}
    {args0 args1: sig.Params o → Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (eq:
      ∀ param: sig.Params o,
        ((args0 param).interpretation salg bv0 b0 c0)
          =
        ((args1 param).interpretation salg bv1 b1 c1))
  :
    ((op o args0).interpretation salg bv0 b0 c0)
      =
    ((op o args1).interpretation salg bv1 b1 c1)
  :=
    let _ := Set3.ordStd
    le_antisymm
      (inter_mono_std_op (fun param => le_of_eq (eq param)))
      (inter_mono_std_op (fun param => le_of_eq (eq param).symm))
  
  
  -- Note we're using `b0 b0` and `b1 b1` in the assumption.
  def inter_mono_std_cpl_defMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      (e1.interpretation salg bv1 b1 b1).posMem
        ≤
      (e0.interpretation salg bv0 b0 b0).posMem)
  :
    ((cpl e0).interpretation salg bv0 b0 c0).defMem
      ⊆
    ((cpl e1).interpretation salg bv1 b1 c1).defMem
  :=
    fun _ ins =>
      let ninwE := insCplElim (c := c0) ins
      insCpl c0 (fun isPos => ninwE (le isPos))

  def inter_mono_std_cpl_posMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      (e1.interpretation salg bv1 b1 b1).defMem
        ≤
      (e0.interpretation salg bv0 b0 b0).defMem)
  :
    ((cpl e0).interpretation salg bv0 b0 c0).posMem
      ⊆
    ((cpl e1).interpretation salg bv1 b1 c1).posMem
  :=
    fun _ inw =>
      let ninsE := inwCplElim (c := c0) inw
      inwCpl c0 (fun isDef => ninsE (le isDef))

  def inter_mono_std_cpl
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      (e1.interpretation salg bv1 b1 b1)
        ≤
      (e0.interpretation salg bv0 b0 b0))
  :
    ((cpl e0).interpretation salg bv0 b0 c0)
      ≤
    ((cpl e1).interpretation salg bv1 b1 c1)
  := {
    defLe := inter_mono_std_cpl_defMem le.posLe
    posLe := inter_mono_std_cpl_posMem le.defLe
  }

  def eq_cpl_of_eq
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (eq:
      (e0.interpretation salg bv0 b0 b0)
        =
      (e1.interpretation salg bv1 b1 b1))
  :
    ((cpl e0).interpretation salg bv0 b0 c0)
      =
    ((cpl e1).interpretation salg bv1 b1 c1)
  :=
    let _ := Set3.ordStd
    le_antisymm
      (inter_mono_std_cpl (le_of_eq eq.symm))
      (inter_mono_std_cpl (le_of_eq eq))
  
  
  def inter_mono_std_arbUn_defMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0).defMem
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1).defMem)
  :
    ((arbUn e0).interpretation salg bv0 b0 c0).defMem
      ⊆
    ((arbUn e1).interpretation salg bv1 b1 c1).defMem
  :=
    fun _ ⟨dB, isDef⟩ => ⟨dB, le dB isDef⟩

  def inter_mono_std_arbUn_posMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0).posMem
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1).posMem)
  :
    ((arbUn e0).interpretation salg bv0 b0 c0).posMem
      ⊆
    ((arbUn e1).interpretation salg bv1 b1 c1).posMem
  :=
    fun _ ⟨dB, isPos⟩ => ⟨dB, le dB isPos⟩

  def inter_mono_std_arbUn
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0)
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1))
  :
    ((arbUn e0).interpretation salg bv0 b0 c0)
      ≤
    ((arbUn e1).interpretation salg bv1 b1 c1)
  := {
    defLe := inter_mono_std_arbUn_defMem (fun dB => (le dB).defLe)
    posLe := inter_mono_std_arbUn_posMem (fun dB => (le dB).posLe)
  }

  def eq_arbUn_of_eq
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (eq:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0)
        =
      (e1.interpretation salg (dB :: bv1) b1 c1))
  :
    ((arbUn e0).interpretation salg bv0 b0 c0)
      =
    ((arbUn e1).interpretation salg bv1 b1 c1)
  :=
    let _ := Set3.ordStd
    le_antisymm
      (inter_mono_std_arbUn (fun dB => le_of_eq (eq dB)))
      (inter_mono_std_arbUn (fun dB => le_of_eq (eq dB).symm))
  
  
  def inter_mono_std_arbIr_defMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0).defMem
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1).defMem)
  :
    ((arbIr e0).interpretation salg bv0 b0 c0).defMem
      ⊆
    ((arbIr e1).interpretation salg bv1 b1 c1).defMem
  :=
    fun _ h dB => le dB (h dB)

  def inter_mono_std_arbIr_posMem
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0).posMem
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1).posMem)
  :
    ((arbIr e0).interpretation salg bv0 b0 c0).posMem
      ⊆
    ((arbIr e1).interpretation salg bv1 b1 c1).posMem
  :=
    fun _ h dB => le dB (h dB)

  def inter_mono_std_arbIr
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (le:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0)
        ≤
      (e1.interpretation salg (dB :: bv1) b1 c1))
  :
    ((arbIr e0).interpretation salg bv0 b0 c0)
      ≤
    ((arbIr e1).interpretation salg bv1 b1 c1)
  :=
  {
    defLe := inter_mono_std_arbIr_defMem (fun dB => (le dB).defLe)
    posLe := inter_mono_std_arbIr_posMem (fun dB => (le dB).posLe)
  }

  def eq_arbIr_of_eq
    {sig: Signature}
    {salg: Salgebra sig}
    {e0 e1: Expr sig}
    {bv0 bv1: List salg.D}
    {b0 c0 b1 c1: Valuation salg.D}
    (eq:
      ∀ dB,
      (e0.interpretation salg (dB :: bv0) b0 c0)
        =
      (e1.interpretation salg (dB :: bv1) b1 c1))
  :
    ((arbIr e0).interpretation salg bv0 b0 c0)
      =
    ((arbIr e1).interpretation salg bv1 b1 c1)
  :=
    let _ := Set3.ordStd
    le_antisymm
      (inter_mono_std_arbIr (fun dB => le_of_eq (eq dB)))
      (inter_mono_std_arbIr (fun dB => le_of_eq (eq dB).symm))
  
end Expr
