import Etst.WFC.Utils.PairExpr

namespace Etst

namespace PairExpr
  open Expr
  
  def intp_mono_std_pair_defMem
    (leL: (intp2 l0 bv b c).defMem ≤ (intp2 l1 bv b c).defMem)
    (leR: (intp2 r0 bv b c).defMem ≤ (intp2 r1 bv b c).defMem)
  :
    ((pair l0 r0).intp2 bv b c).defMem
      ⊆
    ((pair l1 r1).intp2 bv b c).defMem
  :=
    fun
    | .pair _ _, isDef =>
      let ⟨insL, insR⟩ := insPairElim isDef
      insPair (leL insL) (leR insR)
  
  def intp_mono_std_pair_posMem
    (leL: (intp2 l0 bv b c).posMem ≤ (intp2 l1 bv b c).posMem)
    (leR: (intp2 r0 bv b c).posMem ≤ (intp2 r1 bv b c).posMem)
  :
    ((pair l0 r0).intp2 bv b c).posMem
      ⊆
    ((pair l1 r1).intp2 bv b c).posMem
  :=
    fun
    | .pair _ _, isPos =>
      let ⟨inwL, inwR⟩ := inwPairElim isPos
      inwPair (leL inwL) (leR inwR)
  
  def intp_mono_std_pair
    (leL: intp2 l0 bv b c ≤ intp2 l1 bv b c)
    (leR: intp2 r0 bv b c ≤ intp2 r1 bv b c)
  :
    (pair l0 r0).intp2 bv b c
      ≤
    (pair l1 r1).intp2 bv b c
  := {
    defLe := intp_mono_std_pair_defMem leL.defLe leR.defLe
    posLe := intp_mono_std_pair_posMem leL.posLe leR.posLe
  }
  
  def eq_pair_of_eq
    (eqL: (intp2 l0 bv b c) = (intp2 l1 bv b c))
    (eqR: (intp2 r0 bv b c) = (intp2 r1 bv b c))
  :
    (pair l0 r0).intp2 bv b c = (pair l1 r1).intp2 bv b c
  :=
    let _ := Set3.ordStd
    le_antisymm
      (intp_mono_std_pair (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_pair (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp_mono_std_un_defMem
    (leL: (intp2 l0 bv b c).defMem ≤ (intp2 l1 bv b c).defMem)
    (leR: (intp2 r0 bv b c).defMem ≤ (intp2 r1 bv b c).defMem)
  :
    ((un l0 r0).intp2 bv b c).defMem
      ⊆
    ((un l1 r1).intp2 bv b c).defMem
  :=
    fun _ ins =>
      (insUnElim ins).elim
        (fun insL => insUnL (leL insL))
        (fun insR => insUnR (leR insR))

  def intp_mono_std_un_posMem
    (leL: (intp2 l0 bv b c).posMem ≤ (intp2 l1 bv b c).posMem)
    (leR: (intp2 r0 bv b c).posMem ≤ (intp2 r1 bv b c).posMem)
  :
    ((un l0 r0).intp2 bv b c).posMem
      ⊆
    ((un l1 r1).intp2 bv b c).posMem
  :=
    fun _ inw =>
      (inwUnElim inw).elim
        (fun inwL => inwUnL (leL inwL))
        (fun inwR => inwUnR (leR inwR))

  def intp_mono_std_un
    (leL: intp2 l0 bv b c ≤ intp2 l1 bv b c)
    (leR: intp2 r0 bv b c ≤ intp2 r1 bv b c)
  :
    (un l0 r0).intp2 bv b c
      ≤
    (un l1 r1).intp2 bv b c
  := {
    defLe := intp_mono_std_un_defMem leL.defLe leR.defLe
    posLe := intp_mono_std_un_posMem leL.posLe leR.posLe
  }
  
  def eq_un_of_eq
    (eqL: (intp2 l0 bv b c) = (intp2 l1 bv b c))
    (eqR: (intp2 r0 bv b c) = (intp2 r1 bv b c))
  :
    (un l0 r0).intp2 bv b c = (un l1 r1).intp2 bv b c
  :=
    let _ := Set3.ordStd
    le_antisymm
      (intp_mono_std_un (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_un (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp_mono_std_ir_defMem
    (leL: (intp2 l0 bv b c).defMem ≤ (intp2 l1 bv b c).defMem)
    (leR: (intp2 r0 bv b c).defMem ≤ (intp2 r1 bv b c).defMem)
  :
    ((ir l0 r0).intp2 bv b c).defMem
      ⊆
    ((ir l1 r1).intp2 bv b c).defMem
  :=
    fun _ ins =>
      let ⟨insL, insR⟩ := insIrElim ins
      insIr (leL insL) (leR insR)

  def intp_mono_std_ir_posMem
    (leL: (intp2 l0 bv b c).posMem ≤ (intp2 l1 bv b c).posMem)
    (leR: (intp2 r0 bv b c).posMem ≤ (intp2 r1 bv b c).posMem)
  :
    ((ir l0 r0).intp2 bv b c).posMem
      ⊆
    ((ir l1 r1).intp2 bv b c).posMem
  :=
    fun _ inw =>
      let ⟨inwL, inwR⟩ := inwIrElim inw
      inwIr (leL inwL) (leR inwR)

  def intp_mono_std_ir
    (leL: intp2 l0 bv b c ≤ intp2 l1 bv b c)
    (leR: intp2 r0 bv b c ≤ intp2 r1 bv b c)
  :
    (ir l0 r0).intp2 bv b c
      ≤
    (ir l1 r1).intp2 bv b c
  := {
    defLe := intp_mono_std_ir_defMem leL.defLe leR.defLe
    posLe := intp_mono_std_ir_posMem leL.posLe leR.posLe
  }
  
  def eq_ir_of_eq
    (eqL: (intp2 l0 bv b c) = (intp2 l1 bv b c))
    (eqR: (intp2 r0 bv b c) = (intp2 r1 bv b c))
  :
    (ir l0 r0).intp2 bv b c = (ir l1 r1).intp2 bv b c
  :=
    let _ := Set3.ordStd
    le_antisymm
      (intp_mono_std_ir (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_ir (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp_mono_std_condSome_defMem
    (le: (intp2 e0 bv b c).defMem ≤ (intp2 e1 bv b c).defMem)
  :
    ((condSome e0).intp2 bv b c).defMem
      ⊆
    ((condSome e1).intp2 bv b c).defMem
  :=
    fun _ ins =>
      let ⟨_, insE⟩ := insCondSomeElim ins (d := .null)
      insCondSome (le insE) .null

  def intp_mono_std_condSome_posMem
    (le: (intp2 e0 bv b c).posMem ≤ (intp2 e1 bv b c).posMem)
  :
    ((condSome e0).intp2 bv b c).posMem
      ⊆
    ((condSome e1).intp2 bv b c).posMem
  :=
    fun _ inw =>
      let ⟨_, inwE⟩ := inwCondSomeElim inw (d := .null)
      inwCondSome (le inwE) .null

  def intp_mono_std_condSome
    (le: intp2 e0 bv b c ≤ intp2 e1 bv b c)
  :
    (condSome e0).intp2 bv b c
      ≤
    (condSome e1).intp2 bv b c
  := {
    defLe := intp_mono_std_condSome_defMem le.defLe
    posLe := intp_mono_std_condSome_posMem le.posLe
  }
  
  def eq_condSome_of_eq
    (eq: (intp2 e0 bv b c) = (intp2 e1 bv b c))
  :
    (condSome e0).intp2 bv b c = (condSome e1).intp2 bv b c
  :=
    let _ := Set3.ordStd
    le_antisymm
      (intp_mono_std_condSome (le_of_eq eq))
      (intp_mono_std_condSome (le_of_eq eq.symm))
  
  
  def intp_mono_std_condFull_defMem
    (le: (intp2 e0 bv b c).defMem ≤ (intp2 e1 bv b c).defMem)
  :
    ((condFull e0).intp2 bv b c).defMem
      ⊆
    ((condFull e1).intp2 bv b c).defMem
  :=
    fun _ ins =>
      let insE := insCondFullElim ins (d := .null)
      insCondFull (fun d => le (insE d)) .null

  def intp_mono_std_condFull_posMem
    (le: (intp2 e0 bv b c).posMem ≤ (intp2 e1 bv b c).posMem)
  :
    ((condFull e0).intp2 bv b c).posMem
      ⊆
    ((condFull e1).intp2 bv b c).posMem
  :=
    fun _ inw =>
      let inwE := inwCondFullElim inw (d := .null)
      inwCondFull (fun d => le (inwE d)) .null

  def intp_mono_std_condFull
    (le: intp2 e0 bv b c ≤ intp2 e1 bv b c)
  :
    (condFull e0).intp2 bv b c
      ≤
    (condFull e1).intp2 bv b c
  := {
    defLe := intp_mono_std_condFull_defMem le.defLe
    posLe := intp_mono_std_condFull_posMem le.posLe
  }
  
  def eq_condFull_of_eq
    (eq: (intp2 e0 bv b c) = (intp2 e1 bv b c))
  :
    (condFull e0).intp2 bv b c = (condFull e1).intp2 bv b c
  :=
    let _ := Set3.ordStd
    le_antisymm
      (intp_mono_std_condFull (le_of_eq eq))
      (intp_mono_std_condFull (le_of_eq eq.symm))
  
end PairExpr
