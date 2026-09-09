/-
  Triset intersection.
  
  The intersection `inter a b` of two pre-trisets is defined as an
  index of `uniSetMap` whose elements are the elements of `a` that
  are fuzzily in `b`, together with the elements of `b` that are
  fuzzily in `a`. The two disjuncts make the operation symmetric
  by construction (a one-sided definition would not be symmetric
  outside Hc).
  
  The fuzzy characteristic equation
  
    IsInDef (inter a b) x ↔ IsInDef a x ∧ IsInDef b x
  
  holds unconditionally for the definite lane. For the possible lane
  it holds on hereditarily classical trisets (off Hc, `IsBisimPos` is
  not transitive, and the equation fails).
  
  The intersection of hereditarily classical trisets is shown to be
  hereditarily classical.
-/

import Etst.WFC.Utils.Trisets.TrisetMembership

namespace Etst

open SingleLaneExpr


/-
  ## Section: the intersection index
  
  `inter a b` is (an index of) the triset whose definite elements
  are the definite elements of `a` fuzzily contained in `b`, plus
  the definite elements of `b` fuzzily contained in `a` - and
  similarly for the possible lane. The two disjuncts make the
  operation symmetric by construction.
-/

namespace Pair.PreTriset
  
  def interExpr (a b: Pair): BasicExpr :=
    .un
      (.ir
        (.call (.const () isInDl.consts.uniSetMap) a.toExpr)
        (.zth (.call (.const () isInDl.consts.IsIn) b.toExpr)))
      (.ir
        (.call (.const () isInDl.consts.uniSetMap) b.toExpr)
        (.zth (.call (.const () isInDl.consts.IsIn) a.toExpr)))
  
  def inter (a b: Pair): Pair :=
    uniSetMapIndex
      isInDl.toDefList
      isInDl.size
      []
      (interExpr a b)
  
  def inter_wfm_eq (a b: Pair):
    uniSetMap.call (inter a b) = (interExpr a b).triIntp [] isInDl.wfm
  :=
    FiniteDefList.uniSetMapAt_eq isInDl [] (interExpr a b)
  
  def inter_defMem_iff {a b x: Pair}:
    (uniSetMap.call (inter a b)).defMem x ↔
      Or
        (((uniSetMap.call a).defMem x) ∧ (isInDl.IsInDef b x))
        (((uniSetMap.call b).defMem x) ∧ (isInDl.IsInDef a x))
  :=
    inter_wfm_eq a b ▸
      Iff.intro
        (fun h =>
          match inUnElim h with
          | .inl hIr =>
            let ⟨hCallU, hZth⟩ := inIrElim hIr
            let hU := inCallElimSingle hCallU (intp2_toExpr_eq_singleton a)
            let ⟨_, hC⟩ := inZthElim hZth
            let hI := inCallElimSingle hC (intp2_toExpr_eq_singleton b)
            .inl ⟨isInDl.wfm_uniSetMap_eq ▸ hU, isInDl.IsInDef_of_defMem hI⟩
          | .inr hIr =>
            let ⟨hCallU, hZth⟩ := inIrElim hIr
            let hU := inCallElimSingle hCallU (intp2_toExpr_eq_singleton b)
            let ⟨_, hC⟩ := inZthElim hZth
            let hI := inCallElimSingle hC (intp2_toExpr_eq_singleton a)
            .inr ⟨isInDl.wfm_uniSetMap_eq ▸ hU, isInDl.IsInDef_of_defMem hI⟩)
        (fun h =>
          match h with
          | .inl ⟨hU, hI⟩ =>
            inUnL (inIr
              (inCall
                (show (isInDl.wfm isInDl.consts.uniSetMap).defMem (.pair a x)
                from isInDl.wfm_uniSetMap_eq ▸ hU)
                (inToExpr a))
              (inZth (inCall (hI.toDefMem (w := .null)) (inToExpr b))))
          | .inr ⟨hU, hI⟩ =>
            inUnR (inIr
              (inCall
                (show (isInDl.wfm isInDl.consts.uniSetMap).defMem (.pair b x)
                from isInDl.wfm_uniSetMap_eq ▸ hU)
                (inToExpr b))
              (inZth (inCall (hI.toDefMem (w := .null)) (inToExpr a)))))
  
  def inter_posMem_iff {a b x: Pair}:
    (uniSetMap.call (inter a b)).posMem x ↔
      Or
        (((uniSetMap.call a).posMem x) ∧ (isInDl.IsInPos b x))
        (((uniSetMap.call b).posMem x) ∧ (isInDl.IsInPos a x))
  :=
    inter_wfm_eq a b ▸
      Iff.intro
        (fun h =>
          match inUnElim h with
          | .inl hIr =>
            let ⟨hCallU, hZth⟩ := inIrElim hIr
            let hU := inCallElimSingle hCallU (intp2_toExpr_eq_singleton a)
            let ⟨_, hC⟩ := inZthElim hZth
            let hI := inCallElimSingle hC (intp2_toExpr_eq_singleton b)
            .inl ⟨isInDl.wfm_uniSetMap_eq ▸ hU, isInDl.IsInPos_of_posMem hI⟩
          | .inr hIr =>
            let ⟨hCallU, hZth⟩ := inIrElim hIr
            let hU := inCallElimSingle hCallU (intp2_toExpr_eq_singleton b)
            let ⟨_, hC⟩ := inZthElim hZth
            let hI := inCallElimSingle hC (intp2_toExpr_eq_singleton a)
            .inr ⟨isInDl.wfm_uniSetMap_eq ▸ hU, isInDl.IsInPos_of_posMem hI⟩)
        (fun h =>
          match h with
          | .inl ⟨hU, hI⟩ =>
            inUnL (inIr
              (inCall
                (show (isInDl.wfm isInDl.consts.uniSetMap).posMem (.pair a x)
                  from isInDl.wfm_uniSetMap_eq ▸ hU)
                (inToExpr a))
              (inZth (inCall (hI.toPosMem (w := .null)) (inToExpr b))))
          | .inr ⟨hU, hI⟩ =>
            inUnR (inIr
              (inCall
                (show (isInDl.wfm isInDl.consts.uniSetMap).posMem (.pair b x)
                  from isInDl.wfm_uniSetMap_eq ▸ hU)
                (inToExpr b))
              (inZth (inCall (hI.toPosMem (w := .null)) (inToExpr a)))))
  
  /-
    The fuzzy characteristic equation, definite lane.
    (The possible-lane version only holds on Hc trisets —
    `IsBisimPos` is not transitive off Hc.)
  -/
  def isInDef_inter_iff {a b x: Pair}:
    isInDl.IsInDef (inter a b) x ↔ isInDl.IsInDef a x ∧ isInDl.IsInDef b x
  :=
    Iff.intro
      (fun ⟨x', isB, hIns⟩ =>
        match inter_defMem_iff.mp hIns with
        | .inl ⟨hInsA, hIsInB⟩ =>
          ⟨⟨x', isB, hInsA⟩,
           hIsInB.respectsBisim (setoid.iseqv.refl b) isB.toBisim.symm⟩
        | .inr ⟨hInsB, hIsInA⟩ =>
          ⟨hIsInA.respectsBisim (setoid.iseqv.refl a) isB.toBisim.symm,
           ⟨x', isB, hInsB⟩⟩)
      (fun ⟨⟨x1, isB1, hInsA⟩, hIsInB⟩ =>
        ⟨x1, isB1,
         inter_defMem_iff.mpr
           (.inl ⟨hInsA, hIsInB.respectsBisim (setoid.iseqv.refl b) isB1.toBisim⟩)⟩)
  
  -- Transitions of `inter a b` land in `inter a' b'`, up to bisimilarity.
  def inter_respects_sim {a a' b b': Pair}
    (ha: IsBisim a a')
    (hb: IsBisim b b')
  :
    ∀ l x,
      transitionSystem l (inter a b) x →
      ∃ x', transitionSystem l (inter a' b') x' ∧ IsBisim x x'
  | .ins, _x, t =>
    match inter_defMem_iff.mp t with
    | .inl ⟨hInsA, hIsInB⟩ =>
      let ⟨x', hInsA', bisimX⟩ := ha.ins hInsA
      ⟨x', inter_defMem_iff.mpr (.inl ⟨hInsA', hIsInB.respectsBisim hb bisimX⟩), bisimX⟩
    | .inr ⟨hInsB, hIsInA⟩ =>
      let ⟨x', hInsB', bisimX⟩ := hb.ins hInsB
      ⟨x', inter_defMem_iff.mpr (.inr ⟨hInsB', hIsInA.respectsBisim ha bisimX⟩), bisimX⟩
  | .inw, _x, t =>
    match inter_posMem_iff.mp t with
    | .inl ⟨hInwA, hIsInB⟩ =>
      let ⟨x', hInwA', bisimX⟩ := ha.inw hInwA
      ⟨x', inter_posMem_iff.mpr (.inl ⟨hInwA', hIsInB.respectsBisim hb bisimX⟩), bisimX⟩
    | .inr ⟨hInwB, hIsInA⟩ =>
      let ⟨x', hInwB', bisimX⟩ := hb.inw hInwB
      ⟨x', inter_posMem_iff.mpr (.inr ⟨hInwB', hIsInA.respectsBisim ha bisimX⟩), bisimX⟩
  
  def inter_respectsBisim {a a' b b': Pair}
    (ha: IsBisim a a')
    (hb: IsBisim b b')
  :
    IsBisim (inter a b) (inter a' b')
  :=
    ⟨fun u v => (u = inter a b ∧ v = inter a' b') ∨ IsBisim u v,
     ⟨fun l u v u' rUV trans =>
        match rUV with
        | .inr bisimUV =>
          let ⟨v', t', r'⟩ := transitionSystem.IsBisimilar_isSimulation l u v u' bisimUV trans
          ⟨v', t', .inr r'⟩
        | .inl ⟨uEq, vEq⟩ =>
          let ⟨v', t', bisim⟩ := inter_respects_sim ha hb l u' (uEq ▸ trans)
          ⟨v', vEq ▸ t', .inr bisim⟩,
      fun l p q p' rQP trans =>
        match rQP with
        | .inr bisimQP =>
          let ⟨q', t', r'⟩ := transitionSystem.IsBisimilar_isSimulation l p q p' bisimQP.symm trans
          ⟨q', t', .inr (Pair.PreTriset.IsBisim.symm r')⟩
        | .inl ⟨qEq, pEq⟩ =>
          let ⟨q', t', bisim⟩ := inter_respects_sim ha.symm hb.symm l p' (pEq ▸ trans)
          ⟨q', qEq ▸ t', .inr bisim.symm⟩⟩,
     .inl ⟨rfl, rfl⟩⟩
  
  -- The two disjuncts commute.
  def inter_call_comm (a b: Pair):
    uniSetMap.call (inter a b) = uniSetMap.call (inter b a)
  :=
    Set3.ordApx.le_antisymm _ _
      ⟨fun _x h => inter_defMem_iff.mpr (inter_defMem_iff.mp h).symm,
       fun _x h => inter_posMem_iff.mpr (inter_posMem_iff.mp h).symm⟩
      ⟨fun _x h => inter_defMem_iff.mpr (inter_defMem_iff.mp h).symm,
       fun _x h => inter_posMem_iff.mpr (inter_posMem_iff.mp h).symm⟩
  
  def inter_comm_bisim (a b: Pair):
    IsBisim (inter a b) (inter b a)
  :=
    isBisim_of_uniSetMap_call_eq (inter_call_comm a b)
  
end Pair.PreTriset


/-
  ## Section: the quotient-level intersection
-/

namespace Triset
  
  def inter (tsA tsB: Pair.Triset): Pair.Triset :=
    Quotient.lift₂
      (fun a b => ⟦Pair.PreTriset.inter a b⟧)
      (fun _a _b _a' _b' ha hb =>
        Quot.sound (Pair.PreTriset.inter_respectsBisim ha hb))
      tsA tsB
  
  /-- The fuzzy characteristic equation of intersection, definite lane. -/
  def isInDef_inter_iff {tsA tsB x: Pair.Triset}:
    Iff
      (Triset.IsInDef (inter tsA tsB) x)
      (Triset.IsInDef tsA x ∧ Triset.IsInDef tsB x)
  :=
    Quotient.inductionOn₃
      (motive := fun tsA tsB tsX =>
        Iff
          (Triset.IsInDef (inter tsA tsB) tsX)
          (Triset.IsInDef tsA tsX ∧ Triset.IsInDef tsB tsX))
      tsA tsB x
      (fun _a _b _x => Pair.PreTriset.isInDef_inter_iff)
  
  def inter_comm
    (tsA tsB: Pair.Triset)
  :
    inter tsA tsB = inter tsB tsA
  :=
    Quotient.inductionOn₂
      (motive := fun tsA tsB => inter tsA tsB = inter tsB tsA)
      tsA tsB
      (fun a b => Quot.sound (Pair.PreTriset.inter_comm_bisim a b))
  
  /-- The intersection of Hc trisets is Hc. -/
  def hc_inter {tsA tsB: Pair.Triset}
    (hcA: Pair.Triset.Hc tsA)
    (hcB: Pair.Triset.Hc tsB)
  :
    Pair.Triset.Hc (inter tsA tsB)
  :=
    Quotient.inductionOn₂
      (motive := fun tsA tsB =>
        Pair.Triset.Hc tsA →
        Pair.Triset.Hc tsB →
        Pair.Triset.Hc (inter tsA tsB))
      tsA tsB
      (fun a b hA hB nhc =>
        match nhc with
        | .notClassical isPos notDef =>
          let ⟨_preTs, _preElem, tsEq, elemEq, inw⟩ := isPos
          let bisim := (Quotient.exact tsEq).symm
          let ⟨y, inwI, bisimEY⟩ := bisim.inw inw
          match Pair.PreTriset.inter_posMem_iff.mp inwI with
          | .inl ⟨inwA, isInPosB⟩ =>
            let ⟨_y1, isBPy1, inwB1⟩ := isInPosB
            let ⟨y2, insB2, bisim12⟩ := Pair.Triset.hc_ins_of_inw hB inwB1
            let ⟨y3, insA3, bisimY3⟩ := Pair.Triset.hc_ins_of_inw hA inwA
            let hcY3: Pair.Triset.Hc ⟦y3⟧ := Pair.Triset.hc_hered hA insA3.toPos
            let hcY2: Pair.Triset.Hc ⟦y2⟧ := Pair.Triset.hc_hered hB insB2.toPos
            let hcY: Pair.Triset.Hc ⟦y⟧ :=
              Quotient.sound (s := Pair.PreTriset.setoid) bisimY3 ▸ hcY3
            let isBPy2: bisimDl.IsBisimPos y y2 :=
              isBPy1.respectsBisim (Pair.PreTriset.setoid.iseqv.refl y) bisim12
            let isBDy2: bisimDl.IsBisimDef y y2 :=
              bisimDl.IsBisimPos.toIsBisimDef hcY hcY2 isBPy2
            let isInDefB: isInDl.IsInDef b y := ⟨y2, isBDy2, insB2⟩
            let isInDefB3: isInDl.IsInDef b y3 :=
              isInDefB.respectsBisim (Pair.PreTriset.setoid.iseqv.refl b) bisimY3
            let insI: Pair.PreTriset.Ins (Pair.PreTriset.inter a b) y3 :=
              Pair.PreTriset.inter_defMem_iff.mpr (.inl ⟨insA3, isInDefB3⟩)
            notDef
              ⟨Pair.PreTriset.inter a b, y3,
               rfl,
               elemEq.trans
                 ((Quot.sound bisimEY).trans (Quot.sound bisimY3)),
               insI⟩
          | .inr ⟨inwB, isInPosA⟩ =>
            let ⟨_y1, isBPy1, inwA1⟩ := isInPosA
            let ⟨y2, insA2, bisim12⟩ := Pair.Triset.hc_ins_of_inw hA inwA1
            let ⟨y3, insB3, bisimY3⟩ := Pair.Triset.hc_ins_of_inw hB inwB
            let hcY3: Pair.Triset.Hc ⟦y3⟧ := Pair.Triset.hc_hered hB insB3.toPos
            let hcY2: Pair.Triset.Hc ⟦y2⟧ := Pair.Triset.hc_hered hA insA2.toPos
            let hcY: Pair.Triset.Hc ⟦y⟧ :=
              Quotient.sound (s := Pair.PreTriset.setoid) bisimY3 ▸ hcY3
            let isBPy2: bisimDl.IsBisimPos y y2 :=
              isBPy1.respectsBisim (Pair.PreTriset.setoid.iseqv.refl y) bisim12
            let isBDy2: bisimDl.IsBisimDef y y2 :=
              bisimDl.IsBisimPos.toIsBisimDef hcY hcY2 isBPy2
            let isInDefA: isInDl.IsInDef a y := ⟨y2, isBDy2, insA2⟩
            let isInDefA3: isInDl.IsInDef a y3 :=
              isInDefA.respectsBisim (Pair.PreTriset.setoid.iseqv.refl a) bisimY3
            let insI: Pair.PreTriset.Ins (Pair.PreTriset.inter a b) y3 :=
              Pair.PreTriset.inter_defMem_iff.mpr (.inr ⟨insB3, isInDefA3⟩)
            notDef
              ⟨Pair.PreTriset.inter a b, y3,
               rfl,
               elemEq.trans
                 ((Quot.sound bisimEY).trans (Quot.sound bisimY3)),
               insI⟩
        | .containsNhc isPos isNhc =>
          let ⟨_preTs, preElem, tsEq, elemEq, inw⟩ := isPos
          let bisim := (Quotient.exact tsEq).symm
          let ⟨y, inwI, bisimEY⟩ := bisim.inw inw
          let hcY: Pair.Triset.Hc ⟦y⟧ :=
            match Pair.PreTriset.inter_posMem_iff.mp inwI with
            | .inl ⟨inwA, _⟩ => Pair.Triset.hc_hered hA inwA
            | .inr ⟨inwB, _⟩ => Pair.Triset.hc_hered hB inwB
          let hcElem: Pair.Triset.Hc ⟦preElem⟧ :=
            Quotient.sound (s := Pair.PreTriset.setoid) bisimEY ▸ hcY
          (elemEq ▸ hcElem) isNhc)
      hcA hcB
  
  /-- The fuzzy characteristic equation, possible lane, on Hc trisets. -/
  def isInPos_inter_iff_of_hc {tsA tsB tsX: Pair.Triset}
    (hcA: Pair.Triset.Hc tsA)
    (hcB: Pair.Triset.Hc tsB)
    (hcX: Pair.Triset.Hc tsX)
  :
    Iff
      (Triset.IsInPos (inter tsA tsB) tsX)
      (Triset.IsInPos tsA tsX ∧ Triset.IsInPos tsB tsX)
  :=
    (Triset.isInPos_iff_isInDef_of_hc (hc_inter hcA hcB) hcX).trans
      (isInDef_inter_iff.trans
        (Iff.intro
          (fun ⟨hd0, hd1⟩ =>
            ⟨(Triset.isInPos_iff_isInDef_of_hc hcA hcX).mpr hd0,
             (Triset.isInPos_iff_isInDef_of_hc hcB hcX).mpr hd1⟩)
          (fun ⟨hp0, hp1⟩ =>
            ⟨(Triset.isInPos_iff_isInDef_of_hc hcA hcX).mp hp0,
             (Triset.isInPos_iff_isInDef_of_hc hcB hcX).mp hp1⟩)))
  
end Triset
