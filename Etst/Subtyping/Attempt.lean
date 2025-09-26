/-
  TODO describe this file
  
  The `indCoind` rule combines both induction and coinduction principles.
  Given a monotonic operator f, and a set X,
  
    f(X) ⊆ X  implies  lfp(f) ⊆ X  (induction)
    X ⊆ f(X)  implies  X ⊆ gfp(f)  (coinduction)
  
  let A = s A
  let B' = t' B'   (t X = ~(t' ~X))
  let B = ~B'
  
  Let's assume A and B' are both positive (i.e., monotonic), so thus is
  also s and t'.
  
  A ⊆ B
  A ⊆ ~B'
  A ⊆ ~(t' B')
  A ⊆ ~(t' ~~B')
  A ⊆ t ~B'
  A ⊆ t B
  
  A ⊆ B may be proved by any of:
  0. s A ⊆ B (unfolding A)
  1. s B ⊆ B (induction on A)
  2. s (A & B) ⊆ B (not implied by, but a moral combination of the above two)
  3. A ⊆ t B (unfolding B, eq to `A ⊆ ~(t' B')`, `A ⊆ ~(t' ~B)`)
  4. A ⊆ t A (coinduction on "B", or precisely on t)
  5. A ⊆ t (A | B)) (combination of 3 and 4, eq to `A ⊆ ~(t' (~A & B'))`)
  6. s (A & B) ⊆ t (A | B) (combination of all of the above)
  
  Questions and notes:
  0. Should `A & B ⊆ C` be also provable by induction even if neither A
     nor B is a subset of C?
     - yes. It's equivalent to `A ⊆ C | ~B`, which is in a form suitable
       for induction.
     - similarly, `A | B ⊆ C` is equivalent
  1. Induction should be usable even if A uses complements expressions
     that do not use A (directly or transitively).
  2. Do we need induction on pairs*, or is it derivable from induction on
     definitions? (*ie: P () ∧ (P a ∧ P b → P (a,b)) → P t)
     - things like that division produces structurally smaller pairs
       should be inferred automatically.
  
  def Nat0 := 0 | succ (Nat0 | Nat1)
  def Nat1 := 0 | succ (Nat0 | Nat1)
  
  Nat0 | Nat1 ⊆ Nat
-/

import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.PairExprMono

namespace Etst
open PairExpr


def IsDefSubset (a b: Set3 Pair) := ∀ ⦃p⦄, p ∈ a.posMem → p ∈ b.defMem
def IsPosSubset (a b: Set3 Pair) := ∀ ⦃p⦄, p ∈ a.defMem → p ∈ b.posMem

abbrev PairDl.IsDefSubset (dl: PairDl) (a b: PairExpr) :=
  Etst.IsDefSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
abbrev PairDl.IsPosSubset (dl: PairDl) (a b: PairExpr) :=
  Etst.IsPosSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)


def Expr.replacePosVars
  (e: Expr sig)
  (replacer: Nat → Expr sig)
:
  Expr sig
:=
  match e with
  | var x => replacer x
  | bvar x => .bvar x
  | op o args => op o fun param => (args param).replacePosVars replacer
  | cpl body => cpl body -- Note: no replacing in complements.
  | arbUn body => arbUn (body.replacePosVars replacer)
  | arbIr body => arbIr (body.replacePosVars replacer)


structure InductionDescriptor (dl: PairDl) where
  left: Nat
  rite: PairExpr
  riteIsClean: rite.IsClean
  expansion: PairExpr
  expandsInto: ExpandsInto dl (dl.getDef left) expansion
  
structure CoinductionDescriptor (dl: PairDl) where
  left: PairExpr
  rite: Nat
  leftIsClean: left.IsClean
  expansion: PairExpr
  expandsInto: ExpandsInto dl (dl.getDef rite) expansion

structure IndCoindDescriptor (dl: PairDl) where
  left: Nat
  rite: Nat
  expansionLeft: PairExpr
  expansionRite: PairExpr
  expandsLeft: ExpandsInto dl (dl.getDef left) expansionLeft
  expandsRite: ExpandsInto dl (dl.getDef rite) expansionRite

inductive FixpointMethod (dl: PairDl) where
| ind (desc: InductionDescriptor dl)
| coind (desc: CoinductionDescriptor dl)
| indCoind (desc: IndCoindDescriptor dl)

abbrev FixpointMethods (dl: PairDl) := List (FixpointMethod dl)

-- The induction hypothesis for a variable `x`.
def FixpointMethod.ih
  (x: Nat)
  (fm: FixpointMethod dl)
  (expr: PairExpr)
:
  PairExpr
:=
  match fm with
  | .ind desc =>
    if desc.left = x then .ir desc.rite expr else expr
  | .coind _ => expr
  | .indCoind desc =>
    if desc.left = x then .ir (.cpl (.var desc.rite)) expr else expr

-- The coinduction hypothesis for a variable `x`.
def FixpointMethod.ch
  (x: Nat)
  (fm: FixpointMethod dl)
  (expr: PairExpr)
:
  PairExpr
:=
  match fm with
  | .ind _ => expr
  | .coind desc =>
    if desc.rite = x then .ir (.cpl desc.left) expr else expr
  | .indCoind desc =>
    if desc.rite = x then .ir (.cpl (.var desc.left)) expr else expr

def FixpointMethods.ih
  (fms: FixpointMethods dl)
  (x: Nat)
:
  PairExpr
:=
  fms.foldr (FixpointMethod.ih x) (.var x)

def FixpointMethods.ch
  (fms: FixpointMethods dl)
  (x: Nat)
:
  PairExpr
:=
  fms.foldr (FixpointMethod.ch x) (.var x)

def FixpointMethods.hypothesifyInd
  (fms: FixpointMethods dl)
  (expr: PairExpr)
:
  PairExpr
:=
  expr.replacePosVars fms.ih

def FixpointMethods.hypothesifyCoind
  (fms: FixpointMethods dl)
  (expr: PairExpr)
:
  PairExpr
:=
  .cpl (expr.replacePosVars fms.ch)


def FixpointMethod.Invariant
  (wfm v: Valuation Pair)
:
  FixpointMethod dl → Prop
| .ind desc => IsDefSubset (v desc.left) (desc.rite.intp [] wfm)
| .coind desc => IsDefSubset (desc.left.intp [] wfm) (v desc.rite).cpl
| .indCoind desc =>
  And
    (IsDefSubset (v desc.left) (wfm desc.rite).cpl)
    (IsDefSubset (wfm desc.left) (v desc.rite).cpl)

def FixpointMethod.exprLeft: FixpointMethod dl → PairExpr
| .ind desc => .var desc.left
| .coind desc => desc.left
| .indCoind desc => .var desc.left

def FixpointMethod.exprRite: FixpointMethod dl → PairExpr
| .ind desc => desc.rite
| .coind desc => .cpl (.var desc.rite)
| .indCoind desc => .cpl (.var desc.rite)

def FixpointMethod.Invariant.out
  (fms: FixpointMethods dl)
  (i: fms.Index)
  (inv: fms[i].Invariant dl.wfm dl.wfm)
:
  dl.IsDefSubset fms[i].exprLeft fms[i].exprRite
:=
  match h: fms[i] with
  | .ind desc => by rw [h] at inv; exact inv
  | .coind desc => by rw [h] at inv; exact inv
  | .indCoind desc => by rw [h] at inv; exact inv.left

mutual
inductive Premise (dl: PairDl):
  FixpointMethods dl → FixpointMethod dl → Type
| ind
    (premise: Subset dl (fms.hypothesifyInd desc.expansion) desc.rite)
  :
    Premise dl fms (.ind desc)
| coind
    (premise: Subset dl desc.left (fms.hypothesifyCoind desc.expansion))
  :
    Premise dl fms (.coind desc)
| indCoind
    (premise:
      Subset
        dl
        (fms.hypothesifyInd desc.expansionLeft)
        (fms.hypothesifyCoind desc.expansionRite))
  :
    Premise dl fms (.indCoind desc)

inductive Subset
  (dl: PairDl)
:
  PairExpr → PairExpr → Type

| null: Subset dl .null .null
| pair
    (sl: Subset dl al bl)
    (sr: Subset dl ar br)
  :
    Subset dl (.pair al ar) (.pair bl br)
| unL (s: Subset dl a b) {r: PairExpr}: Subset dl a (.un b r)
| unR (s: Subset dl a b) {l: PairExpr}: Subset dl a (.un l b)
| fixpointMethods
    (fms: FixpointMethods dl)
    (premises: (i: fms.Index) → Premise dl fms fms[i])
    (i: fms.Index)
  :
    Subset dl fms[i].exprLeft fms[i].exprRite
end

def PremiseHolds (fms: FixpointMethods dl):
  FixpointMethod dl → Prop
| .ind desc =>
    dl.IsDefSubset (fms.hypothesifyInd desc.expansion) desc.rite
| .coind desc =>
    dl.IsDefSubset desc.left (fms.hypothesifyCoind desc.expansion)
| .indCoind desc =>
    dl.IsDefSubset
      (fms.hypothesifyInd desc.expansionLeft)
      (fms.hypothesifyCoind desc.expansionRite)


def FixpointMethods.var_le_hypothesifyInd
  (fms: FixpointMethods dl)
  (inv: ∀ (i: fms.Index), fms[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  v x ≤ (fms.hypothesifyInd (var x)).intp bv dl.wfm
:=
  match fms with
  | [] => v_le x
  | .ind desc :: (rest: FixpointMethods dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail inv
    if h: desc.left = x then
      if_pos h ▸
      {
        defLe := fun _ inX =>
          let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX.toPos)
          insIr
            (desc.riteIsClean.changeBvDefMem inRite)
            ((rest.var_le_hypothesifyInd invTail v_le).defLe inX)
        posLe := fun _ inX =>
          let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX)
          inwIr
            (desc.riteIsClean.changeBvPosMem inRite.toPos)
            ((rest.var_le_hypothesifyInd invTail v_le).posLe inX)
      }
    else
      if_neg h ▸
      rest.var_le_hypothesifyInd invTail v_le
  | .coind _ :: (rest: FixpointMethods dl) =>
    let invTail := List.Index.indexedTail inv
    rest.var_le_hypothesifyInd invTail v_le
  | .indCoind desc :: (rest: FixpointMethods dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail inv
    if h: desc.left = x then
      if_pos h ▸
      {
        defLe := fun _ inV =>
          insIr
            ((inv ⟨0, Nat.zero_lt_succ _⟩).left (h ▸ inV.toPos))
            ((rest.var_le_hypothesifyInd invTail v_le).defLe inV)
        posLe := fun _ inV =>
          inwIr
            ((inv ⟨0, Nat.zero_lt_succ _⟩).left (h ▸ inV)).toPos
            ((rest.var_le_hypothesifyInd invTail v_le).posLe inV)
      }
    else
      if_neg h ▸
      rest.var_le_hypothesifyInd invTail v_le

def FixpointMethods.le_hypothesifyInd
  (fms: FixpointMethods dl)
  (inv: ∀ (i: fms.Index), fms[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  expr.intp2 bv dl.wfm v
    ≤
  (fms.hypothesifyInd expr).intp bv dl.wfm
:=
  let _ := Set3.ordStdLattice
  match expr with
  | .var _ => var_le_hypothesifyInd fms inv v_le
  | .bvar _ => le_rfl
  | .op _o _args =>
    Expr.inter_mono_std_op fun _param =>
      fms.le_hypothesifyInd inv v_le
  | .cpl _ => le_rfl
  | .arbUn _ =>
    Expr.inter_mono_std_arbUn fun _d =>
      fms.le_hypothesifyInd inv v_le
  | .arbIr _ =>
    Expr.inter_mono_std_arbIr fun _d =>
      fms.le_hypothesifyInd inv v_le


def FixpointMethods.var_hypothesifyCoind_le
  (fms: FixpointMethods dl)
  (inv: ∀ (i: fms.Index), fms[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  v x ≤ intp (fms.ch x) bv dl.wfm
:=
  match fms with
  | [] => v_le x
  | .ind _ :: (rest: FixpointMethods dl) =>
    let invTail := List.Index.indexedTail inv
    rest.var_hypothesifyCoind_le invTail (fun _ => v_le _)
  | .coind desc :: (rest: FixpointMethods dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail inv
    if h: desc.rite = x then
      if_pos h ▸
      {
        defLe := fun _ insX =>
          insIr
            (fun inwLeft =>
              let inwLeft := desc.leftIsClean.changeBvPosMem inwLeft
              inv ⟨0, Nat.zero_lt_succ _⟩ inwLeft (h ▸ insX.toPos))
            ((rest.var_hypothesifyCoind_le invTail v_le).defLe insX)
        posLe := fun _ insX =>
          inwIr
            (fun insLeft =>
              let insLeft := desc.leftIsClean.changeBvDefMem insLeft
              inv ⟨0, Nat.zero_lt_succ _⟩ insLeft.toPos (h ▸ insX))
            ((rest.var_hypothesifyCoind_le invTail v_le).posLe insX)
      }
    else
      if_neg h ▸
      rest.var_hypothesifyCoind_le invTail (fun _ => v_le _)
  | .indCoind desc :: (rest: FixpointMethods dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail inv
    if h: desc.rite = x then
      if_pos h ▸
      {
        defLe := fun _ insX =>
          insIr
            (fun inwLeft =>
              (inv ⟨0, Nat.zero_lt_succ _⟩).right inwLeft (h ▸ insX.toPos))
            ((rest.var_hypothesifyCoind_le invTail v_le).defLe insX)
        posLe := fun _ insX =>
          inwIr
            (fun insLeft =>
              (inv ⟨0, Nat.zero_lt_succ _⟩).right insLeft.toPos (h ▸ insX))
            ((rest.var_hypothesifyCoind_le invTail v_le).posLe insX)
      }
    else
      if_neg h ▸
      rest.var_hypothesifyCoind_le invTail (fun _ => v_le _)

def FixpointMethods.hypothesifyCoind_le
  (fms: FixpointMethods dl)
  (inv: ∀ (i: fms.Index), fms[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
  {expr: PairExpr}
:
  (intp (expr.replacePosVars fms.ch) bv dl.wfm).cpl
    ≤
  (expr.intp2 bv dl.wfm v).cpl
:=
  let _ := Set3.ordStdLattice
  let rec helper (bv: List Pair): (expr: PairExpr) →
    expr.intp2 bv dl.wfm v
      ≤
    intp (expr.replacePosVars fms.ch) bv dl.wfm
  
  | .var _ => fms.var_hypothesifyCoind_le inv v_le
  | .bvar _x => le_rfl
  | .op _o args =>
    Expr.inter_mono_std_op fun param =>
      helper bv (args param)
  | .cpl _ => le_rfl
  | .arbUn body =>
    Expr.inter_mono_std_arbUn fun d =>
      helper (d :: bv) body
  | .arbIr body =>
    Expr.inter_mono_std_arbIr fun d =>
      helper (d :: bv) body
  
  Set3.LeStd.compl_le_compl (helper bv expr)


def DefList.lfpStage_le_wfm_std
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC salg dl (dl.wfm salg)).lfpStage n ≤ dl.wfm salg
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC salg]
  exact (operatorC salg dl (dl.wfm salg)).lfpStage_le_lfp n

def FixpointMethods.isSound
  (fms: FixpointMethods dl)
  (premisesHold: (i: fms.Index) → PremiseHolds fms (fms[i]))
  (i: fms.Index)
:
  dl.IsDefSubset fms[i].exprLeft fms[i].exprRite
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC pairSalgebra dl dl.wfm).lfp :=
    dl.wfm_eq_lfpC pairSalgebra
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC pairSalgebra dl dl.wfm)
      (fun v =>
        ∀ (i: fms.Index), fms[i].Invariant dl.wfm v)
      -- TODO the cases may not be needed for the limit case.
      (fun n isLim ih i =>
      -- | n, isLim, ih, _, _, .ind desc descIn, _, isPos =>
      --   let i := descIn.index
      --   let lePremiseL := 4
      --   sorry
      -- | n, isLim, ih, _, _, .coind desc descIn, _, isPos =>
      --   sorry
      -- | n, isLim, ih, _, _, .indCoind desc descIn, _, isPos =>
        sorry)
      (fun n notLim predLt ih i =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC pairSalgebra dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std pairSalgebra n.pred
        let predStageLe := dl.lfpStage_le_wfm_std pairSalgebra n.pred
        match h: fms[i] with
        | .ind desc => fun _ isPos =>
          let lePremiseL := fms.le_hypothesifyInd ihPred predStageLe
          let leExp := desc.expandsInto.lfpStage_le_std [] n.pred
          (h ▸ premisesHold i) (lePremiseL.posLe (leExp.posLe isPos))
        
        | .coind desc => fun p isPos =>
          let expLe := desc.expandsInto.lfpStage_le_std [] n.pred
          let lePremiseR := fms.hypothesifyCoind_le ihPred predStageLe
          expLe.notPosLe (lePremiseR.defLe ((h ▸ premisesHold i) isPos))
        
        | .indCoind desc =>
          And.intro
            (fun _ isPos =>
              let lePremiseL := fms.le_hypothesifyInd ihPred predStageLe
              let leExp := desc.expandsLeft.lfpStage_le_std [] n.pred
              let insHypoExpRiteCpl :=
                (h ▸ premisesHold i) (lePremiseL.posLe (leExp.posLe isPos))
              let expLe := desc.expandsRite.lfpStage_le_std [] n.pred
              let lePremiseR := fms.hypothesifyCoind_le ihPred predStageLe
              let lkjh: _ ∈ ((intp2 (dl.getDef desc.rite) [] dl.wfm predStage)).posMemᶜ :=
                expLe.notPosLe (lePremiseR.defLe insHypoExpRiteCpl)
              -- Oh, no.
              sorry)
            sorry)
  
  let invariant: fms[i].Invariant dl.wfm dl.wfm :=
    by rw [←eq] at isDefSub; exact isDefSub i
  
  invariant.out

-- -- Fail to show termination ://///
-- def Subset.isSound:
--   Subset dl a b →
--   IsDefSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
-- |
--   null, _, isPos => isPos
-- | pair sl sr, .pair a b, isPos =>
--   let ⟨inwL, inwR⟩ := inwPairElim isPos
--   insPair (sl.isSound inwL) (sr.isSound inwR)
-- | unL s, _, isPos =>
--   insUnL (s.isSound isPos)
-- | unR s, _, isPos =>
--   insUnR (s.isSound isPos)
-- | fixpointMethods fms premises out, _, isPos =>
--   let premisesHold (i: fms.Index): PremiseHolds fms fms[i] :=
--     match fms[i], premises i with
--     | .induction desc, .ind premise =>
--       PremiseHolds.ind premise.isSound
--     | _, @Premise.coind dl fmsa vf df => sorry
--     | _, @Premise.indCoind dl fmsa vf df => sorry
--   fmsIsSound fms premisesHold out isPos


def Subset.isSound
  (sub: Subset dl a b)
:
  dl.IsDefSubset a b
:=
  sub.rec
    (motive_1 := fun fms fm _ => PremiseHolds fms fm)
    (motive_2 := fun a b _ => dl.IsDefSubset a b)
    (fun _ isSub _ isPos => isSub isPos)
    (fun _ isSub _ isPos => isSub isPos)
    (fun _ isSub _ isPos => isSub isPos)
    (fun _ isPos => isPos)
    (fun
    | _, _, isSubL, isSubR, .pair _ _, isPos =>
      let ⟨inwL, inwR⟩ := inwPairElim isPos
      insPair (isSubL inwL) (isSubR inwR))
    (fun _ _ isSub _ isPos => insUnL (isSub isPos))
    (fun _ _ isSub _ isPos => insUnR (isSub isPos))
    (fun _ _ out ih _ isPos => FixpointMethods.isSound _ ih out isPos)
