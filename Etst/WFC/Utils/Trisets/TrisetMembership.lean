/-
  Here we define WFC's notion of membership for the "sets" of WFC
  (ie. indices of uniSetMap quotiented by bisimilarity), and show
  the relation is well-defined on the quotient.
  
  This notion of membership is not the same as `Triset.ExactMem`
  from `BisimQuotient.lean`. The exact membership treats the empty
  triset and the undetermined triset as fully distinct trisets.
  The membership defined here is "fuzzy" in that a set containing
  one of these two trisets is considered to possibly contain the
  other as well (since settling the membership of possible elements
  of the undetermined set could produce the empty set).
  
  We also show that
  - the definite-lane bisimilarity implies actual bisimilarity of
    pre-trisets (and therefore equality of trisets).
  - for hereditarily classical trisets, definite-lane bisimilarity
    equals possible-lane bisimilarity equals equality of trisets.
-/

import Etst.WFC.Ch7_Polymorphism
import Etst.WFC.Utils.Trisets.BisimQuotient

namespace Etst

open SingleLaneExpr


pairDefList bisimDl extends uniSetMapDl
  s3 NonBisim :=
    Ex p q,
    × p
    × q
    × (| (Ex p',
         & (?some p' & uniSetMap p)
         & (All q', (?some q' & uniSetMap q) -> NonBisim p' q'))
      | (Ex q',
         & (?some q' & uniSetMap q)
         & (All p', (?some p' & uniSetMap p) -> NonBisim p' q')))
  
  s3 IsBisim := Ex p q, p × q × (!NonBisim p q)
  
  s3 IsIn :=
    Ex set elem,
    × set
    × elem
    × (Ex elemX,
      & IsBisim elem elemX
      & (?some elemX & uniSetMap set))
pairDefList.

-- A Lean-native definition of `NonBisim`'s possible-membership lane.
inductive bisimDl.NonBisimDef: (p q: Pair) → Prop where
| ofP {p q}
    (p': Pair)
    (inP: (uniSetMap.call p).defMem p')
    (allQ:
      ∀ q',
        (uniSetMap.call q).posMem q' →
        bisimDl.NonBisimDef p' q')
  :
    bisimDl.NonBisimDef p q
| ofQ {p q}
    (q': Pair)
    (inQ: (uniSetMap.call q).defMem q')
    (allP:
      ∀ p',
        (uniSetMap.call p).posMem p' →
        bisimDl.NonBisimDef p' q')
  :
    bisimDl.NonBisimDef p q

-- A Lean-native definition of `NonBisim`'s necessary-membership lane.
inductive bisimDl.NonBisimPos: (p q: Pair) → Prop where
| ofP {p q}
    (p': Pair)
    (inP: (uniSetMap.call p).posMem p')
    (allQ:
      ∀ q',
        (uniSetMap.call q).defMem q' →
        bisimDl.NonBisimPos p' q')
  :
    bisimDl.NonBisimPos p q
| ofQ {p q}
    (q': Pair)
    (inQ: (uniSetMap.call q).posMem q')
    (allP:
      ∀ p',
        (uniSetMap.call p).defMem p' →
        bisimDl.NonBisimPos p' q')
  :
    bisimDl.NonBisimPos p q

def bisimDl.IsBisimDef (p q: Pair): Prop := ¬ NonBisimPos p q
def bisimDl.IsBisimPos (p q: Pair): Prop := ¬ NonBisimDef p q

-- A Lean-native definition of `IsIn`'s definite-membership lane:
-- `elem` is (a bisimilar copy of) a definite element of `set`.
def bisimDl.IsInDef (set elem: Pair): Prop :=
  ∃ elemX, IsBisimDef elem elemX ∧ Set3Pair.PreTriset.Ins set elemX

-- A Lean-native definition of `IsIn`'s possible-membership lane:
-- `elem` is (a bisimilar copy of) a possible element of `set`.
def bisimDl.IsInPos (set elem: Pair): Prop :=
  ∃ elemX, IsBisimPos elem elemX ∧ Set3Pair.PreTriset.Inw set elemX

/-
  ## Section: proving equivalence of the Lean-native WFM defs
  
  This section is write-once, read-never code. You have been warned.
-/
def bisimDl.wfm_uniSetMap_eq:
  bisimDl.wfm bisimDl.consts.uniSetMap = uniSetMap
:=
  (FiniteDefList.extend_wfm_eq_of_lt
    uniSetMapDl bisimDl rfl rfl (by decide)).symm

def bisimDl.NonBisimDef_of_Ins {cst index p q w}
  (ins: bisimDl.Ins cst index)
  (cstEq: cst = bisimDl.consts.NonBisim)
  (indexEq: index = .pair p (.pair q w))
:
  NonBisimDef p q
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let ins:
      (bisimDl.getDef bisimDl.consts.NonBisim).triIntp2Def
        []
        cause.leastBackgroundApx
        cause.leastContextApx
        (.pair p (.pair q w))
    :=
      indexEq ▸ cstEq ▸ isCause cause.leastValsApxAreSat
    let ⟨pAlias, ins⟩ := inArbUnElim ins
    let ⟨qAlias, ins⟩ := inArbUnElim ins
    let ⟨leftP, ins⟩ := inProdElim ins
    let ⟨leftQ, ins⟩ := inProdElim ins
    let pEq: pAlias = p := (inVarElim leftP rfl).symm
    let qEq: qAlias = q := (inVarElim leftQ rfl).symm
    match inUnElim ins with
    | .inl ins =>
      let ⟨p', ins⟩ := inArbUnElim ins
      let ⟨insSome, insArbIr⟩ := inIrElim ins
      let ⟨p'Alias, insIr⟩ := inSomeElim insSome
      let ⟨insVar, insCall⟩ := inIrElim insIr
      let p'AliasEq: p'Alias = p' := inVarElim insVar rfl
      let insAtP := pEq ▸ p'AliasEq ▸ inCallElimSingle insCall rfl
      let inP: uniSetMap.defMem (p.pair p') :=
        wfm_uniSetMap_eq ▸ (cinsSat insAtP).isSound
      .ofP p' inP fun q' inQ =>
        match inUnElim (inArbIrElim insArbIr q') with
        | .inl ins =>
          let notBout inBout :=
            (boutSat inBout).isSound (wfm_uniSetMap_eq ▸ qEq ▸ inQ)
          False.elim <|
          ins (inSome q' (inIr rfl (inCall notBout rfl)))
        | .inr ins =>
          let ins := inCallElimSingle ins rfl
          let ins := inCallElimSingle ins rfl
          NonBisimDef_of_Ins (cinsSat ins) rfl rfl
    | .inr ins =>
      let ⟨q', ins⟩ := inArbUnElim ins
      let ⟨insSome, insArbIr⟩ := inIrElim ins
      let ⟨q'Alias, insIr⟩ := inSomeElim insSome
      let ⟨insVar, insCall⟩ := inIrElim insIr
      let q'AliasEq: q'Alias = q' := inVarElim insVar rfl
      let insAtQ := qEq ▸ q'AliasEq ▸ inCallElimSingle insCall rfl
      let inQ: uniSetMap.defMem (q.pair q') :=
        wfm_uniSetMap_eq ▸ (cinsSat insAtQ).isSound
      .ofQ q' inQ fun p' inP =>
        match inUnElim (inArbIrElim insArbIr p') with
        | .inl ins =>
          let notBout inBout :=
            (boutSat inBout).isSound (wfm_uniSetMap_eq ▸ pEq ▸ inP)
          False.elim <|
          ins (inSome p' (inIr rfl (inCall notBout rfl)))
        | .inr ins =>
          let ins := inCallElimSingle ins rfl
          let ins := inCallElimSingle ins rfl
          NonBisimDef_of_Ins (cinsSat ins) rfl rfl

def bisimDl.NonBisimDef_of_defMem {p q w}
  (ins: ((bisimDl.vals.NonBisim.call p).call q).defMem w)
:
  NonBisimDef p q
:=
  NonBisimDef_of_Ins (DefList.Ins.isComplete ins) rfl rfl

def bisimDl.NonBisimDef.toDefMem {p q w}
  (nbi: bisimDl.NonBisimDef p q)
:
  ((bisimDl.vals.NonBisim.call p).call q).defMem w
:=
  DefList.InWfm.of_in_def_no_fv (lane := .defLane)
    (inArbUn p
      (inArbUn q
        (inProd (inVar rfl)
          (inProd (inVar rfl)
            (match nbi with
            | .ofP p' inP allQ =>
              inUnL
                (inArbUn p'
                  (inIr
                    (inSome p'
                      (inIr (inVar rfl)
                        (inCall
                          (show (bisimDl.wfm bisimDl.consts.uniSetMap).defMem
                              (Pair.pair p p')
                            from wfm_uniSetMap_eq ▸ inP)
                          (inVar rfl))))
                    (inArbIr fun q' =>
                      inImpl fun hLhs =>
                        let ⟨pE, hIr⟩ := inSomeElim hLhs
                        let ⟨hVar, hUni⟩ := inIrElim hIr
                        let eqE: pE = q' := inVarElim hVar rfl
                        let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
                        let eqA: pA = q := inVarElim hA rfl
                        let inPos: (uniSetMap.call q).posMem q' :=
                          wfm_uniSetMap_eq ▸ (eqA ▸ hFn)
                        inCall
                          (inCall (allQ q' inPos).toDefMem (inVar rfl))
                          (inVar rfl))))
            | .ofQ q' inQ allP =>
              inUnR
                (inArbUn q'
                  (inIr
                    (inSome q'
                      (inIr (inVar rfl)
                        (inCall
                          (show (bisimDl.wfm bisimDl.consts.uniSetMap).defMem
                              (Pair.pair q q')
                            from wfm_uniSetMap_eq ▸ inQ)
                          (inVar rfl))))
                    (inArbIr fun p' =>
                      inImpl fun hLhs =>
                        let ⟨pE, hIr⟩ := inSomeElim hLhs
                        let ⟨hVar, hUni⟩ := inIrElim hIr
                        let eqE: pE = p' := inVarElim hVar rfl
                        let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
                        let eqA: pA = p := inVarElim hA rfl
                        let inPos: (uniSetMap.call p).posMem p' :=
                          wfm_uniSetMap_eq ▸ (eqA ▸ hFn)
                        inCall
                          (inCall (allP p' inPos).toDefMem (inVar rfl))
                          (inVar rfl)))))))))


def bisimDl.NonBisimPos.cycle (x: Nat) (elem: Pair): Prop :=
  x = bisimDl.consts.NonBisim ∧
  ∃ p q w, elem = .pair p (.pair q w) ∧ ¬ bisimDl.NonBisimPos p q

def bisimDl.NonBisimPos.cycleIsEmpty
  {x elem}
  (inCycle: bisimDl.NonBisimPos.cycle x elem)
  (cause: Cause Pair)
  (isCause: cause.IsWeakCause (bisimDl.getDef x) elem)
:
  bisimDl.IsCauseInapplicableExtended bisimDl.NonBisimPos.cycle cause
:=
  let ⟨xEq, P, Q, W, elemEq, notNbi⟩ := inCycle
  let ins:
    (bisimDl.getDef bisimDl.consts.NonBisim).triIntp2Pos
      []
      cause.maximalBackgroundApx
      cause.maximalContextApx
      (.pair P (.pair Q W))
  :=
    elemEq ▸ xEq ▸ isCause cause.maximalValsApxAreSat
  let ⟨pAlias, ins⟩ := inArbUnElim ins
  let ⟨qAlias, ins⟩ := inArbUnElim ins
  let ⟨leftP, ins⟩ := inProdElim ins
  let ⟨leftQ, ins⟩ := inProdElim ins
  let pEq: pAlias = P := (inVarElim leftP rfl).symm
  let qEq: qAlias = Q := (inVarElim leftQ rfl).symm
  match inUnElim ins with
  | .inl ins =>
    let ⟨p', ins⟩ := inArbUnElim ins
    let ⟨insSome, insArbIr⟩ := inIrElim ins
    let ⟨p'Alias, insIr⟩ := inSomeElim insSome
    let ⟨insVar, insCall⟩ := inIrElim insIr
    let p'AliasEq: p'Alias = p' := inVarElim insVar rfl
    let insAtP: cause.cins bisimDl.consts.uniSetMap (P.pair p') :=
      pEq ▸ p'AliasEq ▸ inCallElimSingle insCall rfl
    match Classical.em ((uniSetMap.call P).posMem p') with
    | .inr notPos =>
      .blockedCinsOut insAtP
        (DefList.Out.isComplete
          (show ¬ (bisimDl.wfm bisimDl.consts.uniSetMap).posMem (P.pair p')
            from wfm_uniSetMap_eq ▸ notPos))
    | .inl posP' =>
      let notAll:
        ¬ ∀ q', (uniSetMap.call Q).defMem q' → NonBisimPos p' q'
      :=
        fun allQ => notNbi (NonBisimPos.ofP p' posP' allQ)
      let ⟨q', hq⟩ := Classical.not_forall.mp notAll
      let ⟨defQ, notNbi'⟩ := Classical.not_imp.mp hq
      match inUnElim (inArbIrElim insArbIr q') with
      | .inl ins =>
        let bout: cause.bout bisimDl.consts.uniSetMap (qAlias.pair q') :=
          Classical.byContradiction fun notBout =>
            ins (inSome q' (inIr rfl (inCall notBout rfl)))
        .blockedBout bout
          (DefList.Ins.isComplete
            (show (bisimDl.wfm bisimDl.consts.uniSetMap).defMem (qAlias.pair q')
              from wfm_uniSetMap_eq ▸ (qEq ▸ defQ: uniSetMap.defMem (qAlias.pair q'))))
      | .inr ins =>
        let ins := inCallElimSingle ins rfl
        let ins := inCallElimSingle ins rfl
        .blockedCinsCycle ins ⟨rfl, p', q', _, rfl, notNbi'⟩
  | .inr ins =>
    let ⟨q', ins⟩ := inArbUnElim ins
    let ⟨insSome, insArbIr⟩ := inIrElim ins
    let ⟨q'Alias, insIr⟩ := inSomeElim insSome
    let ⟨insVar, insCall⟩ := inIrElim insIr
    let q'AliasEq: q'Alias = q' := inVarElim insVar rfl
    let insAtQ: cause.cins bisimDl.consts.uniSetMap (Q.pair q') :=
      qEq ▸ q'AliasEq ▸ inCallElimSingle insCall rfl
    match Classical.em ((uniSetMap.call Q).posMem q') with
    | .inr notPos =>
      .blockedCinsOut insAtQ
        (DefList.Out.isComplete
          (show ¬ (bisimDl.wfm bisimDl.consts.uniSetMap).posMem (Q.pair q')
            from wfm_uniSetMap_eq ▸ notPos))
    | .inl posQ' =>
      let notAll:
        ¬ ∀ p', (uniSetMap.call P).defMem p' → NonBisimPos p' q'
      :=
        fun allP => notNbi (NonBisimPos.ofQ q' posQ' allP)
      let ⟨p', hp⟩ := Classical.not_forall.mp notAll
      let ⟨defP, notNbi'⟩ := Classical.not_imp.mp hp
      match inUnElim (inArbIrElim insArbIr p') with
      | .inl ins =>
        let bout: cause.bout bisimDl.consts.uniSetMap (pAlias.pair p') :=
          Classical.byContradiction fun notBout =>
            ins (inSome p' (inIr rfl (inCall notBout rfl)))
        .blockedBout bout
          (DefList.Ins.isComplete
            (show (bisimDl.wfm bisimDl.consts.uniSetMap).defMem (pAlias.pair p')
              from wfm_uniSetMap_eq ▸ (pEq ▸ defP: uniSetMap.defMem (pAlias.pair p'))))
      | .inr ins =>
        let ins := inCallElimSingle ins rfl
        let ins := inCallElimSingle ins rfl
        .blockedCinsCycle ins ⟨rfl, p', q', _, rfl, notNbi'⟩

def bisimDl.NonBisimPos_of_posMem {p q w}
  (ins: ((bisimDl.vals.NonBisim.call p).call q).posMem w)
:
  NonBisimPos p q
:=
  Classical.byContradiction fun notNbi =>
    let out:
      bisimDl.Out bisimDl.consts.NonBisim (.pair p (.pair q w))
    :=
      DefList.Out.intro3
        bisimDl.NonBisimPos.cycle
        NonBisimPos.cycleIsEmpty
        ⟨rfl, p, q, w, rfl, notNbi⟩
    out.isSound
      (show (bisimDl.wfm bisimDl.consts.NonBisim).posMem (.pair p (.pair q w))
        from ins)

def bisimDl.NonBisimPos.toPosMem {p q w}
  (nbi: NonBisimPos p q)
:
  ((bisimDl.vals.NonBisim.call p).call q).posMem w
:=
  DefList.InWfm.of_in_def_no_fv (lane := .posLane)
    (inArbUn p
      (inArbUn q
        (inProd (inVar rfl)
          (inProd (inVar rfl)
            (match nbi with
            | .ofP p' inP allQ =>
              inUnL
                (inArbUn p'
                  (inIr
                    (inSome p'
                      (inIr (inVar rfl)
                        (inCall
                          (show (bisimDl.wfm bisimDl.consts.uniSetMap).posMem
                              (Pair.pair p p')
                            from wfm_uniSetMap_eq ▸ inP)
                          (inVar rfl))))
                    (inArbIr fun q' =>
                      inImpl fun hLhs =>
                        let ⟨pE, hIr⟩ := inSomeElim hLhs
                        let ⟨hVar, hUni⟩ := inIrElim hIr
                        let eqE: pE = q' := inVarElim hVar rfl
                        let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
                        let eqA: pA = q := inVarElim hA rfl
                        let inDef: (uniSetMap.call q).defMem q' :=
                          wfm_uniSetMap_eq ▸ (eqA ▸ hFn)
                        inCall
                          (inCall (allQ q' inDef).toPosMem (inVar rfl))
                          (inVar rfl))))
            | .ofQ q' inQ allP =>
              inUnR
                (inArbUn q'
                  (inIr
                    (inSome q'
                      (inIr (inVar rfl)
                        (inCall
                          (show (bisimDl.wfm bisimDl.consts.uniSetMap).posMem
                              (Pair.pair q q')
                            from wfm_uniSetMap_eq ▸ inQ)
                          (inVar rfl))))
                    (inArbIr fun p' =>
                      inImpl fun hLhs =>
                        let ⟨pE, hIr⟩ := inSomeElim hLhs
                        let ⟨hVar, hUni⟩ := inIrElim hIr
                        let eqE: pE = p' := inVarElim hVar rfl
                        let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
                        let eqA: pA = p := inVarElim hA rfl
                        let inDef: (uniSetMap.call p).defMem p' :=
                          wfm_uniSetMap_eq ▸ (eqA ▸ hFn)
                        inCall
                          (inCall (allP p' inDef).toPosMem (inVar rfl))
                          (inVar rfl)))))))))

/-
  ## Section: lifting the Lean-native defs to the bisimilarity quotient

  Since bisimilar pre-trisets have matching definite and possible
  elements (up to bisimilarity), and `NonBisimDef` only inspects
  membership through those two lanes, it respects bisimilarity in
  both arguments.
-/

def bisimDl.NonBisimDef.respectsBisim:
  {p q p' q': Pair} →
  NonBisimDef p q →
  Set3Pair.Bisim p p' →
  Set3Pair.Bisim q q' →
  NonBisimDef p' q'
|
  _p, _q, _p', _q', .ofP pp insP allQ, ⟨R, isBisimP, Rpp'⟩, qBisim =>
    let ⟨pp', insP', RppPp'⟩ := isBisimP.left .ins _ _ pp Rpp' insP
    .ofP pp' insP' fun qq' inwQ' =>
      let ⟨Rq, isBisimQ, Rqq'⟩ := qBisim
      let ⟨qq, inwQ, RqqQq'⟩ := isBisimQ.right .inw _ _ qq' Rqq' inwQ'
      (allQ qq inwQ).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩
|
  _p, _q, _p', _q', .ofQ qq insQ allP, pBisim, ⟨Rq, isBisimQ, Rqq'⟩ =>
    let ⟨qq', insQ', RqqQq'⟩ := isBisimQ.left .ins _ _ qq Rqq' insQ
    .ofQ qq' insQ' fun pp' inwP' =>
      let ⟨R, isBisimP, Rpp'⟩ := pBisim
      let ⟨pp, inwP, RppPp'⟩ := isBisimP.right .inw _ _ pp' Rpp' inwP'
      (allP pp inwP).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩

def bisimDl.NonBisimPos.respectsBisim:
  {p q p' q': Pair} →
  NonBisimPos p q →
  Set3Pair.Bisim p p' →
  Set3Pair.Bisim q q' →
  NonBisimPos p' q'
|
  _p, _q, _p', _q', .ofP pp inwP allQ, ⟨R, isBisimP, Rpp'⟩, qBisim =>
    let ⟨pp', inwP', RppPp'⟩ := isBisimP.left .inw _ _ pp Rpp' inwP
    .ofP pp' inwP' fun qq' insQ' =>
      let ⟨Rq, isBisimQ, Rqq'⟩ := qBisim
      let ⟨qq, insQ, RqqQq'⟩ := isBisimQ.right .ins _ _ qq' Rqq' insQ'
      (allQ qq insQ).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩
|
  _p, _q, _p', _q', .ofQ qq inwQ allP, pBisim, ⟨Rq, isBisimQ, Rqq'⟩ =>
    let ⟨qq', inwQ', RqqQq'⟩ := isBisimQ.left .inw _ _ qq Rqq' inwQ
    .ofQ qq' inwQ' fun pp' insP' =>
      let ⟨R, isBisimP, Rpp'⟩ := pBisim
      let ⟨pp, insP, RppPp'⟩ := isBisimP.right .ins _ _ pp' Rpp' insP'
      (allP pp insP).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩


def Triset.NonBisimDef (a b: Set3Pair.Triset) :=
  let respects
    a0 b0 a1 b1
    (aBisim: Set3Pair.trisetSetoid.r a0 a1)
    (bBisim: Set3Pair.trisetSetoid.r b0 b1)
  :
    bisimDl.NonBisimDef a0 b0 = bisimDl.NonBisimDef a1 b1
  :=
    propext (Iff.intro
      (fun nbi => nbi.respectsBisim aBisim bBisim)
      (fun nbi =>
        nbi.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm aBisim)
          (Set3Pair.trisetSetoid.iseqv.symm bBisim)))
  Quotient.lift₂ bisimDl.NonBisimDef respects a b

def Triset.NonBisimPos (a b: Set3Pair.Triset) :=
  let respects
    a0 b0 a1 b1
    (aBisim: Set3Pair.trisetSetoid.r a0 a1)
    (bBisim: Set3Pair.trisetSetoid.r b0 b1)
  :
    bisimDl.NonBisimPos a0 b0 = bisimDl.NonBisimPos a1 b1
  :=
    propext (Iff.intro
      (fun nbi => nbi.respectsBisim aBisim bBisim)
      (fun nbi =>
        nbi.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm aBisim)
          (Set3Pair.trisetSetoid.iseqv.symm bBisim)))
  Quotient.lift₂ bisimDl.NonBisimPos respects a b


/-
  ## Section: the `IsBisim` lanes

  `IsBisim` is the complement of `NonBisim`. Respecting bisimilarity
  is preserved under negation, so both lanes lift to the quotient.
-/

def bisimDl.IsBisimDef.respectsBisim {p q p' q': Pair}
  (isB: IsBisimDef p q)
  (pBisim: Set3Pair.Bisim p p')
  (qBisim: Set3Pair.Bisim q q')
:
  IsBisimDef p' q'
:=
  fun nbi =>
    isB
      (nbi.respectsBisim
        (Set3Pair.trisetSetoid.iseqv.symm pBisim)
        (Set3Pair.trisetSetoid.iseqv.symm qBisim))

def bisimDl.IsBisimPos.respectsBisim {p q p' q': Pair}
  (isB: IsBisimPos p q)
  (pBisim: Set3Pair.Bisim p p')
  (qBisim: Set3Pair.Bisim q q')
:
  IsBisimPos p' q'
:=
  fun nbi =>
    isB
      (nbi.respectsBisim
        (Set3Pair.trisetSetoid.iseqv.symm pBisim)
        (Set3Pair.trisetSetoid.iseqv.symm qBisim))


def Triset.IsBisimDef (a b: Set3Pair.Triset) :=
  let respects
    a0 b0 a1 b1
    (aBisim: Set3Pair.trisetSetoid.r a0 a1)
    (bBisim: Set3Pair.trisetSetoid.r b0 b1)
  :
    bisimDl.IsBisimDef a0 b0 = bisimDl.IsBisimDef a1 b1
  :=
    propext (Iff.intro
      (fun isB => isB.respectsBisim aBisim bBisim)
      (fun isB =>
        isB.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm aBisim)
          (Set3Pair.trisetSetoid.iseqv.symm bBisim)))
  Quotient.lift₂ bisimDl.IsBisimDef respects a b

def Triset.IsBisimPos (a b: Set3Pair.Triset) :=
  let respects
    a0 b0 a1 b1
    (aBisim: Set3Pair.trisetSetoid.r a0 a1)
    (bBisim: Set3Pair.trisetSetoid.r b0 b1)
  :
    bisimDl.IsBisimPos a0 b0 = bisimDl.IsBisimPos a1 b1
  :=
    propext (Iff.intro
      (fun isB => isB.respectsBisim aBisim bBisim)
      (fun isB =>
        isB.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm aBisim)
          (Set3Pair.trisetSetoid.iseqv.symm bBisim)))
  Quotient.lift₂ bisimDl.IsBisimPos respects a b


/-
  ## Section: the `IsIn` lanes

  `IsIn set elem` says `elem` bisimulates some element of `set`.
-/

def bisimDl.IsInDef.respectsBisim {set elem set' elem': Pair}
  (isIn: IsInDef set elem)
  (setBisim: Set3Pair.Bisim set set')
  (elemBisim: Set3Pair.Bisim elem elem')
:
  IsInDef set' elem'
:=
  let ⟨elemX, isB, ins⟩ := isIn
  let ⟨R, isBisimSet, Rss'⟩ := setBisim
  let ⟨elemX', ins', RxX'⟩ := isBisimSet.left .ins _ _ elemX Rss' ins
  ⟨elemX', isB.respectsBisim elemBisim ⟨R, isBisimSet, RxX'⟩, ins'⟩

def bisimDl.IsInPos.respectsBisim {set elem set' elem': Pair}
  (isIn: IsInPos set elem)
  (setBisim: Set3Pair.Bisim set set')
  (elemBisim: Set3Pair.Bisim elem elem')
:
  IsInPos set' elem'
:=
  let ⟨elemX, isB, inw⟩ := isIn
  let ⟨R, isBisimSet, Rss'⟩ := setBisim
  let ⟨elemX', inw', RxX'⟩ := isBisimSet.left .inw _ _ elemX Rss' inw
  ⟨elemX', isB.respectsBisim elemBisim ⟨R, isBisimSet, RxX'⟩, inw'⟩


def Triset.IsInDef (set elem: Set3Pair.Triset) :=
  let respects
    s0 e0 s1 e1
    (sBisim: Set3Pair.trisetSetoid.r s0 s1)
    (eBisim: Set3Pair.trisetSetoid.r e0 e1)
  :
    bisimDl.IsInDef s0 e0 = bisimDl.IsInDef s1 e1
  :=
    propext (Iff.intro
      (fun isIn => isIn.respectsBisim sBisim eBisim)
      (fun isIn =>
        isIn.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm sBisim)
          (Set3Pair.trisetSetoid.iseqv.symm eBisim)))
  Quotient.lift₂ bisimDl.IsInDef respects set elem

def Triset.IsInPos (set elem: Set3Pair.Triset) :=
  let respects
    s0 e0 s1 e1
    (sBisim: Set3Pair.trisetSetoid.r s0 s1)
    (eBisim: Set3Pair.trisetSetoid.r e0 e1)
  :
    bisimDl.IsInPos s0 e0 = bisimDl.IsInPos s1 e1
  :=
    propext (Iff.intro
      (fun isIn => isIn.respectsBisim sBisim eBisim)
      (fun isIn =>
        isIn.respectsBisim
          (Set3Pair.trisetSetoid.iseqv.symm sBisim)
          (Set3Pair.trisetSetoid.iseqv.symm eBisim)))
  Quotient.lift₂ bisimDl.IsInPos respects set elem


/-
  ## Section: definite bisimilarity implies equality

  We show `IsBisimDef p q → Set3Pair.Bisim p q`, hence at the quotient
  level `Triset.IsBisimDef ts0 ts1 → ts0 = ts1`.

  Note this needs NEITHER the requested `IsBisimPos` hypothesis NOR any
  (hereditary) classicality assumption. The reason: `IsBisimDef` unfolds
  (classically) to the statement that every *possible* element of `p` is
  matched by a *definite* element of `q` (and symmetrically). That is a
  strictly stronger requirement than a bisimulation needs, so `IsBisimDef`
  is itself a bisimulation, i.e. definite bisimilarity is contained in
  exact bisimilarity. The `Hc` hypothesis only becomes relevant for the
  converse direction (`Bisim → IsBisimDef`), which fails in general but
  holds for hereditarily classical trisets.

  The `IsBisimPos ↔ IsBisimDef ↔ Eq` collapse for hereditarily classical
  trisets is proved in the next section (`Triset.hc_isBisimPos_iff_eq`);
  `toEq` supplies its `IsBisimDef → Eq` half.
-/

-- Every possible element of `p` is matched, via `IsBisimDef`, by some
-- definite element of `q`. (Contrapositive of `NonBisimPos.ofP`.)
def bisimDl.IsBisimDef.matchDef {p q p': Pair}
  (isBD: IsBisimDef p q)
  (posP: (uniSetMap.call p).posMem p')
:
  ∃ q', (uniSetMap.call q).defMem q' ∧ IsBisimDef p' q'
:=
  Classical.byContradiction fun h =>
    isBD (NonBisimPos.ofP p' posP fun q' defQ =>
      Classical.byContradiction fun notNbi => h ⟨q', defQ, notNbi⟩)

-- The symmetric statement. (Contrapositive of `NonBisimPos.ofQ`.)
def bisimDl.IsBisimDef.matchDef' {p q q': Pair}
  (isBD: IsBisimDef p q)
  (posQ: (uniSetMap.call q).posMem q')
:
  ∃ p', (uniSetMap.call p).defMem p' ∧ IsBisimDef p' q'
:=
  Classical.byContradiction fun h =>
    isBD (NonBisimPos.ofQ q' posQ fun p' defP =>
      Classical.byContradiction fun notNbi => h ⟨p', defP, notNbi⟩)

-- `IsBisimDef` is itself a bisimulation, so it is contained in `Bisim`.
def bisimDl.IsBisimDef.toBisim {p q: Pair}
  (isBD: IsBisimDef p q)
:
  Set3Pair.Bisim p q
:=
  ⟨
    bisimDl.IsBisimDef,
    ⟨
      fun l a _b a' isB trans =>
        match l, trans with
        | .ins, trans =>
          let transPos: (uniSetMap.call a).posMem a' :=
            (show (uniSetMap.call a).defMem a' from trans).toPos
          let ⟨b', defB, isB'⟩ := bisimDl.IsBisimDef.matchDef isB transPos
          ⟨b', defB, isB'⟩
        | .inw, trans =>
          let transPos: (uniSetMap.call a).posMem a' := trans
          let ⟨b', defB, isB'⟩ := bisimDl.IsBisimDef.matchDef isB transPos
          ⟨b', defB.toPos, isB'⟩,
      fun l a _b a' isB trans =>
        match l, trans with
        | .ins, trans =>
          let transPos: (uniSetMap.call a).posMem a' :=
            (show (uniSetMap.call a).defMem a' from trans).toPos
          let ⟨b', defB, isB'⟩ := bisimDl.IsBisimDef.matchDef' isB transPos
          ⟨b', defB, isB'⟩
        | .inw, trans =>
          let transPos: (uniSetMap.call a).posMem a' := trans
          let ⟨b', defB, isB'⟩ := bisimDl.IsBisimDef.matchDef' isB transPos
          ⟨b', defB.toPos, isB'⟩,
    ⟩,
    isBD,
  ⟩

-- Bisimilar pre-trisets are equal in the quotient.
def Triset.IsBisimDef.toEq {ts0 ts1: Set3Pair.Triset}
  (isBisim: Triset.IsBisimDef ts0 ts1)
:
  ts0 = ts1
:=
  Quotient.inductionOn₂
    (motive := fun t0 t1 => Triset.IsBisimDef t0 t1 → t0 = t1)
    ts0 ts1
    (fun _p _q isBD => Quot.sound (bisimDl.IsBisimDef.toBisim isBD))
    isBisim


/-
  ## Section: `IsBisimPos` collapses to `IsBisimDef` (hence `Eq`) on Hc trisets

  `IsBisimDef` always implies `IsBisimPos`: definite bisimilarity is the
  stronger relation. The converse fails in general — a possible-only
  element has no definite counterpart to be matched against, so
  `IsBisimPos` cannot upgrade its witnesses. For hereditarily classical
  trisets there are no such elements: every possible element is definite
  (up to bisimilarity) and is itself hereditarily classical. Hence both
  lanes coincide there, and by `toEq` both coincide with equality:

    `Hc ts0 → Hc ts1 → (IsBisimPos ts0 ts1 ↔ IsBisimDef ts0 ts1 ↔ ts0 = ts1)`.
-/

-- Transporting a definite/possible transition across a bisimulation.
def Set3Pair.Bisim.symm {a b: Set3Pair.PreTriset}
  (bisim: Set3Pair.Bisim a b)
:
  Set3Pair.Bisim b a
:=
  Set3Pair.trisetSetoid.iseqv.symm bisim

def Set3Pair.Bisim.ins {a b x: Set3Pair.PreTriset}
  (bisim: Set3Pair.Bisim a b)
  (ins: Set3Pair.PreTriset.Ins a x)
:
  ∃ y, Set3Pair.PreTriset.Ins b y ∧ Set3Pair.Bisim x y
:=
  let ⟨R, isBisim, Rab⟩ := bisim
  let ⟨y, insY, Rxy⟩ := isBisim.left .ins a b x Rab ins
  ⟨y, insY, R, isBisim, Rxy⟩

def Set3Pair.Bisim.inw {a b x: Set3Pair.PreTriset}
  (bisim: Set3Pair.Bisim a b)
  (inw: Set3Pair.PreTriset.Inw a x)
:
  ∃ y, Set3Pair.PreTriset.Inw b y ∧ Set3Pair.Bisim x y
:=
  let ⟨R, isBisim, Rab⟩ := bisim
  let ⟨y, inwY, Rxy⟩ := isBisim.left .inw a b x Rab inw
  ⟨y, inwY, R, isBisim, Rxy⟩


-- `NonBisimDef` is the stronger lane: it always entails `NonBisimPos`.
def bisimDl.NonBisimDef.toNonBisimPos:
  {p q: Pair} → NonBisimDef p q → NonBisimPos p q
| _, _, .ofP p' inP allQ =>
    .ofP p' inP.toPos fun q' defQ => (allQ q' defQ.toPos).toNonBisimPos
| _, _, .ofQ q' inQ allP =>
    .ofQ q' inQ.toPos fun p' defP => (allP p' defP.toPos).toNonBisimPos

def bisimDl.IsBisimDef.toIsBisimPos {p q: Pair}
  (isBD: IsBisimDef p q)
:
  IsBisimPos p q
:=
  fun nbd => isBD nbd.toNonBisimPos


-- Bisimilar pre-trisets are never `NonBisimDef`, so `Bisim ⊆ IsBisimPos`.
def bisimDl.NonBisimDef.not_bisim:
  {p q: Pair} → NonBisimDef p q → ¬ Set3Pair.Bisim p q
| _, _, .ofP _p' inP allQ, bisim =>
    let ⟨q', insQ', bisimP'Q'⟩ := bisim.ins inP
    (allQ q' insQ'.toPos).not_bisim bisimP'Q'
| _, _, .ofQ _q' inQ allP, bisim =>
    let ⟨p', insP', bisimQ'P'⟩ := bisim.symm.ins inQ
    (allP p' insP'.toPos).not_bisim bisimQ'P'.symm

def bisimDl.IsBisimPos.of_bisim {p q: Pair}
  (bisim: Set3Pair.Bisim p q)
:
  IsBisimPos p q
:=
  fun nbd => nbd.not_bisim bisim


-- On an Hc triset, every possible element is a definite element up to
-- bisimilarity. (If not, the pre-triset witnesses `Nhc` via `notClassical`.)
def Set3Pair.Triset.hc_ins_of_inw {p p': Set3Pair.PreTriset}
  (hc: Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p))
  (inw: Set3Pair.PreTriset.Inw p p')
:
  ∃ p'', Set3Pair.PreTriset.Ins p p'' ∧ Set3Pair.Bisim p' p''
:=
  Classical.byContradiction fun h =>
    hc (Set3Pair.Triset.Nhc.notClassical
      (elem := Quotient.mk Set3Pair.trisetSetoid p')
      ⟨p, p', rfl, rfl, inw⟩
      fun exIns =>
        let ⟨preTs, preElem, tsEq, elemEq, ins⟩ := exIns
        let bisimPre: Set3Pair.Bisim p preTs := Quotient.exact tsEq
        let bisimElem: Set3Pair.Bisim p' preElem := Quotient.exact elemEq
        let ⟨p'', insP'', bisimPreElem⟩ := bisimPre.symm.ins ins
        h ⟨p'', insP'',
          Set3Pair.trisetSetoid.iseqv.trans bisimElem bisimPreElem⟩)

-- On an Hc triset, every possible element is itself Hc.
-- (Otherwise the pre-triset witnesses `Nhc` via `containsNhc`.)
def Set3Pair.Triset.hc_hered {p p': Set3Pair.PreTriset}
  (hc: Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p))
  (inw: Set3Pair.PreTriset.Inw p p')
:
  Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p')
:=
  fun nhc' =>
    hc (Set3Pair.Triset.Nhc.containsNhc ⟨p, p', rfl, rfl, inw⟩ nhc')


-- On Hc trisets possible non-bisimilarity implies the definite one.
def bisimDl.NonBisimPos.toNonBisimDef:
  {p q: Pair} →
  NonBisimPos p q →
  Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p) →
  Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid q) →
  NonBisimDef p q
| _p, _q, .ofP _p' inwP allQ, hcP, hcQ =>
    let ⟨p'', insP'', bisimP'⟩ := Set3Pair.Triset.hc_ins_of_inw hcP inwP
    .ofP p'' insP'' fun _q' inwQ' =>
      let ⟨q'', insQ'', bisimQ'⟩ := Set3Pair.Triset.hc_ins_of_inw hcQ inwQ'
      let hcP' := Set3Pair.Triset.hc_hered hcP inwP
      let hcQ' := Set3Pair.Triset.hc_hered hcQ inwQ'
      let hcQ'':
        Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid q'')
      :=
        (@Quotient.sound _ Set3Pair.trisetSetoid _ _ bisimQ') ▸ hcQ'
      let nbd := (allQ q'' insQ'').toNonBisimDef hcP' hcQ''
      nbd.respectsBisim bisimP' bisimQ'.symm
| _p, _q, .ofQ _q' inwQ allP, hcP, hcQ =>
    let ⟨q'', insQ'', bisimQ'⟩ := Set3Pair.Triset.hc_ins_of_inw hcQ inwQ
    .ofQ q'' insQ'' fun _p' inwP' =>
      let ⟨p'', insP'', bisimP'⟩ := Set3Pair.Triset.hc_ins_of_inw hcP inwP'
      let hcQ' := Set3Pair.Triset.hc_hered hcQ inwQ
      let hcP' := Set3Pair.Triset.hc_hered hcP inwP'
      let hcP'':
        Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p'')
      :=
        (@Quotient.sound _ Set3Pair.trisetSetoid _ _ bisimP') ▸ hcP'
      let nbd := (allP p'' insP'').toNonBisimDef hcP'' hcQ'
      nbd.respectsBisim bisimP'.symm bisimQ'

def bisimDl.IsBisimPos.toIsBisimDef {p q: Pair}
  (hcP: Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid p))
  (hcQ: Set3Pair.Triset.Hc (Quotient.mk Set3Pair.trisetSetoid q))
  (isBP: IsBisimPos p q)
:
  IsBisimDef p q
:=
  fun nbp => isBP (nbp.toNonBisimDef hcP hcQ)


-- Lifting the collapse to the quotient, and packaging the equivalences.
def Triset.IsBisimDef.toIsBisimPos {ts0 ts1: Set3Pair.Triset}
  (isBD: Triset.IsBisimDef ts0 ts1)
:
  Triset.IsBisimPos ts0 ts1
:=
  Quotient.inductionOn₂
    (motive :=
      fun t0 t1 => Triset.IsBisimDef t0 t1 → Triset.IsBisimPos t0 t1)
    ts0 ts1
    (fun _p _q h => bisimDl.IsBisimDef.toIsBisimPos h)
    isBD

def Triset.IsBisimPos.toIsBisimDef {ts0 ts1: Set3Pair.Triset}
  (hc0: Set3Pair.Triset.Hc ts0)
  (hc1: Set3Pair.Triset.Hc ts1)
  (isBP: Triset.IsBisimPos ts0 ts1)
:
  Triset.IsBisimDef ts0 ts1
:=
  Quotient.inductionOn₂
    (motive := fun t0 t1 =>
      Set3Pair.Triset.Hc t0 →
      Set3Pair.Triset.Hc t1 →
      Triset.IsBisimPos t0 t1 →
      Triset.IsBisimDef t0 t1)
    ts0 ts1
    (fun _p _q hcp hcq h => bisimDl.IsBisimPos.toIsBisimDef hcp hcq h)
    hc0 hc1 isBP

def Triset.IsBisimPos.refl
  (ts: Set3Pair.Triset)
:
  Triset.IsBisimPos ts ts
:=
  Quotient.inductionOn
    (motive := fun t => Triset.IsBisimPos t t)
    ts
    (fun p =>
      let rflP := Set3Pair.trisetSetoid.iseqv.refl p
      bisimDl.IsBisimPos.of_bisim rflP)

def Triset.IsBisimDef.refl_of_hc {ts: Set3Pair.Triset}
  (hc: Set3Pair.Triset.Hc ts)
:
  Triset.IsBisimDef ts ts
:=
  (Triset.IsBisimPos.refl ts).toIsBisimDef hc hc


-- Assuming a hc triset, definite bisimilarity is equivalent to equality.
def Triset.hc_isBisimDef_iff_eq {ts0 ts1: Set3Pair.Triset}
  (hc0: Set3Pair.Triset.Hc ts0)
:
  Triset.IsBisimDef ts0 ts1 ↔ ts0 = ts1
:=
  Iff.intro
    Triset.IsBisimDef.toEq
    (fun eq => eq ▸ Triset.IsBisimDef.refl_of_hc hc0)

-- Assuming two hc trisets, possible bisimilarity is equivalent to
-- definite bisimilarity.
def Triset.hc_isBisimPos_iff_isBisimDef {ts0 ts1: Set3Pair.Triset}
  (hc0: Set3Pair.Triset.Hc ts0)
  (hc1: Set3Pair.Triset.Hc ts1)
:
  Triset.IsBisimPos ts0 ts1 ↔ Triset.IsBisimDef ts0 ts1
:=
  Iff.intro
    (fun isBP => isBP.toIsBisimDef hc0 hc1)
    Triset.IsBisimDef.toIsBisimPos

-- Assuming two hc trisets, possible bisimilarity is equivalent to
-- equality.
def Triset.hc_isBisimPos_iff_eq {ts0 ts1: Set3Pair.Triset}
  (hc0: Set3Pair.Triset.Hc ts0)
  (hc1: Set3Pair.Triset.Hc ts1)
:
  Triset.IsBisimPos ts0 ts1 ↔ ts0 = ts1
:=
  (Triset.hc_isBisimPos_iff_isBisimDef hc0 hc1).trans
    (Triset.hc_isBisimDef_iff_eq hc0)
