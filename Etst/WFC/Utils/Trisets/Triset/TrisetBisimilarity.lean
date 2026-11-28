/-
  Here we define WFC's notion of bisimilarity for the "sets" of WFC
  (ie. indices of uniSetMap quotiented by bisimilarity), and show
  the relation is well-defined on the quotient.
  
  The fuzzy notion of membership built on top of this bisimilarity
  is defined in `TrisetMembership.lean`.
  
  We show that
  - the definite-lane bisimilarity implies actual bisimilarity of
    pre-trisets (and therefore equality of trisets).
  - for hereditarily classical trisets, definite-lane bisimilarity
    equals possible-lane bisimilarity equals equality of trisets.
-/
module
public import Etst.WFC.Utils.MembershipPs.OutIntro3
public import Etst.WFC.Utils.Trisets.Triset.Triset
import Etst.WFC.Ch7_Polymorphism
import Etst.WFC.Utils.Cause

public section
namespace Etst
open Expr


exposed pairDefList bisimDl extends uniSetMapDl
  p3 NonBisim :=
    Ex p q,
    × p
    × q
    × (| (Ex p',
         & (?some p' & uniSetMap p)
         & (All q', (?some q' & uniSetMap q) -> NonBisim p' q'))
      | (Ex q',
         & (?some q' & uniSetMap q)
         & (All p', (?some p' & uniSetMap p) -> NonBisim p' q')))
  
  p3 IsBisim := Ex p q, p × q × (!NonBisim p q)
pairDefList.

-- A Lean-native definition of `NonBisim`.
inductive bisimDl.NonBisim (lane: Set3.Lane): (p q: Pair) → Prop where
| ofP {p q}
    (p': Pair)
    (inP: p' ∈ (uniSetMap.call p).getLane lane)
    (allQ:
      ∀ q',
        q' ∈ (uniSetMap.call q).getLane lane.toggle →
        bisimDl.NonBisim lane p' q')
  :
    bisimDl.NonBisim lane p q
| ofQ {p q}
    (q': Pair)
    (inQ: q' ∈ (uniSetMap.call q).getLane lane)
    (allP:
      ∀ p',
        p' ∈ (uniSetMap.call p).getLane lane.toggle →
        bisimDl.NonBisim lane p' q')
  :
    bisimDl.NonBisim lane p q

-- `NonBisim`'s definite-membership lane.
abbrev bisimDl.NonBisimDef := bisimDl.NonBisim .defLane

-- `NonBisim`'s possible-membership lane.
abbrev bisimDl.NonBisimPos := bisimDl.NonBisim .posLane

/-
  The two `IsBisim` lanes are the complements of `NonBisim` at the
  *opposite* lane: `!NonBisim` sits behind a complement, which flips
  the lane.
-/
exposed def bisimDl.IsBisimAt (lane: Set3.Lane) (p q: Pair): Prop :=
  ¬ bisimDl.NonBisim lane.toggle p q

abbrev bisimDl.IsBisimDef (p q: Pair): Prop := IsBisimAt .defLane p q
abbrev bisimDl.IsBisimPos (p q: Pair): Prop := IsBisimAt .posLane p q

/-
  ## Section: proving equivalence of the Lean-native WFM defs
  
  This section is write-once, read-never code. You have been warned.
-/
theorem bisimDl.wfm_uniSetMap_eq:
  bisimDl.val "uniSetMap" = uniSetMap
:=
  bisimDl.extend_wfm_eq uniSetMapDl "uniSetMap"

/-
  `wfm_uniSetMap_eq` in the shape the proofs below actually need.
-/
theorem bisimDl.mem_uniSetMap {lane p}:
  p ∈ (bisimDl.dl.wfm (bisimDl.const "uniSetMap")).getLane lane ↔
  p ∈ uniSetMap.getLane lane
:=
  Iff.of_eq (congrArg (fun s => p ∈ s.getLane lane) wfm_uniSetMap_eq)

theorem bisimDl.NonBisimDef_of_Ins {cst index p q w}
  (ins: bisimDl.dl.Ins cst index)
  (cstEq: cst = bisimDl.const "NonBisim")
  (indexEq: index = .pair p (.pair q w))
:
  NonBisimDef p q
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let ins:
      Set.Mem
        ((bisimDl.dl.getDef (bisimDl.const "NonBisim")).intp
          .defLane
          cause.leastBackgroundApx
          cause.leastContextApx
          [])
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
      let inP: p' ∈ (uniSetMap.call p).defMem :=
        (bisimDl.mem_uniSetMap (lane := .defLane)).mp
          (cinsSat insAtP).isSound
      .ofP p' inP fun q' inQ =>
        match inUnElim (inArbIrElim insArbIr q') with
        | .inl ins =>
          let notBout inBout :=
            (boutSat inBout).isSound
              (bisimDl.mem_uniSetMap.mpr (qEq ▸ inQ))
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
      let inQ: q' ∈ (uniSetMap.call q).defMem :=
        (bisimDl.mem_uniSetMap (lane := .defLane)).mp
          (cinsSat insAtQ).isSound
      .ofQ q' inQ fun p' inP =>
        match inUnElim (inArbIrElim insArbIr p') with
        | .inl ins =>
          let notBout inBout :=
            (boutSat inBout).isSound
              (bisimDl.mem_uniSetMap.mpr (pEq ▸ inP))
          False.elim <|
          ins (inSome p' (inIr rfl (inCall notBout rfl)))
        | .inr ins =>
          let ins := inCallElimSingle ins rfl
          let ins := inCallElimSingle ins rfl
          NonBisimDef_of_Ins (cinsSat ins) rfl rfl

theorem bisimDl.NonBisimDef_of_defMem {p q w}
  (ins: w ∈ (((bisimDl.val "NonBisim").call p).call q).defMem)
:
  NonBisimDef p q
:=
  NonBisimDef_of_Ins (DefList.Ins.isComplete ins) rfl rfl

theorem bisimDl.NonBisim.toMem {lane: Set3.Lane} {p q w}
  (nbi: bisimDl.NonBisim lane p q)
:
  w ∈ (((bisimDl.val "NonBisim").call p).call q).getLane lane
:=
  DefList.in_def_no_fv (lane := lane)
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
            (bisimDl.mem_uniSetMap.mpr inP)
            (inVar rfl))))
      (inArbIr fun q' =>
        inImpl fun hLhs =>
          let ⟨pE, hIr⟩ := inSomeElim hLhs
          let ⟨hVar, hUni⟩ := inIrElim hIr
          let eqE: pE = q' := inVarElim hVar rfl
          let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
          let eqA: pA = q := inVarElim hA rfl
          let inOther: q' ∈ (uniSetMap.call q).getLane lane.toggle :=
            (bisimDl.mem_uniSetMap (lane := lane.toggle)).mp (eqA ▸ hFn)
          inCall
            (inCall (allQ q' inOther).toMem (inVar rfl))
            (inVar rfl))))
  | .ofQ q' inQ allP =>
    inUnR
    (inArbUn q'
    (inIr
      (inSome q'
        (inIr (inVar rfl)
          (inCall
            ((bisimDl.mem_uniSetMap (lane := lane)).mpr inQ)
            (inVar rfl))))
      (inArbIr fun p' =>
        inImpl fun hLhs =>
          let ⟨pE, hIr⟩ := inSomeElim hLhs
          let ⟨hVar, hUni⟩ := inIrElim hIr
          let eqE: pE = p' := inVarElim hVar rfl
          let ⟨pA, hFn, hA⟩ := inCallElim (eqE ▸ hUni)
          let eqA: pA = p := inVarElim hA rfl
          let inOther: p' ∈ (uniSetMap.call p).getLane lane.toggle :=
            (bisimDl.mem_uniSetMap (lane := lane.toggle)).mp (eqA ▸ hFn)
          inCall
            (inCall (allP p' inOther).toMem (inVar rfl))
            (inVar rfl)))))))))


def bisimDl.NonBisimPos.cycle (x: Nat) (elem: Pair): Prop :=
  And
    (x = bisimDl.const "NonBisim")
    (∃ p q w, elem = .pair p (.pair q w) ∧ ¬ bisimDl.NonBisimPos p q)

theorem bisimDl.NonBisimPos.cycleIsEmpty
  {x elem}
  (inCycle: bisimDl.NonBisimPos.cycle x elem)
  (cause: Cause Pair)
  (isCause: cause.IsWeakCause (bisimDl.dl.getDef x) elem)
:
  bisimDl.dl.IsCauseInapplicableExtended bisimDl.NonBisimPos.cycle cause
:=
  let ⟨xEq, P, Q, W, elemEq, notNbi⟩ := inCycle
  let ins:
    Set.Mem
      ((bisimDl.dl.getDef (bisimDl.const "NonBisim")).intp
        .posLane
        cause.maximalBackgroundApx
        cause.maximalContextApx
        [])
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
    let insAtP: cause.cins (bisimDl.const "uniSetMap") (P.pair p') :=
      pEq ▸ p'AliasEq ▸ inCallElimSingle insCall rfl
    match Classical.em (p' ∈ (uniSetMap.call P).posMem) with
    | .inr notPos =>
      .blockedCinsOut insAtP
        (DefList.Out.isComplete fun h =>
          notPos ((bisimDl.mem_uniSetMap (lane := .posLane)).mp h))
    | .inl posP' =>
      let notAll:
        ¬ ∀ q' ∈ (uniSetMap.call Q).defMem, NonBisimPos p' q'
      :=
        fun allQ => notNbi (bisimDl.NonBisim.ofP p' posP' allQ)
      let ⟨q', hq⟩ := Classical.not_forall.mp notAll
      let ⟨defQ, notNbi'⟩ := Classical.not_imp.mp hq
      match inUnElim (inArbIrElim insArbIr q') with
      | .inl ins =>
        let bout: cause.bout (bisimDl.const "uniSetMap") (qAlias.pair q') :=
          Classical.byContradiction fun notBout =>
            ins (inSome q' (inIr rfl (inCall notBout rfl)))
        .blockedBout bout
          (DefList.Ins.isComplete
            (bisimDl.mem_uniSetMap.mpr (qEq ▸ defQ)))
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
    let insAtQ: cause.cins (bisimDl.const "uniSetMap") (Q.pair q') :=
      qEq ▸ q'AliasEq ▸ inCallElimSingle insCall rfl
    match Classical.em (q' ∈ (uniSetMap.call Q).posMem) with
    | .inr notPos =>
      .blockedCinsOut insAtQ
        (DefList.Out.isComplete fun h =>
          notPos ((bisimDl.mem_uniSetMap (lane := .posLane)).mp h))
    | .inl posQ' =>
      let notAll:
        ¬ ∀ p' ∈ (uniSetMap.call P).defMem, NonBisimPos p' q'
      :=
        fun allP => notNbi (bisimDl.NonBisim.ofQ q' posQ' allP)
      let ⟨p', hp⟩ := Classical.not_forall.mp notAll
      let ⟨defP, notNbi'⟩ := Classical.not_imp.mp hp
      match inUnElim (inArbIrElim insArbIr p') with
      | .inl ins =>
        let bout: cause.bout (bisimDl.const "uniSetMap") (pAlias.pair p') :=
          Classical.byContradiction fun notBout =>
            ins (inSome p' (inIr rfl (inCall notBout rfl)))
        .blockedBout bout
          (DefList.Ins.isComplete
            (bisimDl.mem_uniSetMap.mpr (pEq ▸ defP)))
      | .inr ins =>
        let ins := inCallElimSingle ins rfl
        let ins := inCallElimSingle ins rfl
        .blockedCinsCycle ins ⟨rfl, p', q', _, rfl, notNbi'⟩

theorem bisimDl.NonBisimPos_of_posMem {p q w}
  (ins: w ∈ (((bisimDl.val "NonBisim").call p).call q).posMem)
:
  NonBisimPos p q
:=
  Classical.byContradiction fun notNbi =>
    let out:
      bisimDl.dl.Out (bisimDl.const "NonBisim") (.pair p (.pair q w))
    :=
      DefList.Out.intro3
        bisimDl.NonBisimPos.cycle
        NonBisimPos.cycleIsEmpty
        ⟨rfl, p, q, w, rfl, notNbi⟩
    out.isSound ins

/-
  `NonBisim.toMem` above is lane-generic, but this direction is not:
  `Ins` is only complete for the definite lane, so the possible lane has
  to go through the `Out.intro3` cycle instead.
-/
theorem bisimDl.NonBisim_of_mem {lane: Set3.Lane} {p q w}
  (h: w ∈ (((bisimDl.val "NonBisim").call p).call q).getLane lane.toggle)
:
  bisimDl.NonBisim lane.toggle p q
:=
  match lane with
  | .defLane => bisimDl.NonBisimPos_of_posMem h
  | .posLane => bisimDl.NonBisimDef_of_defMem h

theorem bisimDl.IsBisimAt_of_mem {lane p q w}
  (h: w ∈ (((bisimDl.val "IsBisim").call p).call q).getLane lane)
:
  bisimDl.IsBisimAt lane p q
:=
  let h2 := DefList.in_def_body_no_fv (lane := lane) h
  let ⟨pA, h2⟩ := inArbUnElim h2
  let ⟨qA, h2⟩ := inArbUnElim h2
  let ⟨hP, h2⟩ := inProdElim h2
  let ⟨hQ, hCompl⟩ := inProdElim h2
  let pEq: pA = p := (inVarElim hP rfl).symm
  let qEq: qA = q := (inVarElim hQ rfl).symm
  fun nbp =>
    hCompl (inCall (inCall
      (pEq.symm ▸ qEq.symm ▸ nbp.toMem (w := w))
      (inVar rfl)) (inVar rfl))

theorem bisimDl.IsBisimAt.toMem {lane p q w}
  (isB: bisimDl.IsBisimAt lane p q)
:
  w ∈ (((bisimDl.val "IsBisim").call p).call q).getLane lane
:=
  DefList.in_def_no_fv (lane := lane)
  (inArbUn p
  (inArbUn q
  (inProd (inVar rfl)
  (inProd (inVar rfl)
  (inCompl fun hMem =>
    let ⟨pA1, hFn, hArg⟩ := inCallElim hMem
    let pA1Eq: pA1 = q := inVarElim hArg rfl
    let ⟨pA2, hFn2, hArg2⟩ := inCallElim (pA1Eq ▸ hFn)
    let pA2Eq: pA2 = p := inVarElim hArg2 rfl
    let hNbi := pA2Eq ▸ hFn2
    isB (NonBisim_of_mem hNbi))))))

theorem bisimDl.NonBisim.respectsBisim {lane: Set3.Lane}:
  {p q p' q': Pair} →
  bisimDl.NonBisim lane p q →
  Pair.PreTriset.IsBisim p p' →
  Pair.PreTriset.IsBisim q q' →
  bisimDl.NonBisim lane p' q'
|
  _p, _q, _p', _q', .ofP pp insP allQ, ⟨R, isBisimP, Rpp'⟩, qBisim =>
    let ⟨pp', insP', RppPp'⟩ := isBisimP.left lane _ _ pp Rpp' insP
    .ofP pp' insP' fun qq' insQ' =>
      let ⟨Rq, isBisimQ, Rqq'⟩ := qBisim
      let ⟨qq, insQ, RqqQq'⟩ :=
        isBisimQ.right lane.toggle _ _ qq' Rqq' insQ'
      (allQ qq insQ).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩
|
  _p, _q, _p', _q', .ofQ qq insQ allP, pBisim, ⟨Rq, isBisimQ, Rqq'⟩ =>
    let ⟨qq', insQ', RqqQq'⟩ := isBisimQ.left lane _ _ qq Rqq' insQ
    .ofQ qq' insQ' fun pp' insP' =>
      let ⟨R, isBisimP, Rpp'⟩ := pBisim
      let ⟨pp, insP, RppPp'⟩ :=
        isBisimP.right lane.toggle _ _ pp' Rpp' insP'
      (allP pp insP).respectsBisim
        ⟨R, isBisimP, RppPp'⟩ ⟨Rq, isBisimQ, RqqQq'⟩


/-
  ## Section: lifting the Lean-native defs to the bisimilarity quotient

  Since bisimilar pre-trisets have matching elements in either lane (up
  to bisimilarity), `NonBisim` respects bisimilarity in both arguments.
-/

-- Lifting a relation on representatives to the bisimilarity quotient.
exposed def Triset.liftBisim (P: Pair → Pair → Prop)
  (respects:
    ∀ {a0 b0 a1 b1},
      Pair.PreTriset.setoid.r a0 a1 →
      Pair.PreTriset.setoid.r b0 b1 →
      P a0 b0 → P a1 b1)
:
  Pair.Triset → Pair.Triset → Prop
:=
  Quotient.lift₂ P
    (fun _a0 _b0 _a1 _b1 aBisim bBisim =>
      propext (Iff.intro
        (fun p => respects aBisim bBisim p)
        (fun p =>
          respects
            (Pair.PreTriset.setoid.iseqv.symm aBisim)
            (Pair.PreTriset.setoid.iseqv.symm bBisim)
            p)))

exposed def Triset.NonBisimDef: Pair.Triset → Pair.Triset → Prop :=
  Triset.liftBisim bisimDl.NonBisimDef
    (fun aBisim bBisim nbi => nbi.respectsBisim aBisim bBisim)

exposed def Triset.NonBisimPos: Pair.Triset → Pair.Triset → Prop :=
  Triset.liftBisim bisimDl.NonBisimPos
    (fun aBisim bBisim nbi => nbi.respectsBisim aBisim bBisim)


/-
  ## Section: the `IsBisim` lanes

  `IsBisim` is the complement of `NonBisim`. Respecting bisimilarity
  is preserved under negation, so both lanes lift to the quotient.
-/

theorem bisimDl.IsBisimAt.respectsBisim {lane: Set3.Lane} {p q p' q': Pair}
  (isB: bisimDl.IsBisimAt lane p q)
  (pBisim: Pair.PreTriset.IsBisim p p')
  (qBisim: Pair.PreTriset.IsBisim q q')
:
  bisimDl.IsBisimAt lane p' q'
:=
  fun nbi =>
    isB
      (nbi.respectsBisim
        (Pair.PreTriset.setoid.iseqv.symm pBisim)
        (Pair.PreTriset.setoid.iseqv.symm qBisim))

exposed def Triset.IsBisimDef: Pair.Triset → Pair.Triset → Prop :=
  Triset.liftBisim bisimDl.IsBisimDef
    (fun aBisim bBisim isB => isB.respectsBisim aBisim bBisim)

exposed def Triset.IsBisimPos: Pair.Triset → Pair.Triset → Prop :=
  Triset.liftBisim bisimDl.IsBisimPos
    (fun aBisim bBisim isB => isB.respectsBisim aBisim bBisim)


/-
  ## Section: definite bisimilarity implies equality

  We show `IsBisimDef p q → Pair.PreTriset.IsBisim p q`, hence at the
  quotient level `Triset.IsBisimDef ts0 ts1 → ts0 = ts1`.
-/

-- Every possible element of `p` is matched, via `IsBisimDef`, by some
-- definite element of `q`. (Contrapositive of `NonBisimPos.ofP`.)
theorem bisimDl.IsBisimAt.matchDef {p q p': Pair}
  (isBD: IsBisimAt .defLane p q)
  (posP: p' ∈ (uniSetMap.call p).posMem)
:
  ∃ q' ∈ (uniSetMap.call q).defMem, IsBisimAt .defLane p' q'
:=
  Classical.byContradiction fun h =>
    isBD (bisimDl.NonBisim.ofP p' posP fun q' defQ =>
      Classical.byContradiction fun notNbi => h ⟨q', defQ, notNbi⟩)

-- The symmetric statement. (Contrapositive of `NonBisimPos.ofQ`.)
theorem bisimDl.IsBisimAt.matchDef' {p q q': Pair}
  (isBD: IsBisimAt .defLane p q)
  (posQ: q' ∈ (uniSetMap.call q).posMem)
:
  ∃ p' ∈ (uniSetMap.call p).defMem, IsBisimAt .defLane p' q'
:=
  Classical.byContradiction fun h =>
    isBD (bisimDl.NonBisim.ofQ q' posQ fun p' defP =>
      Classical.byContradiction fun notNbi => h ⟨p', defP, notNbi⟩)

-- `IsBisimDef` is itself a bisimulation, so it is contained in `Bisim`.
theorem bisimDl.IsBisimAt.toBisim {p q: Pair}
  (isBD: IsBisimAt .defLane p q)
:
  Pair.PreTriset.IsBisim p q
:=
  ⟨
    bisimDl.IsBisimDef,
    ⟨
      fun l _ _ _ isB trans =>
        match l, trans with
        | .defLane, trans =>
          let ⟨b', defB, isB'⟩ :=
            bisimDl.IsBisimAt.matchDef isB (Set3.defToPos trans)
          ⟨b', defB, isB'⟩
        | .posLane, trans =>
          let ⟨b', defB, isB'⟩ :=
            bisimDl.IsBisimAt.matchDef isB trans
          ⟨b', Set3.defToPos defB, isB'⟩,
      fun l _ _ _ isB trans =>
        match l, trans with
        | .defLane, trans =>
          let ⟨b', defB, isB'⟩ :=
            bisimDl.IsBisimAt.matchDef' isB (Set3.defToPos trans)
          ⟨b', defB, isB'⟩
        | .posLane, trans =>
          let ⟨b', defB, isB'⟩ :=
            bisimDl.IsBisimAt.matchDef' isB trans
          ⟨b', Set3.defToPos defB, isB'⟩,
    ⟩,
    isBD,
  ⟩

-- Bisimilar pre-trisets are equal in the quotient.
theorem Triset.IsBisimDef.toEq {ts0 ts1: Pair.Triset}
  (isBisim: Triset.IsBisimDef ts0 ts1)
:
  ts0 = ts1
:=
  Quotient.inductionOn₂
    (motive := fun t0 t1 => Triset.IsBisimDef t0 t1 → t0 = t1)
    ts0 ts1
    (fun _p _q isBD => Quot.sound (bisimDl.IsBisimAt.toBisim isBD))
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

-- Transporting a membership across a bisimulation.
theorem Pair.PreTriset.IsBisim.symm {a b: Pair.PreTriset}
  (bisim: Pair.PreTriset.IsBisim a b)
:
  Pair.PreTriset.IsBisim b a
:=
  Pair.PreTriset.setoid.iseqv.symm bisim

theorem Pair.PreTriset.IsBisim.has {lane}
  {a b x: Pair.PreTriset}
  (bisim: a.IsBisim b)
  (has: a.Has lane x)
:
  ∃ y, b.Has lane y ∧ Pair.PreTriset.IsBisim x y
:=
  let ⟨R, isBisim, Rab⟩ := bisim
  let ⟨y, hasY, Rxy⟩ := isBisim.left lane a b x Rab has
  ⟨y, hasY, R, isBisim, Rxy⟩


-- `NonBisimDef` is the stronger lane: it always entails `NonBisimPos`.
theorem bisimDl.NonBisim.toNonBisimPos:
  {p q: Pair} → NonBisimDef p q → NonBisimPos p q
| _, _, .ofP p' inP allQ =>
    .ofP
      p'
      (Set3.defToPos inP)
      fun q' defQ => (allQ q' (Set3.defToPos defQ)).toNonBisimPos
| _, _, .ofQ q' inQ allP =>
    .ofQ
      q'
      (Set3.defToPos inQ)
      fun p' defP => (allP p' (Set3.defToPos defP)).toNonBisimPos

theorem bisimDl.IsBisimAt.toIsBisimPos {p q: Pair}
  (isBD: IsBisimAt .defLane p q)
:
  IsBisimAt .posLane p q
:=
  fun nbd => isBD nbd.toNonBisimPos


-- Bisimilar pre-trisets are never `NonBisimDef`, so `IsBisim ⊆ IsBisimPos`.
theorem bisimDl.NonBisim.not_bisim:
  {p q: Pair} → NonBisimDef p q → ¬ Pair.PreTriset.IsBisim p q
| _, _, .ofP _p' inP allQ, bisim =>
    let ⟨q', insQ', bisimP'Q'⟩ := bisim.has (lane := .defLane) inP
    (allQ q' (Set3.defToPos insQ')).not_bisim bisimP'Q'
| _, _, .ofQ _q' inQ allP, bisim =>
    let ⟨p', insP', bisimQ'P'⟩ := bisim.symm.has (lane := .defLane) inQ
    (allP p' (Set3.defToPos insP')).not_bisim bisimQ'P'.symm

theorem bisimDl.IsBisimPos.of_bisim {p q: Pair}
  (bisim: Pair.PreTriset.IsBisim p q)
:
  IsBisimPos p q
:=
  fun nbd => nbd.not_bisim bisim


-- On an Hc triset, every possible element is a definite element up to
-- bisimilarity.
theorem Pair.Triset.hc_ins_of_inw {p p': Pair.PreTriset}
  (hc: Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p))
  (inw: Pair.PreTriset.Inw p p')
:
  ∃ p'', Pair.PreTriset.Ins p p'' ∧ Pair.PreTriset.IsBisim p' p''
:=
  Classical.byContradiction fun h =>
    hc (Pair.Triset.Nhc.notClassical
      (elem := Quotient.mk Pair.PreTriset.setoid p')
      ⟨p, p', rfl, rfl, inw⟩
      fun exIns =>
        let ⟨preTs, preElem, tsEq, elemEq, ins⟩ := exIns
        let bisimPre: Pair.PreTriset.IsBisim p preTs := Quotient.exact tsEq
        let bisimElem: Pair.PreTriset.IsBisim p' preElem := Quotient.exact elemEq
        let ⟨p'', insP'', bisimPreElem⟩ := bisimPre.symm.has ins
        h ⟨p'', insP'',
          Pair.PreTriset.setoid.iseqv.trans bisimElem bisimPreElem⟩)

-- On an Hc triset, every possible element is itself Hc.
theorem Pair.Triset.hc_hered {p p': Pair.PreTriset}
  (hc: Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p))
  (inw: Pair.PreTriset.Inw p p')
:
  Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p')
:=
  fun nhc' =>
    hc (Pair.Triset.Nhc.containsNhc ⟨p, p', rfl, rfl, inw⟩ nhc')


-- On Hc trisets possible non-bisimilarity implies the definite one.
theorem bisimDl.NonBisim.toNonBisimDef:
  {p q: Pair} →
  NonBisimPos p q →
  Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p) →
  Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid q) →
  NonBisimDef p q
| _p, _q, .ofP _p' inwP allQ, hcP, hcQ =>
    let ⟨p'', insP'', bisimP'⟩ := Pair.Triset.hc_ins_of_inw hcP inwP
    .ofP p'' insP'' fun _q' inwQ' =>
      let ⟨q'', insQ'', bisimQ'⟩ := Pair.Triset.hc_ins_of_inw hcQ inwQ'
      let hcP' := Pair.Triset.hc_hered hcP inwP
      let hcQ' := Pair.Triset.hc_hered hcQ inwQ'
      let hcQ'':
        Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid q'')
      :=
        (@Quotient.sound _ Pair.PreTriset.setoid _ _ bisimQ') ▸ hcQ'
      let nbd := (allQ q'' insQ'').toNonBisimDef hcP' hcQ''
      nbd.respectsBisim bisimP' bisimQ'.symm
| _p, _q, .ofQ _q' inwQ allP, hcP, hcQ =>
    let ⟨q'', insQ'', bisimQ'⟩ := Pair.Triset.hc_ins_of_inw hcQ inwQ
    .ofQ q'' insQ'' fun _p' inwP' =>
      let ⟨p'', insP'', bisimP'⟩ := Pair.Triset.hc_ins_of_inw hcP inwP'
      let hcQ' := Pair.Triset.hc_hered hcQ inwQ
      let hcP' := Pair.Triset.hc_hered hcP inwP'
      let hcP'':
        Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p'')
      :=
        (@Quotient.sound _ Pair.PreTriset.setoid _ _ bisimP') ▸ hcP'
      let nbd := (allP p'' insP'').toNonBisimDef hcP'' hcQ'
      nbd.respectsBisim bisimP'.symm bisimQ'

theorem bisimDl.IsBisimPos.toIsBisimDef {p q: Pair}
  (hcP: Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid p))
  (hcQ: Pair.Triset.Hc (Quotient.mk Pair.PreTriset.setoid q))
  (isBP: IsBisimPos p q)
:
  IsBisimDef p q
:=
  fun nbp => isBP (nbp.toNonBisimDef hcP hcQ)


-- Lifting the collapse to the quotient, and packaging the equivalences.
theorem Triset.IsBisimDef.toIsBisimPos {ts0 ts1: Pair.Triset}
  (isBD: Triset.IsBisimDef ts0 ts1)
:
  Triset.IsBisimPos ts0 ts1
:=
  Quotient.inductionOn₂
    (motive :=
      fun t0 t1 => Triset.IsBisimDef t0 t1 → Triset.IsBisimPos t0 t1)
    ts0 ts1
    (fun _p _q h => bisimDl.IsBisimAt.toIsBisimPos h)
    isBD

theorem Triset.IsBisimPos.toIsBisimDef {ts0 ts1: Pair.Triset}
  (hc0: Pair.Triset.Hc ts0)
  (hc1: Pair.Triset.Hc ts1)
  (isBP: Triset.IsBisimPos ts0 ts1)
:
  Triset.IsBisimDef ts0 ts1
:=
  Quotient.inductionOn₂
    (motive := fun t0 t1 =>
      Pair.Triset.Hc t0 →
      Pair.Triset.Hc t1 →
      Triset.IsBisimPos t0 t1 →
      Triset.IsBisimDef t0 t1)
    ts0 ts1
    (fun _p _q hcp hcq h => bisimDl.IsBisimPos.toIsBisimDef hcp hcq h)
    hc0 hc1 isBP

theorem Triset.IsBisimPos.refl
  (ts: Pair.Triset)
:
  Triset.IsBisimPos ts ts
:=
  Quotient.inductionOn
    (motive := fun t => Triset.IsBisimPos t t)
    ts
    (fun p =>
      let rflP := Pair.PreTriset.setoid.iseqv.refl p
      bisimDl.IsBisimPos.of_bisim rflP)

theorem Triset.IsBisimDef.refl_of_hc {ts: Pair.Triset}
  (hc: Pair.Triset.Hc ts)
:
  Triset.IsBisimDef ts ts
:=
  (Triset.IsBisimPos.refl ts).toIsBisimDef hc hc


-- Assuming a hc triset, definite bisimilarity is equivalent to equality.
theorem Triset.hc_isBisimDef_iff_eq {ts0 ts1: Pair.Triset}
  (hc0: Pair.Triset.Hc ts0)
:
  Triset.IsBisimDef ts0 ts1 ↔ ts0 = ts1
:=
  Iff.intro
    Triset.IsBisimDef.toEq
    (fun eq => eq ▸ Triset.IsBisimDef.refl_of_hc hc0)

-- Assuming two hc trisets, possible bisimilarity is equivalent to
-- definite bisimilarity.
theorem Triset.hc_isBisimPos_iff_isBisimDef {ts0 ts1: Pair.Triset}
  (hc0: Pair.Triset.Hc ts0)
  (hc1: Pair.Triset.Hc ts1)
:
  Triset.IsBisimPos ts0 ts1 ↔ Triset.IsBisimDef ts0 ts1
:=
  Iff.intro
    (fun isBP => isBP.toIsBisimDef hc0 hc1)
    Triset.IsBisimDef.toIsBisimPos

-- Assuming two hc trisets, possible bisimilarity is equivalent to
-- equality.
theorem Triset.hc_isBisimPos_iff_eq {ts0 ts1: Pair.Triset}
  (hc0: Pair.Triset.Hc ts0)
  (hc1: Pair.Triset.Hc ts1)
:
  Triset.IsBisimPos ts0 ts1 ↔ ts0 = ts1
:=
  (Triset.hc_isBisimPos_iff_isBisimDef hc0 hc1).trans
    (Triset.hc_isBisimDef_iff_eq hc0)
