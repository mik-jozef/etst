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

/-
  ## Section: proving equivalence of the Lean-native WFM defs
  
  This is write-once, read-never code. You have been warned.
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
  ## Section: <Name>
-/
