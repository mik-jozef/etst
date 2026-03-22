import Etst.WFC.Utils.SelfDefinability.UniSetMapDl

namespace Etst
open SingleLaneExpr


def InUniSetMapDefAt (dl n fv b c expr p) :=
  (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap).triIntp2Def
    []
    b
    c
    (.pair (uniSetMapIndex dl n fv expr) p)

def insEncElim {b c dl n fv expr exprEnc fvEnc dlEnc}
  (ins:
    (pair (var 2) (pair (var 1) (var 0))).intp2
      [exprEnc, fvEnc, dlEnc]
      b
      c
      (uniSetMapIndex dl n fv expr))
:
  dl.prefixEncoding n = dlEnc ∧
  Pair.listEncoding fv = fvEnc ∧
  expr.encoding = exprEnc
:=
  let ⟨insDl, ins⟩ := inPairElim ins
  let ⟨insFv, insExpr⟩ := inPairElim ins
  And.intro
    (inVarElim insDl rfl)
    (And.intro
      (inVarElim insFv rfl)
      (inVarElim insExpr rfl))


def isAtConst {dl n fv b c x p}
  (ins: InUniSetMapDefAt dl n fv b c (.const x) p)
  (inCins: (∀ {d x}, d ∈ (c x).defMem → uniSetMapDl.Ins d x))
:
  (c uniSetMapDl.consts.uniSetMap).defMem
    (.pair (uniSetMapIndex dl n [] ((dl.prefix n).getDef x)) p)
:=
  let ⟨dlEnc, ins⟩ := inArbUnElim ins
  let ⟨fvEnc, ins⟩ := inArbUnElim ins
  let ⟨exprEnc, ins⟩ := inArbUnElim ins
  let ⟨insEnc, ins⟩ := inPairElim ins
  let ⟨dlEncEq, fvEncEq, exprEncEq⟩ := insEncElim insEnc
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
    let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
    let exprEncEqPair: exprEnc = .pair (.nat 0) xEnc :=
      match exprGuard with
      | .null => inPairElimNope insGuardL
      | .pair _ _ =>
        let ⟨insNat, insVar⟩ := inPairElim insGuardL
        inVarElim insGuardR rfl ▸
        Pair.eq (inNatElim insNat) (inVarElim insVar rfl)
    let xEncEq: .nat x = xEnc :=
      Pair.noConfusion (exprEncEq.trans exprEncEqPair) fun _ => id
    let ⟨pArg, inMap, inArg⟩ := inCallElim ins
    match pArg with
    | .null => inPairElimNope inArg
    | .pair _ .null => inPairElimNope (inPairElim inArg).right
    | .pair dlEncAlias (.pair fvAlias exprAlias) =>
      let ⟨insDlAlias, ins⟩ := inPairElim inArg
      let ⟨insFvAlias, insDefX⟩ := inPairElim ins
      let eqDlAlias := inVarElim insDlAlias rfl
      let eqFvAlias: fvAlias = Pair.listEncoding [] :=
        inNullElim insFvAlias
      let insDefX := inCallElimSingle insDefX rfl
      let insDefX := inCallElimSingle insDefX rfl
      let insGetDef := (inCins insDefX).isSound
      let someExprAliasEq :=
        uniSetMapDl.getDefElim (show
          intp (const .defLane 0) _ _ _
        from
          dlEncEq ▸ xEncEq ▸ insGetDef)
      let exprAliasEq := dl.prefixList_at_eq someExprAliasEq
      by
      unfold uniSetMapIndex
      exact
      exprAliasEq ▸ eqFvAlias ▸ dlEncEq ▸ eqDlAlias ▸ inMap
  (inUnElim ins).elim
    main
    (fun ins =>
      (inUnElim ins).elim
        sorry
        sorry)


/-
  Has to use the weird equality trick :( else we get:
  
  ```
    fail to show termination for
    [...]
    Not considering parameter ins of Etst.uniSetMapAt_le_ins:
      its type Etst.DefList.Ins is an inductive family and
      indices are not variables
  ```
-/
def uniSetMapAt_le_ins_helper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins index cst)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (whyDoINeedThisEq: cst = uniSetMapDl.consts.uniSetMap)
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  let cstEq := whyDoINeedThisEq
  match ins with
  | .intro _ _ cause isCause cinsSat binsSat boutSat =>
    let isConsistent :=
      Cause.IsStronglySatisfiedByBackground.toIsConsistent {
        backgroundInsHold := DefList.Ins.isSound ∘ binsSat
        backgroundOutHold := DefList.Out.isSound ∘ boutSat
      }
    let inUniSetMapDef := isCause isConsistent.leastValsApxAreSat
    match expr with
    | .const x =>
      let inCins := isAtConst (indexEq ▸ cstEq ▸ inUniSetMapDef) cinsSat
      let ih := uniSetMapAt_le_ins_helper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | _ => sorry


def uniSetMapAt_le_out {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      (.pair (uniSetMapIndex dl n fv expr) p)
      uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  sorry

def uniSetMapAt_le_ins {dl n fv expr p}
  (ins:
    uniSetMapDl.Ins
      (.pair (uniSetMapIndex dl n fv expr) p)
      uniSetMapDl.consts.uniSetMap)
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  uniSetMapAt_le_ins_helper ins rfl rfl

def uniSetMapAt_le
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  uniSetMapAt dl n fv expr ⊑ expr.triIntp fv (dl.prefix n).wfm
:= {
  defLe _ := uniSetMapAt_le_ins ∘ DefList.Ins.isComplete
  posLe _ :=
    Function.mtr (uniSetMapAt_le_out ∘ DefList.Out.isComplete)
}
