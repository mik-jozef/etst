import Etst.WFC.Utils.SelfDefinability.UniSetMapDl

namespace Etst
open SingleLaneExpr


def InUniSetMapDefAt (dl n fv b c expr p) :=
  let vars := [
    BasicExpr.encoding expr,
    Pair.listEncoding fv,
    DefList.prefixEncoding dl n,
  ]
  intp2 (exprEncList.toLane .defLane) vars b c p

def isAtElimConst {dl n fv b c x p}
  (ins: InUniSetMapDefAt dl n fv b c (.const x) p)
  (inCins: (∀ {d x}, d ∈ (c x).defMem → uniSetMapDl.Ins d x))
:
  (c uniSetMapDl.consts.uniSetMap).defMem
    (.pair (uniSetMapIndex dl n [] ((dl.prefix n).getDef x)) p)
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
    let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
    let xEncEq: .nat x = xEnc :=
      match exprGuard with
      | .null => inPairElimNope insGuardL
      | .pair _ _ =>
        let ⟨insNat, insVar⟩ := inPairElim insGuardL
        let eqNatX :=
          Pair.noConfusion (inVarElim insGuardR rfl) fun _ => id
        eqNatX.symm.trans (inVarElim insVar rfl)
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
        uniSetMapDl.getDefElim
          (show intp (const .defLane 0) _ _ _
          from xEncEq ▸ insGetDef)
      let exprAliasEq := dl.prefixList_at_eq someExprAliasEq
      by
      unfold uniSetMapIndex
      exact exprAliasEq ▸ eqFvAlias ▸ eqDlAlias ▸ inMap
  (inUnElim ins).elim
    main
    (fun ins =>
      (inUnElim ins).elim
        (fun ins =>
          let ⟨xEnc, ins⟩ := inArbUnElim ins
          let ⟨insExprGuard, _⟩ := inIrElim ins
          let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
          let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
          let xEncEq: .nat x = xEnc :=
            match exprGuard with
            | .null => inPairElimNope insGuardL
            | .pair _ _ =>
              let ⟨insNat, insVar⟩ := inPairElim insGuardL
              let eqNatX :=
                Pair.noConfusion (inVarElim insGuardR rfl) fun _ => id
              eqNatX.symm.trans (inVarElim insVar rfl)
          sorry)
        sorry)

def isAtElimVar {dl n fv b c v p}
  (ins: InUniSetMapDefAt dl n fv b c (.var v) p)
  (inCins: (∀ {d x}, d ∈ (c x).defMem → uniSetMapDl.Ins d x))
:
  sorry
:=
  sorry


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
    let ins := isCause isConsistent.leastValsApxAreSat
    let ⟨dlEnc, ins⟩ := inArbUnElim (indexEq ▸ cstEq ▸ ins)
    let ⟨fvEnc, ins⟩ := inArbUnElim ins
    let ⟨exprEnc, ins⟩ := inArbUnElim ins
    let ⟨insEnc, insLB⟩ := inPairElim ins
    let ⟨dlEncEq, fvEncEq, exprEncEq⟩ :=
      let ⟨insDl, ins⟩ := inPairElim insEnc
      let ⟨insFv, insExpr⟩ := inPairElim ins
      And.intro
        (inVarElim insDl rfl)
        (And.intro
          (inVarElim insFv rfl)
          (inVarElim insExpr rfl))
    
    match expr with
    | .const x =>
      let inCins :=
        isAtElimConst (dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insLB) cinsSat
      let ih := uniSetMapAt_le_ins_helper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .var _ => sorry
    | .null => sorry
    | .pair _ _ => sorry
    | .ir _ _ => sorry
    | .full _ => sorry
    | .compl _ =>
      sorry
    | .arbIr _ => sorry

def uniSetMapAt_le_out_helper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out index cst)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (whyDoINeedThisEq: cst = uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  sorry


def uniSetMapAt_le_out {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      (.pair (uniSetMapIndex dl n fv expr) p)
      uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  uniSetMapAt_le_out_helper out rfl rfl

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
