import old.UniSet3.Ch8_S12_DefListToEncoding
import old.Utils.CauseSatisfiesBoundVars
import old.Utils.IsBound
import old.Utils.NopeInterp
import old.Utils.OutIntro4

open Expr
open Pair
open Pair.uniSet3
open PairExpr


def elimPosExternalVar
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.var x) d))
:
  Or
    (Set3.posMem
      (c uniDefList.getBound)
      (pair (boundVarsEncoding boundVars) (pair x d)))
    (And
      (Set3.posMem (c uniDefList.theSet) (pair x d))
      (¬ ∃ d,
        Set3.defMem
          (b uniDefList.getBound)
          (pair (boundVarsEncoding boundVars) (pair x d))))
:=
  let eqZ: zero = fromNat 0 := rfl
  inwFinUnElim
    (list := uniDefList.interpretation.exprList)
    inw
    (fun inw =>
      let ⟨xEnc, _, inw⟩ := inwUnDomElim inw
      let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
      let ⟨inwBv, inw⟩ := inwPairElim inw
      let bvEq := inwBoundElim inwBv
      let ⟨inwExprEnc, inwBoundOrFree⟩ := inwPairElim inw
      let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
      let xEncEq :=
        inwBoundElim (inwFreeElim inwExprEnc nat501Neq500)
      (inwUnElim inwBoundOrFree).elim
        (fun inw =>
          let inw := inwCallElimBound inw rfl nat502Neq500
          let inw := inwCallElimBound inw rfl nat503Neq501
          bvEq ▸ xEncEq ▸ Or.inl inw)
        (fun inw =>
          let ⟨inwL, inwR⟩ := inwIrElim inw
          let inw := inwCallElimBound inwR rfl nat502Neq500
          bvEq ▸ xEncEq ▸ Or.inr ⟨
            inw,
            fun ⟨dBound, ins⟩ =>
              let inwL := inwCondFullElim inwL dBound
              let nins := inwCplElim inwL
              nins
                (insCallExpr
                  (insCallExpr
                    ins
                    (insFree
                      (insFree
                        insBound
                        nat502Neq501)
                      nat503Neq501))
                  (insFree
                    (insFree
                      insBound
                      nat501Neq500)
                    nat502Neq500))
          ⟩))
    (nopePosInterpZero fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpPair fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpCpl fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpCondSome fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpCondFull fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpArbUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopePosInterpArbIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))

def elimDefExternalVar
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.var x) d))
:
  Or
    (Set3.defMem
      (c uniDefList.getBound)
      (pair (boundVarsEncoding boundVars) (pair x d)))
    (And
      (Set3.defMem (c uniDefList.theSet) (pair x d))
      (¬ ∃ d,
        Set3.posMem
          (b uniDefList.getBound)
          (pair (boundVarsEncoding boundVars) (pair x d))))
:=
  let eqZ: zero = fromNat 0 := rfl
  insFinUnElim
    (list := uniDefList.interpretation.exprList)
    ins
    (fun ins =>
      let ⟨xEnc, _, ins⟩ := insUnDomElim ins
      let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
      let ⟨inwBv, ins⟩ := insPairElim ins
      let bvEq := insBoundElim inwBv
      let ⟨insExprEnc, insBoundOrFree⟩ := insPairElim ins
      let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
      let xEncEq :=
        insBoundElim (insFreeElim insExprEnc nat501Neq500)
      (insUnElim insBoundOrFree).elim
        (fun ins =>
          let ins := insCallElimBound ins rfl nat502Neq500
          let ins := insCallElimBound ins rfl nat503Neq501
          bvEq ▸ xEncEq ▸ Or.inl ins)
        (fun ins =>
          let ⟨insL, insR⟩ := insIrElim ins
          let ins := insCallElimBound insR rfl nat502Neq500
          bvEq ▸ xEncEq ▸ Or.inr ⟨
            ins,
            fun ⟨dBound, inw⟩ =>
              let inwL := insCondFullElim insL dBound
              let ninw := insCplElim inwL
              ninw
                (inwCallExpr
                  (inwCallExpr
                    inw
                    (inwFree
                      (inwFree
                        inwBound
                        nat502Neq501)
                      nat503Neq501))
                  (inwFree
                    (inwFree
                      inwBound
                      nat501Neq500)
                    nat502Neq500))
          ⟩))
    (nopeDefInterpZero fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpPair fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpUn fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpIr fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpCpl fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpCondSome fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpCondFull fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpArbUn fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))
    (nopeDefInterpArbIr fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope (eqZ ▸ ins) (by decide))


def elimPosExternalZero
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars zeroExpr d))
:
  d = zero
:=
  inwFinUnElim
    (list := uniDefList.interpretation.exprList)
    inw
    (nopePosInterpVar fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      Pair.noConfusion (inwZeroElim inw))
    (fun inw =>
      let ⟨_, inw⟩ := inwArbUnElim inw
      let ⟨_, inw⟩ := inwPairElim inw
      let ⟨_, inw⟩ := inwPairElim inw
      inwZeroElim inw)
    (nopePosInterpPair fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpCpl fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpCondSome fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpCondFull fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpArbUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopePosInterpArbIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))

def elimDefExternalZero
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars zeroExpr d))
:
  d = zero
:=
  insFinUnElim
    (list := uniDefList.interpretation.exprList)
    ins
    (nopeDefInterpVar fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      Pair.noConfusion (insZeroElim ins))
    (fun ins =>
      let ⟨_, ins⟩ := insArbUnElim ins
      let ⟨_, ins⟩ := insPairElim ins
      let ⟨_, ins⟩ := insPairElim ins
      insZeroElim ins)
    (nopeDefInterpPair fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpUn fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpIr fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpCpl fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpCondSome fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpCondFull fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpArbUn fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))
    (nopeDefInterpArbIr fun ins =>
      let ⟨ins, _⟩ := insPairElim ins
      insNatExprElimNope ins (by decide))


def elimPosExternalPair
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (pairExpr left rite) d))
:
  ∃ dLeft dRite,
    d = pair dLeft dRite ∧
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left dLeft) ∧
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite dRite)
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨leftEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨riteEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwLeft, inwRite⟩ := inwPairElim inwExprEnc
        let leftEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          inwBoundElim (inwFreeElim inwRite nat502Neq501)
        let ⟨dL, dR, dEq, inwL, inwR⟩ := inwPairElim.ex inw
        let inwL := inwCallElimBound inwL rfl nat503Neq500
        let inwL := inwCallElimBound inwL rfl nat504Neq502
        let inwR := inwCallElimBound inwR rfl nat503Neq501
        let inwR := inwCallElimBound inwR rfl nat504Neq502
        bvEq ▸ leftEq ▸ riteEq ▸ ⟨dL, dR, dEq, inwL, inwR⟩)
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalPair
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (pairExpr left rite) d))
:
  ∃ dLeft dRite,
    d = pair dLeft dRite ∧
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left dLeft) ∧
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite dRite)
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨leftEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨riteEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let ⟨insLeft, insRite⟩ := insPairElim insExprEnc
        let leftEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          insBoundElim (insFreeElim insRite nat502Neq501)
        let ⟨dL, dR, dEq, inwL, inwR⟩ := insPairElim.ex ins
        let inwL := insCallElimBound inwL rfl nat503Neq500
        let inwL := insCallElimBound inwL rfl nat504Neq502
        let inwR := insCallElimBound inwR rfl nat503Neq501
        let inwR := insCallElimBound inwR rfl nat504Neq502
        bvEq ▸ leftEq ▸ riteEq ▸ ⟨dL, dR, dEq, inwL, inwR⟩)
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalUn
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra b c (uniDefList.interpretation.expr))
      (InterpEnc boundVars (unExpr left rite) d))
:
  Or
    (Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left d))
    (Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite d))
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨leftEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨riteEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwLeft, inwRite⟩ := inwPairElim inwExprEnc
        let leftEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          inwBoundElim (inwFreeElim inwRite nat502Neq501)
        (inwUnElim inw).elim
          (fun inwL =>
            let inw := inwCallElimBound inwL rfl nat503Neq500
            let inw := inwCallElimBound inw rfl nat504Neq502
            bvEq ▸ leftEq ▸ Or.inl inw)
          (fun inwR =>
            let inw := inwCallElimBound inwR rfl nat503Neq501
            let inw := inwCallElimBound inw rfl nat504Neq502
            bvEq ▸ riteEq ▸ Or.inr inw))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalUn
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (unExpr left rite) d))
:
  Or
    (Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left d))
    (Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite d))
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨leftEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨riteEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let ⟨insLeft, insRite⟩ := insPairElim insExprEnc
        let leftEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          insBoundElim (insFreeElim insRite nat502Neq501)
        (insUnElim ins).elim
          (fun insL =>
            let ins := insCallElimBound insL rfl nat503Neq500
            let ins := insCallElimBound ins rfl nat504Neq502
            bvEq ▸ leftEq ▸ Or.inl ins)
          (fun insR =>
            let ins := insCallElimBound insR rfl nat503Neq501
            let ins := insCallElimBound ins rfl nat504Neq502
            bvEq ▸ riteEq ▸ Or.inr ins))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalIr
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (irExpr left rite) d))
:
  And
    (Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left d))
    (Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite d))
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨leftEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨riteEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwLeft, inwRite⟩ := inwPairElim inwExprEnc
        let leftEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          inwBoundElim (inwFreeElim inwRite nat502Neq501)
        let ⟨inwL, inwR⟩ := inwIrElim inw
        let inwL := inwCallElimBound inwL rfl nat503Neq500
        let inwL := inwCallElimBound inwL rfl nat504Neq502
        let inwR := inwCallElimBound inwR rfl nat503Neq501
        let inwR := inwCallElimBound inwR rfl nat504Neq502
        bvEq ▸ leftEq ▸ riteEq ▸ ⟨inwL, inwR⟩)
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalIr
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (irExpr left rite) d))
:
  And
    (Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars left d))
    (Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars rite d))
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨leftEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨riteEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let ⟨insLeft, insRite⟩ := insPairElim insExprEnc
        let leftEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insLeft
                nat502Neq500)
              nat501Neq500)
        let riteEq :=
          insBoundElim (insFreeElim insRite nat502Neq501)
        let ⟨insL, insR⟩ := insIrElim ins
        let insL := insCallElimBound insL rfl nat503Neq500
        let insL := insCallElimBound insL rfl nat504Neq502
        let insR := insCallElimBound insR rfl nat503Neq501
        let insR := insCallElimBound insR rfl nat504Neq502
        bvEq ▸ leftEq ▸ riteEq ▸ ⟨insL, insR⟩)
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalCpl
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.cpl expr) d))
:
  Not
    (Set3.defMem
      (b uniDefList.interpretation)
      (InterpEnc boundVars expr d))
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨exprEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let exprEncEq :=
          inwBoundElim
            (inwFreeElim
              inwExprEnc
              nat502Neq500)
        let nins := inwCplElim inw
        bvEq ▸
        exprEncEq ▸
        fun ins =>
          nins
            (insCallExpr
              (insCallExpr
                ins
                (insFree
                  (insFree
                    insBound
                    nat503Neq502)
                  nat504Neq502))
              (insFree
                (insFree
                  insBound
                  nat502Neq500)
                nat503Neq500)))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalCpl
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.cpl expr) d))
:
  Not
    (Set3.posMem
      (b uniDefList.interpretation)
      (InterpEnc boundVars expr d))
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨exprEnc, ⟨_, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let exprEncEq :=
          insBoundElim
            (insFreeElim
              insExprEnc
              nat502Neq500)
        let ninw := insCplElim ins
        bvEq ▸
        exprEncEq ▸
        fun ins =>
          ninw
            (inwCallExpr
              (inwCallExpr
                ins
                (inwFree
                  (inwFree
                    inwBound
                    nat503Neq502)
                  nat504Neq502))
              (inwFree
                (inwFree
                  inwBound
                  nat502Neq500)
                nat503Neq500)))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalCondSome
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (condSomeExpr expr) d))
:
  ∃ dCond,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars expr dCond)
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨exprEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let exprEq :=
          inwBoundElim
            (inwFreeElim
              inwExprEnc
              nat502Neq500)
        let ⟨dE, inwExpr⟩ := inwCondSomeElim inw
        let inwExpr := inwCallElimBound inwExpr rfl nat503Neq500
        let inwExpr := inwCallElimBound inwExpr rfl nat504Neq502
        bvEq ▸ exprEq ▸ ⟨dE, inwExpr⟩)
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalCondSome
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (condSomeExpr expr) d))
:
  ∃ dCond,
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars expr dCond)
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨condEnc, ⟨_, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let exprEq :=
          insBoundElim
            (insFreeElim
              insExprEnc
              nat502Neq500)
        let ⟨dE, insExpr⟩ := insCondSomeElim ins
        let insExpr := insCallElimBound insExpr rfl nat503Neq500
        let insExpr := insCallElimBound insExpr rfl nat504Neq502
        bvEq ▸ exprEq ▸ ⟨dE, insExpr⟩)
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalCondFull
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (condFullExpr expr) d))
:
  ∀ dCond,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars expr dCond)
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw dCond =>
        let ⟨exprEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let exprEq :=
          inwBoundElim
            (inwFreeElim
              inwExprEnc
              nat502Neq500)
        let inwExpr := inwCondFullElim inw dCond
        let inwExpr := inwCallElimBound inwExpr rfl nat503Neq500
        let inwExpr := inwCallElimBound inwExpr rfl nat504Neq502
        bvEq ▸ exprEq ▸ inwExpr)
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalCondFull
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (condFullExpr expr) d))
:
  ∀ dCond,
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars expr dCond)
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins dE =>
        let ⟨condEnc, ⟨_, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let exprEq :=
          insBoundElim
            (insFreeElim
              insExprEnc
              nat502Neq500)
        let insExpr := insCondFullElim ins dE
        let insExpr := insCallElimBound insExpr rfl nat503Neq500
        let insExpr := insCallElimBound insExpr rfl nat504Neq502
        bvEq ▸ exprEq ▸ insExpr)
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalArbUn
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.arbUn x body) d))
:
  ∃ dX,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨xEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨bodyEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwX, inwBody⟩ := inwPairElim inwExprEnc
        let xEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwX
                nat502Neq500)
              nat501Neq500)
        let bodyEq :=
          inwBoundElim
            (inwFreeElim
              inwBody
              nat502Neq501)
        let ⟨dX, inw⟩ := inwArbUnElim inw
        let inw := inwCallElimBound inw rfl nat504Neq501
        let ⟨bvEncUpdated, inwInterp, inw⟩ := inwCallExprElim inw
        let ⟨bvHead, bvEncAlias, eqBvUpd, inwHead, inwBv⟩ :=
          inwPairElim.ex inw
        let ⟨xAlias, dXAlias, eqH, inwX, inwXd⟩ :=
          inwPairElim.ex inwHead
        let xAliasEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim
                      inwX
                      nat505Neq500)
                    nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
        let dXAliasEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwXd
                nat505Neq503)
              nat504Neq503)
        let bvEncEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                (inwFreeElim
                  inwBv
                  nat505Neq502)
                nat504Neq502)
              nat503Neq502)
        let eqHead := xAliasEq ▸ dXAliasEq ▸ eqH
        ⟨
          dX,
          by
            unfold boundVarsEncoding
            rw [
              bvEq,
              xEq,
              bodyEq,
              bvEncEq.symm,
              eqHead.symm,
              eqBvUpd.symm,
            ]
            exact inwInterp
        ⟩)
      (nopePosInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimDefExternalArbUn
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.arbUn x body) d))
:
  ∃ dX,
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨xEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨bodyEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let ⟨insX, insBody⟩ := insPairElim insExprEnc
        let xEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insX
                nat502Neq500)
              nat501Neq500)
        let bodyEq :=
          insBoundElim
            (insFreeElim
              insBody
              nat502Neq501)
        let ⟨dX, ins⟩ := insArbUnElim ins
        let ins := insCallElimBound ins rfl nat504Neq501
        let ⟨bvEncUpdated, insInterp, ins⟩ := insCallExprElim ins
        let ⟨bvHead, bvEncAlias, eqBvUpd, insHead, insBv⟩ :=
          insPairElim.ex ins
        let ⟨xAlias, dXAlias, eqH, insX, insXd⟩ :=
          insPairElim.ex insHead
        let xAliasEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                (insFreeElim
                  (insFreeElim
                    (insFreeElim
                      insX
                      nat505Neq500)
                    nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
        let dXAliasEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insXd
                nat505Neq503)
              nat504Neq503)
        let bvEncEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                (insFreeElim
                  insBv
                  nat505Neq502)
                nat504Neq502)
              nat503Neq502)
        let eqHead := xAliasEq ▸ dXAliasEq ▸ eqH
        ⟨
          dX,
          by
            unfold boundVarsEncoding
            rw [
              bvEq,
              xEq,
              bodyEq,
              bvEncEq.symm,
              eqHead.symm,
              eqBvUpd.symm,
            ]
            exact insInterp
        ⟩)
      (nopeDefInterpArbIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))


def elimPosExternalArbIr
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.arbIr x body) d))
:
  ∀ dX,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  intro dX
  exact
    inwFinUnElim
      (list := uniDefList.interpretation.exprList)
      inw
      (nopePosInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopePosInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondSome fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpCondFull fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopePosInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨xEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨bodyEnc, ⟨_inwDom, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwX, inwBody⟩ := inwPairElim inwExprEnc
        let xEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwX
                nat502Neq500)
              nat501Neq500)
        let bodyEq :=
          inwBoundElim
            (inwFreeElim
              inwBody
              nat502Neq501)
        let inw := inwArbIrElim inw dX
        let inw := inwCallElimBound inw rfl nat504Neq501
        let ⟨bvEncUpdated, inwInterp, inw⟩ := inwCallExprElim inw
        let ⟨bvHead, bvEncAlias, eqBvUpd, inwHead, inwBv⟩ :=
          inwPairElim.ex inw
        let ⟨xAlias, dXAlias, eqH, inwX, inwXd⟩ :=
          inwPairElim.ex inwHead
        let xAliasEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim
                      inwX
                      nat505Neq500)
                    nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
        let dXAliasEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwXd
                nat505Neq503)
              nat504Neq503)
        let bvEncEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                (inwFreeElim
                  inwBv
                  nat505Neq502)
                nat504Neq502)
              nat503Neq502)
        let eqHead := xAliasEq ▸ dXAliasEq ▸ eqH
        by
          unfold boundVarsEncoding
          rw [
            bvEq,
            xEq,
            bodyEq,
            bvEncEq.symm,
            eqHead.symm,
            eqBvUpd.symm,
          ]
          exact inwInterp)

def elimDefExternalArbIr
  (ins:
    Set3.defMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.arbIr x body) d))
:
  ∀ dX,
    Set3.defMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  intro dX
  exact
    insFinUnElim
      (list := uniDefList.interpretation.exprList)
      ins
      (nopeDefInterpVar fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        Pair.noConfusion (insZeroElim ins))
      (nopeDefInterpZero fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpPair fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpIr fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCpl fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondSome fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpCondFull fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (nopeDefInterpArbUn fun ins =>
        let ⟨ins, _⟩ := insPairElim ins
        insNatExprElimNope ins (by decide))
      (fun ins =>
        let ⟨xEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨bodyEnc, ⟨_inwDom, ins⟩⟩ := insUnDomElim ins
        let ⟨boundVarsEnc, ins⟩ := insArbUnElim ins
        let ⟨inwBv, ins⟩ := insPairElim ins
        let bvEq := insBoundElim inwBv
        let ⟨insExprEnc, ins⟩ := insPairElim ins
        let ⟨_, insExprEnc⟩ := insPairElim insExprEnc
        let ⟨insX, insBody⟩ := insPairElim insExprEnc
        let xEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insX
                nat502Neq500)
              nat501Neq500)
        let bodyEq :=
          insBoundElim
            (insFreeElim
              insBody
              nat502Neq501)
        let inw := insArbIrElim ins dX
        let inw := insCallElimBound inw rfl nat504Neq501
        let ⟨bvEncUpdated, insInterp, ins⟩ := insCallExprElim inw
        let ⟨bvHead, bvEncAlias, eqBvUpd, insHead, insBv⟩ :=
          insPairElim.ex ins
        let ⟨xAlias, dXAlias, eqH, insX, insXd⟩ :=
          insPairElim.ex insHead
        let xAliasEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                (insFreeElim
                  (insFreeElim
                    (insFreeElim
                      insX
                      nat505Neq500)
                    nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
        let dXAliasEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insXd
                nat505Neq503)
              nat504Neq503)
        let bvEncEq :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                (insFreeElim
                  insBv
                  nat505Neq502)
                nat504Neq502)
              nat503Neq502)
        let eqHead := xAliasEq ▸ dXAliasEq ▸ eqH
        by
          unfold boundVarsEncoding
          rw [
            bvEq,
            xEq,
            bodyEq,
            bvEncEq.symm,
            eqHead.symm,
            eqBvUpd.symm,
          ]
          exact insInterp)


def Cause.boundVarSat
  (isBoundTo: IsBoundTo boundVars x d)
:
  (Cause.var x d).SatisfiesBoundVars boundVars
:=
  fun {xx _dd} isBound =>
    if h: xx = x then
      let dEq := isBoundTo.isUnique (h ▸ isBound)
      {
        cinsSat := fun _ ⟨eqVvD, _⟩ _ => eqVvD.trans dEq
        binsSat := nofun
        boutSat := nofun
      }
    else {
      cinsSat := fun _ ⟨_, eqVvX⟩ xxEq =>
        (h (xxEq.symm.trans eqVvX)).elim
      binsSat := nofun
      boutSat := nofun
    }

def Cause.freeVarSat
  (notBound: ¬ IsBound boundVars x)
:
  (Cause.var x d).SatisfiesBoundVars boundVars
:=
  fun isBound => {
    cinsSat :=
      fun _ ⟨_, eqVvX⟩ xxEq =>
        absurd ⟨_, eqVvX ▸ xxEq ▸ isBound⟩ notBound
    binsSat := nofun
    boutSat := nofun
  }

def Cause.emptySat
  (boundVars: List (ValVar Pair))
:
  Cause.empty.SatisfiesBoundVars boundVars
:=
  fun _ => {
    cinsSat := nofun
    binsSat := nofun
    boutSat := nofun
  }
