import UniSet3.Ch8_S12_DefListToEncoding
import Utils.CauseSatisfiesBoundVars
import Utils.NopeInterp
import Utils.OutIntro4

open Expr
open Pair
open Pair.uniSet3
open PairExpr

def IsVarFree
  (x: Nat)
  (boundVars: List (ValVar D))
:
  Prop
:=
  ∀ d, ⟨d, x⟩ ∉ boundVars

def IsVarFree.Not.exBoundOfNot
  {boundVars: List (ValVar D)}
  (notFree: ¬ IsVarFree x boundVars)
:
  ∃ d, ⟨d, x⟩ ∈ boundVars
:=
  notFree.toEx fun _ => Not.dne

def IsVarFree.nopeGetBound
  (isFree: IsVarFree x boundVars)
  (isBound: IsGetBound (boundVarsEncoding boundVars) x d)
:
  P
:=
  False.elim (isFree d isBound.inBoundVars)

def IsVarFree.toNotBound
  (isFree: IsVarFree x boundVars)
:
  ¬ IsBound boundVars x
:=
  fun ⟨_, isGetBound⟩ => isFree.nopeGetBound isGetBound

def IsVarFree.ofEmpty
  {D: Type*}
  (x: Nat)
:
  IsVarFree (D := D) x []
:=
  nofun

def IsVarFree.ofTail
  (isFree: IsVarFree x boundVars)
  (neqHead: xH ≠ x)
  dH
:
  IsVarFree x (⟨dH, xH⟩ :: boundVars)
:=
  fun _ isBound =>
    match List.mem_cons.mp isBound with
    | Or.inl eq => ValVar.noConfusion eq fun _ => Ne.symm neqHead
    | Or.inr inBoundTail => isFree _ inBoundTail


def elimExternalVar
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
  @inwFinUnElim
    pairSignature
    pairSalgebra
    b
    c
    uniDefList.interpretation.exprList
    (InterpEnc boundVars (Expr.var x) d)
    _
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
          let ⟨⟨dC, inwC⟩, inw⟩ := inwIfThenElim inw
          let nins := inwCplElim inwC
          let inw := inwCallElimBound inw rfl nat502Neq500
          bvEq ▸ xEncEq ▸ Or.inr ⟨
            inw,
            fun ⟨dBound, ins⟩ =>
              nins
                (insIfThen
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
                  insAny)
          ⟩))
    (nopeInterpZero fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpPair fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpCpl fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpIfThen fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpArbUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))
    (nopeInterpArbIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope (eqZ ▸ inw) (by decide))

def elimExternalZero
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
  @inwFinUnElim
    pairSignature
    pairSalgebra
    b
    c
    uniDefList.interpretation.exprList
    (InterpEnc boundVars zeroExpr d)
    _
    inw
    (nopeInterpVar fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      Pair.noConfusion (inwZeroElim inw))
    (fun inw =>
      let ⟨_, inw⟩ := inwArbUnElim inw
      let ⟨_, inw⟩ := inwPairElim inw
      let ⟨_, inw⟩ := inwPairElim inw
      inwZeroElim inw)
    (nopeInterpPair fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpCpl fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpIfThen fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpArbUn fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))
    (nopeInterpArbIr fun inw =>
      let ⟨inw, _⟩ := inwPairElim inw
      inwNatExprElimNope inw (by decide))

def elimExternalPair
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
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (pairExpr left rite) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
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
      (nopeInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIfThen fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalUn
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra b c (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.un left rite) d))
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
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.un left rite) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
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
      (nopeInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIfThen fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalIr
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.ir left rite) d))
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
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.ir left rite) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpUn fun inw =>
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
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIfThen fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalCpl
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
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.cpl expr) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIr fun inw =>
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
      (nopeInterpIfThen fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalIfThen
  {cond}
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.ifThen cond body) d))
:
  And
    (∃ dCond,
      Set3.posMem
        (c uniDefList.interpretation)
        (InterpEnc boundVars cond dCond))
    (Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc boundVars body d))
:= by
  unfold InterpEnc
  exact
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.ifThen cond body) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (fun inw =>
        let ⟨condEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
        let ⟨bodyEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
        let ⟨boundVarsEnc, inw⟩ := inwArbUnElim inw
        let ⟨inwBv, inw⟩ := inwPairElim inw
        let bvEq := inwBoundElim inwBv
        let ⟨inwExprEnc, inw⟩ := inwPairElim inw
        let ⟨_, inwExprEnc⟩ := inwPairElim inwExprEnc
        let ⟨inwCond, inwBody⟩ := inwPairElim inwExprEnc
        let condEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                inwCond
                nat502Neq500)
              nat501Neq500)
        let bodyEq :=
          inwBoundElim
            (inwFreeElim
              inwBody
              nat502Neq501)
        let ⟨⟨dC, inwCond⟩, inwBody⟩ := inwIfThenElim inw
        let inwCond := inwCallElimBound inwCond rfl nat503Neq500
        let inwCond := inwCallElimBound inwCond rfl nat504Neq502
        let inwBody := inwCallElimBound inwBody rfl nat503Neq501
        let inwBody := inwCallElimBound inwBody rfl nat504Neq502
        bvEq ▸ condEq ▸ bodyEq ▸ ⟨⟨dC, inwCond⟩, inwBody⟩)
      (nopeInterpArbUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalArbUn
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.Un x body) d))
:
  ∃ dX,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  exact
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.Un x body) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIfThen fun inw =>
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
      (nopeInterpArbIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))

def elimExternalArbIr
  (inw:
    Set3.posMem
      (interpretation
        pairSalgebra
          b
          c
          (uniDefList.interpretation.expr))
      (InterpEnc boundVars (Expr.Ir x body) d))
:
  ∀ dX,
    Set3.posMem
      (c uniDefList.interpretation)
      (InterpEnc (⟨dX, x⟩ :: boundVars) body d)
:= by
  unfold InterpEnc
  intro dX
  exact
    @inwFinUnElim
      pairSignature
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprList
      (InterpEnc boundVars (Expr.Ir x body) d)
      _
      inw
      (nopeInterpVar fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        Pair.noConfusion (inwZeroElim inw))
      (nopeInterpZero fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpPair fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpUn fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIr fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpCpl fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpIfThen fun inw =>
        let ⟨inw, _⟩ := inwPairElim inw
        inwNatExprElimNope inw (by decide))
      (nopeInterpArbUn fun inw =>
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

def Cause.boundVarSat
  (isGetBound:
    Pair.uniSet3.IsGetBound
      (boundVarsEncoding boundVars)
      (fromNat x)
      d)
:
  (Cause.var x d).SatisfiesBoundVars boundVars
:=
  fun {xx _xxEnc _dd} xxEncEq isBound =>
    if h: xx = x then
      let dEq := isGetBound.isUnique (h ▸ xxEncEq ▸ isBound)
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
  (notBound:
    ¬∃ dB, IsGetBound (boundVarsEncoding boundVars) (fromNat x) dB)
:
  (Cause.var x d).SatisfiesBoundVars boundVars
:=
  fun xxEncEq isBound => {
    cinsSat := fun _ ⟨_, eqVvX⟩ xxEq =>
      False.elim
        (notBound ⟨_, eqVvX ▸ xxEq ▸ xxEncEq ▸ isBound⟩)
    binsSat := nofun
    boutSat := nofun
  }

def Cause.emptySat
  (boundVars: List (ValVar Pair))
:
  Cause.empty.SatisfiesBoundVars boundVars
:=
  fun _ _ => {
    cinsSat := nofun
    binsSat := nofun
    boutSat := nofun
  }
