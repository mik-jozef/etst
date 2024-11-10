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


def Cause.minBoundVars
  (boundVars: List (ValVar Pair))
:
  Cause Pair
:= {
  contextIns :=
    fun ⟨d, x⟩ => IsGetBound (boundVarsEncoding boundVars) x d
  backgroundIns :=
    fun ⟨d, x⟩ => IsGetBound (boundVarsEncoding boundVars) x d
  backgroundOut := fun ⟨d, x⟩ =>
    ∃ dBound,
      dBound ≠ d ∧
      IsGetBound (boundVarsEncoding boundVars) x dBound
}

def Cause.minBoundVarsSat
  (boundVars: List (ValVar Pair))
:
  (minBoundVars boundVars).SatisfiesBoundVars boundVars
:=
  fun xEncEq isGetBound => {
    cinsSat := fun _ inCins xEq =>
      inCins.isUnique (xEq ▸ xEncEq ▸ isGetBound)
    binsSat := fun _ inBins xEq =>
      inBins.isUnique (xEq ▸ xEncEq ▸ isGetBound)
    boutSat := fun _ ⟨_dBound, dNeq, isGetBound1⟩ xEq dEq =>
      (dEq ▸ dNeq)
        (isGetBound1.isUnique (xEq ▸ xEncEq ▸ isGetBound))
  }

def Cause.minBoundVarsWeakCause
  (boundVars: List (ValVar Pair))
  (isGetBound:
    IsGetBound (boundVarsEncoding boundVars) (fromNat x) d)
:
  IsWeakCause pairSalgebra (minBoundVars boundVars) d x
:=
  fun isSat => isSat.contextInsHold isGetBound


def Cause.minBvAndVar
  (boundVars: List (ValVar Pair))
  (x: Nat)
  (d: Pair)
:
  Cause Pair
:=
  (Cause.minBoundVars boundVars).union (Cause.var x d)

def Cause.minBvAndVarSat
  (boundVars: List (ValVar Pair))
  (notBound:
    ¬ ∃ d, IsGetBound (boundVarsEncoding boundVars) (fromNat x) d)
  (d: Pair)
:
  Cause.SatisfiesBoundVars
    (minBvAndVar boundVars x d)
    boundVars
:=
  Cause.SatisfiesBoundVars.union
    (Cause.minBoundVarsSat boundVars)
    (fun {_xx _xxEnc dd} eqXxEnc isBound =>
      {
        cinsSat :=
          -- Lean improvement idea: make ⟨_, _⟩ unnecessary.
          fun ⟨_, _⟩ ⟨_, eqAliasX⟩ eqAliasXx =>
            let eqX := eqAliasX.symm.trans eqAliasXx
            False.elim (notBound ⟨dd, eqX ▸ eqXxEnc ▸ isBound⟩)
        binsSat := fun ⟨_, _⟩ nope => nope.elim
        boutSat := fun ⟨_, _⟩ nope => nope.elim
      })

def Cause.minBvAndVarWeakCause
  (boundVars: List (ValVar Pair))
  (x: Nat)
  (d: Pair)
:
  IsWeakCause pairSalgebra (minBvAndVar boundVars x d) d x
:=
  fun isSat => isSat.contextInsHold (Or.inr ⟨rfl, rfl⟩)


def Cause.minBvCinsNopeFree
  (inCins: (Cause.minBoundVars boundVars).contextIns ⟨d, x⟩)
  (isFree: IsVarFree x boundVars)
:
  P
:=
  isFree.nopeGetBound inCins

def Cause.minBvBinsNopeFree
  (inBins: (Cause.minBoundVars boundVars).backgroundIns ⟨d, x⟩)
  (isFree: IsVarFree x boundVars)
:
  P
:=
  isFree.nopeGetBound inBins

def Cause.minBvBoutNopeFree
  {P: Prop}
  (inBout: (Cause.minBoundVars boundVars).backgroundOut ⟨d, x⟩)
  (isFree: IsVarFree x boundVars)
:
  P
:=
  let ⟨_, _, isGetBound⟩ := inBout
  isFree.nopeGetBound isGetBound


def Cause.inVarOfIsFree
  (inCins: (Cause.minBvAndVar boundVars x d).contextIns ⟨dd, xx⟩)
  (isFree: IsVarFree xx boundVars)
:
  dd = d ∧ xx = x
:=
  inCins.elim
    (minBvCinsNopeFree · isFree)
    id

def Cause.minBvAndVarBinsNopeFree
  (inBins: (Cause.minBvAndVar boundVars x d).backgroundIns ⟨dd, xx⟩)
  (isFree: IsVarFree xx boundVars)
:
  P
:=
  inBins.elim
    (minBvBinsNopeFree · isFree)
    False.elim

def Cause.minBvAndVarBoutNopeFree
  (inBout: (Cause.minBvAndVar boundVars x d).backgroundOut ⟨dd, xx⟩)
  (isFree: IsVarFree xx boundVars)
:
  P
:=
  inBout.elim
    (minBvBoutNopeFree · isFree)
    False.elim
