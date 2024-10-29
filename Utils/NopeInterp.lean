/-
  Various boring helpers related to the interpretation defined in
  the external definition list of Chapter 7.
-/

import UniSet3.Ch8_S12_DefListToEncoding
import Utils.PairExpr

open Expr
open Pair
open PairExpr


def interpretationInExprList.exprVar:
  uniDefList.interpretation.exprVar
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprZero:
  uniDefList.interpretation.exprZero
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprPair:
  uniDefList.interpretation.exprPair
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprUn:
  uniDefList.interpretation.exprUnion
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprIr:
  uniDefList.interpretation.exprIntersection
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprCpl:
  uniDefList.interpretation.exprCpl
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.exprIfThen:
  uniDefList.interpretation.exprIfThen
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.arbUn:
  uniDefList.interpretation.exprArbUnion
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def interpretationInExprList.arbIr:
  uniDefList.interpretation.exprArbIntersection
    ∈
  uniDefList.interpretation.exprList
:=
  by unfold uniDefList.interpretation.exprList; simp

def nopeInterpVar
  {P: Prop}
  (ninw:
    {d500 d501: Pair} →
    Not
      (InwP
        ((b.update 500 d500).update 501 d501)
        ((c.update 500 d500).update 501 d501)
        (pairExpr zeroExpr 500)
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprVar
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpZero
  {P: Prop}
  (ninw:
    {d501: Pair} →
    Not
      (InwP
        (b.update 501 d501)
        (c.update 501 d501)
        (pairExpr (natExpr 1) zeroExpr)
        (exprToEncoding expr).val))
  (nope:
    Inw
      pairSalgebra
      b
      c
      uniDefList.interpretation.exprZero
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, inw⟩ := inwArbUnElim nope
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpPair
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 2) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprPair
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpUn
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 3) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprUnion
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpIr
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 4) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprIntersection
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpCpl
  {P: Prop}
  (ninw:
    {d500 d502: Pair} →
    Not
      (InwP
        ((b.update 500 d500).update 502 d502)
        ((c.update 500 d500).update 502 d502)
        (pairExpr (natExpr 5) 500)
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprCpl
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpIfThen
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 6) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprIfThen
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpArbUn
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 7) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprArbUnion
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim

def nopeInterpArbIr
  {P: Prop}
  (ninw:
    {d500 d501 d502: Pair} →
    Not
      (InwP
        (((b.update 500 d500).update 501 d501).update 502 d502)
        (((c.update 500 d500).update 501 d501).update 502 d502)
        (pairExpr (natExpr 8) (pairExpr 500 501))
        (exprToEncoding expr).val))
  (nope:
    Inw pairSalgebra b c
      uniDefList.interpretation.exprArbIntersection
      (InterpEnc boundVars expr d))
:
  P
:=
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim nope
  let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
  let ⟨_, inw⟩ := inwArbUnElim inw
  let ⟨_, inw⟩ := inwPairElim inw
  let ⟨inw, _⟩ := inwPairElim inw
  (ninw inw).elim
