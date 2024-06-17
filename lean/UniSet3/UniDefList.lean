/-
  Consider these definitions:
  
  ```
    def call (fn arg: Set Pair): Set Pair :=
      { ret | ∃ a ∈ arg, (a, ret) ∈ fn }
    
    def call3 (fn arg: Set3 Pair): Set Pair := {
      defMem := call fn.defMem arg.defMem
      posMem := call fn.posMem arg.posMem
      defLePos := by [monotonicity of call]
    }
  ```
  
  In this file, we define the triset `t` of all definable trisets
  of pairs, in the sense that for any definable triset `tDef`,
  there exists a triset `tIndex` such that `tDef = call3 t tIndex`.
  
  We show that this triset is itself definable by constructing
  a definition list that defines it.
-/

import Utils.LeN37
import Utils.PairExpr
import Utils.PairFreeVars
import WFC.Ch4_Operators
import WFC.Ch5_PairSalgebra


namespace Pair
  open pairSignature
  open Expr
  open PairExpr
  
  instance exprOfNat: (n: Nat) → OfNat Expr n :=
    PairExpr.exprOfNat
  
  -- Convention: bound variables start at 500.
  namespace uniDefList
    /-
      Contains exactly the pairs that encode natural numbers.
      nat = () | (nat, ())
    -/
    def nat: Nat := 0
    def nat.expr := Expr.un zeroExpr (pairExpr nat zeroExpr)
    
    /-
      Contains (a, a) iff a is a natural number.
      natPairAA = Un n: nat, (n, n)
    -/
    def natPairAA: Nat := 1
    def natPairAA.expr := unionExpr 500 nat (pairExpr 500 500)
    
    /-
      Contains (a, b) iff a and b are naturals st. a ≤ b.
      natLe = natPairAA | Ex (a, b): natLe, (a, succ b)
    -/
    def natLe: Nat := 2
    def natLe.expr :=
      Expr.un
        natPairAA
        (unionExpr 500 natLe
          (pairExpr
            (zthMember 501 500)
            (succExpr (fstMember 501 500))))
    
    /-
      Contains (0, n) for natural n.
      expr.var = Un n: nat, ((), n)
    -/
    def exprEncoding.var: Nat := 3
    def exprEncoding.var.expr: Expr :=
      unionExpr 500 nat (pairExpr zeroExpr 500)
    
    /-
      Contains (1, ()).
    -/
    def exprEncoding.zero: Nat := 4
    def exprEncoding.zero.expr: Expr :=
      (pairExpr (natExpr 1) zeroExpr)
    
    /-
      Contains the triset { 2, 3, 4, 6 }.
    -/
    def exprEncoding.binary: Nat := 5
    def exprEncoding.binary.expr: Expr :=
      Expr.un
        (natExpr 2)
        (Expr.un
          (natExpr 3)
          ((Expr.un (natExpr 4) (natExpr 6))))
    
    /-
      Contains the triset { 7, 8 }.
    -/
    def exprEncoding.quantifier: Nat := 6
    def exprEncoding.quantifier.expr: Expr :=
      Expr.un (natExpr 7) (natExpr 8)
    
    def exprEncoding: Nat := 7
    def exprEncoding.binExpr :=
      pairExpr
        exprEncoding.binary
        (pairExpr exprEncoding exprEncoding)
    def exprEncoding.cplExpr :=
      pairExpr (natExpr 5) exprEncoding
    def exprEncoding.quantifierExpr :=
      pairExpr
        exprEncoding.quantifier
        (pairExpr nat exprEncoding)
    
    /-
      Contains all pairs that encode an expression.
      
      Expressions are encoded like this:
      | var (v: Nat)                 => (0, v)
      | op (op: zero) (args)         => (1, ())
      | op (op: pair) (args)         => (2, (args 0, args 1))
      | un (left rite: Expr sig)     => (3, (left, rite))
      | ir (left rite: Expr sig)     => (4, (left, rite))
      | cpl (expr: Expr sig)         => (5, expr)
      | ifThen (cond expr: Expr sig) => (6, (cond, expr))
      | Un (x: Nat) (body: Expr sig) => (7, (x, body))
      | Ir (x: Nat) (body: Expr sig) => (8, (x, body))
    -/
    def exprEncoding.exprList: List Expr :=
      [
        Expr.var exprEncoding.var,
        Expr.var exprEncoding.zero,
        binExpr,
        cplExpr,
        quantifierExpr,
      ]
    def exprEncoding.expr := finUnExpr exprList
    
    /-
      Contains all pairs that encode a finite prefix of a definition
      list -- ie. a list of expressions.
      
      The empty list is encoded as (), and `head :: tail` as
      `pair head tailEncoding`.
    -/
    def defEncoding: Nat := 8
    def defEncoding.expr: Expr :=
      Expr.un zeroExpr (pairExpr exprEncoding defEncoding)
    
    /-
      Contains (a, b) with a and b being pairs such that a < b
      in the dictionary order. Base case: () < (a, b).
    -/
    def pairDictLt: Nat := 9
    def pairDictLt.zeroPair: Expr :=
      pairExpr zeroExpr (pairExpr anyExpr anyExpr)
    def pairDictLt.ltLeft: Expr :=
      unionExpr 500 pairDictLt
        (pairExpr
          (pairExpr (zthMember 502 500) anyExpr)
          (pairExpr (fstMember 502 500) anyExpr))
    def pairDictLt.eqLeft: Expr :=
      unionExpr 500 pairDictLt
        (Expr.Un 501
          (pairExpr
            (pairExpr 501 (zthMember 502 500))
            (pairExpr 501 (fstMember 502 500))))
    def pairDictLt.list: List Expr := [
      zeroPair,
      ltLeft,
      eqLeft,
    ]
    
    def pairDictLt.expr: Expr :=
      finUnExpr list
    
    /-
      Contains (n, m) such that m ≤ n, n and m being natural
      numbers.
    -/
    def natLeFn: Nat := 10
    def natLeFn.expr: Expr :=
      unionExpr 500 natLe
        (pairExpr (fstMember 501 500) (zthMember 501 500))
    
    /-
      Contains (n, p) such that p is a pair and n an encoding of
      its depth.
    -/
    def pairOfDepth: Nat := 11
    def pairOfDepth.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nat
          (unionExpr 501 (callExpr 502 pairOfDepth 500)
            (unionExpr 502
              (callExpr 503 pairOfDepth (callExpr 504 natLeFn 500))
              (Expr.un
                (pairExpr (succExpr 500) (pairExpr 501 502))
                (pairExpr (succExpr 500) (pairExpr 502 501))))))
    
    /-
      The "less than" relation on natural numbers.
    -/
    def natLt: Nat := 12
    def natLt.expr: Expr :=
      Expr.ir natLe (Expr.cpl (Expr.Un 500 (pairExpr 500 500)))
    
    /-
      Contains (a, b) if the pairs `a` and `b` have the same depth.
    -/
    def sameDepth: Nat := 13
    def sameDepth.expr: Expr :=
      unionExpr 500 nat
        (pairExpr
          (callExpr 501 pairOfDepth 500)
          (callExpr 501 pairOfDepth 500))
    
    /-
      Pairs ordered zeroth by depth and then by the
      dictionary order.
      
      Has the order type of naturals, since for any
      pair p, there is only finitely many pairs less
      than p.
    -/
    def pairLt: Nat := 14
    def pairLt.expr: Expr :=
      Expr.un
        (Expr.ir sameDepth pairDictLt)
        (unionExpr 500 natLt
          (pairExpr
            (callExpr 501 pairOfDepth (zthMember 502 500))
            (callExpr 501 pairOfDepth (fstMember 502 500))))
    
    /-
      The ordering `pairLt` restricted to deflist encodings.
    -/
    def defEncodingLt: Nat := 15
    def defEncodingLt.expr: Expr :=
      Expr.ir pairLt (pairExpr defEncoding defEncoding)
    
    /-
      Contains (a, b) iff `a < x < b` for some deflist encodings
      `a`, `b` and `x`.
    -/
    def defEncodingMinDist2: Nat := 16
    def defEncodingMinDist2.expr: Expr :=
      Expr.Un 500
        (Expr.Un 501
          (Expr.Un 502
            (Expr.ifThen
              (pairExpr
                (Expr.ir defEncodingLt (pairExpr 500 501))
                (Expr.ir defEncodingLt (pairExpr 501 502)))
              (pairExpr 500 502))))
    
    /-
      Contains (a, b) where `b` is the least defEncoding greater
      than `a`.
    -/
    def nextDef: Nat := 17
    def nextDef.expr: Expr :=
      Expr.ir
        defEncodingLt
        (Expr.cpl defEncodingMinDist2)
    
    /-
      Contains (n, dl), where `dl` is the `n`th least deflist
      encoding in the `defEncodingLt` order.
    -/
    def nthDefList: Nat := 18
    def nthDefList.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nthDefList
          (pairExpr
            (succExpr (zthMember 501 500))
            (callExpr 501 nextDef (fstMember 502 500))))
    
    -- See incrVarsExpr.
    def incrVarsExpr.var: Nat := 19
    def incrVarsExpr.var.expr: Expr :=
      unionExpr 500 nat
        (pairExpr
          (pairExpr zeroExpr 500)
          (pairExpr zeroExpr (succExpr 500)))
    
    /-
      Contains (eIn, eOut) such that `eIn` is an encoding
      of an expression and `eOut` is `eIn` with variables
      incremented by 1.
    -/
    def incrVarsExpr: Nat := 20
    
    def incrVarsExpr.opZero: Expr :=
      pairExpr exprEncoding.zero exprEncoding.zero
    
    def incrVarsExpr.binExpr: Expr :=
      unionExpr 500 exprEncoding.binary
        (unionExpr 501 exprEncoding
          (unionExpr 502 exprEncoding
            (pairExpr
              (pairExpr
                500
                (pairExpr 501 502))
              (pairExpr
                500
                (pairExpr
                  (callExpr 503 incrVarsExpr 501)
                  (callExpr 503 incrVarsExpr 502))))))
    
    def incrVarsExpr.cplExpr: Expr :=
      unionExpr 501 exprEncoding
        (pairExpr
          (pairExpr (natExpr 5) 501)
          (pairExpr (natExpr 5)
            (callExpr 503 incrVarsExpr 501)))
    
    def incrVarsExpr.quantifierExpr: Expr :=
      unionExpr 500 exprEncoding.quantifier
        (unionExpr 501 exprEncoding
          (unionExpr 502 nat
            (pairExpr
              (pairExpr
                500
                (pairExpr 502 501))
              (pairExpr
                500
                (pairExpr
                  (succExpr 502)
                  (callExpr 503 incrVarsExpr 501))))))
    
    def incrVarsExpr.exprList: List Expr := [
      incrVarsExpr.var,
      opZero,
      binExpr,
      cplExpr,
      quantifierExpr,
    ]
    
    def incrVarsExpr.expr: Expr := finUnExpr exprList
    
    /-
      (dlIn, dlOut) where `dlIn` equals `dlOut` except that the
      variables of `dlOut` are incremented by 1.
    -/
    def incrVarsDefEncoding: Nat := 21
    def incrVarsDefEncoding.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 exprEncoding
          (unionExpr 501 defEncoding
            (pairExpr
              (pairExpr 500 501)
              (pairExpr
                (callExpr 502 incrVarsExpr 500)
                (callExpr 502 incrVarsDefEncoding 501)))))
    
    /-
      (n, (dlIn, dlOut)) where `dlOut` is `dlIn` with variables
      incremented by n.
    -/
    def shiftDefEncoding: Nat := 22
    def shiftDefEncoding.expr: Expr :=
      Expr.un
        (unionExpr 500 defEncoding
          (pairExpr zeroExpr (pairExpr 500 500)))
        (unionExpr 500 nat
          (unionExpr 501 defEncoding
            (pairExpr
              (succExpr 500)
              (pairExpr
                501
                (callExpr 502
                  incrVarsDefEncoding
                  (callExpr 503
                    (callExpr 504 shiftDefEncoding 500)
                    501))))))
    
    /-
      (dl, expr), where `dl` is (an encoding of a prefix of)
      a definition list of length one, and `expr` is the only its
      expression.
    -/
    def lastExpr.base: Nat := 23
    def lastExpr.base.expr: Expr :=
      unionExpr 500 exprEncoding
        (pairExpr
          (pairExpr 500 zeroExpr)
          500)
    
    /-
      (dl, expr), where `expr` is the last expression of (the
      encoding of) a prefix of a definition list `dl`.
    -/
    def lastExpr: Nat := 24
    def lastExpr.expr: Expr :=
      Expr.un
        lastExpr.base
        (unionExpr 500 lastExpr
          (pairExpr
            (pairExpr exprEncoding (zthMember 501 500))
            (fstMember 501 500)))
    
    /-
      (dlIn, dlOut), where `dlOut` contains all but the last
      definition of `dlIn`.
      
      For every encoding of a definition list `dl`,
      
          dl = [ ...upToLast(dl), lastExpr(dl) ] \,.
    -/
    def upToLast: Nat := 25
    def upToLast.expr: Expr :=
      Expr.un
        (pairExpr (pairExpr exprEncoding zeroExpr) zeroExpr)
        (unionExpr 500 upToLast
          (unionExpr 501 exprEncoding
            (pairExpr
              (pairExpr 501 (zthMember 502 500))
              (pairExpr 501 (fstMember 502 500)))))
    
    /-
      (dlA, (dlB, dlRes)), where `dlRes = [ ...dlA, ...dlB ]`.
      
      Array append on definition lists. Variables are not affected,
      breaking the semantics of the latter one. This gets fixed
      below.
    -/
    def arrayAppend: Nat := 26
    def arrayAppend.expr: Expr :=
      (Expr.un
        (pairExpr
          zeroExpr
          (unionExpr 500 defEncoding
            (pairExpr 500 500)))
        (unionExpr 500 defEncoding
          (unionExpr 501 defEncoding
            (pairExpr
              500
              (pairExpr
                501
                (callExpr 502
                  (callExpr 503 arrayAppend (callExpr 504 upToLast 500))
                  (pairExpr
                    (callExpr 503 lastExpr 500)
                    501)))))))
    
    /-
      (arr, n), where `arr` is an array of length `n`.
      
      Note that every pair encodes some array.
    -/
    def arrayLength: Nat := 27
    def arrayLength.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (Expr.Un 500
          (pairExpr
            (pairExpr anyExpr 500)
            (succExpr (callExpr 501 arrayLength 500))))
    
    /-
      The append operation on definition lists is a combination
      of the array append operation and the shift operation on
      the first (not the zeroth) array. Unlike array append, this
      operation preserves the internal structure of both definition
      lists, because the variables of the latter are shifted by
      the length of the former.
      
      Contains (dlA, (dlB, dlRes)), where
      
          dlRes = [ ...dlA, ...shift(dlA.length, dlB) ] \,.
    -/
    def append: Nat := 28
    def append.expr: Expr :=
      unionExpr 500 defEncoding
        (unionExpr 501 defEncoding
          (pairExpr
            500
            (pairExpr
              501
              (callExpr 502
                (callExpr 503 arrayAppend 500)
                (callExpr 503
                  (callExpr 504 shiftDefEncoding
                    (callExpr 505 arrayLength 500))
                  501)))))
    
    /-
      Contains (n, dl), such that dl is a (finite prefix of a)
      definition list consisting of the zeroth n definition list
      prefixes joined together.
      
      (Deflist prefixes are ordered by `defEncodingLt`.)
      
      For any two deflists returned by `enumUpTo`, one is a prefix
      of the other. Every finite prefix of every definition list
      is contained in some deflist prefix returned by `enumUpTo`.
    -/
    def enumUpTo: Nat := 29
    def enumUpTo.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nat
          (pairExpr
            (pairExpr 500 zeroExpr)
            (callExpr 501
              (callExpr 502 append
                (callExpr 503 enumUpTo 500))
              (callExpr 502 nthDefList 500))))
    
    /-
      Contains (dl, (n, e)) such that `e` is the nth expression
      of the definition list encoding `dl`.
    -/
    def defListToSet: Nat := 30
    def defListToSet.expr: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 defEncoding
          (Expr.un
            (pairExpr
              (pairExpr 500 501)
              (pairExpr zeroExpr 500))
            (unionExpr 502 nat
              (pairExpr
                (pairExpr 500 501)
                (pairExpr
                  (succExpr 502)
                  (callExpr 503 (callExpr 504 defListToSet 501) 502))))))
    
    /-
      Contains all deflists of enumUpTo.
      
      Recall that for every pair of elements of enumUpTo, one is
      a prefix of the other. This guarantees that for any two
      definition lists of `theDlPrefixes` (of sufficient length),
      and any n, their nth expressions are the same.
      
      This in turn means that `theDlPrefixes` represents a unique
      definition list (not just some finite prefix of it), which
      contains all definitions up to structural equivalence.
      Every definable triset is therefore defined in this definition
      list.
    -/
    def theDlPrefixes: Nat := 31
    def theDlPrefixes.expr: Expr :=
      unionExpr 500 nat
        (callExpr 501 enumUpTo 500)
    
    /-
      Contains (n, expr) where `expr` is the `n`th expression in
      any `dl` in `theDlPrefixes`.
      
      This is a different representation of the definition list
      represented by `theDlPrefixes`. While `theDlPrefixes` contains
      its finite prefixes, `theDefList` contains its index-expression
      pairs.
    -/
    def theDefList: Nat := 32
    def theDefList.expr: Expr :=
      unionExpr 500 theDlPrefixes
        (callExpr 501 defListToSet 500)
    
    /-
      Contains ([(n, p), ...], (n, p)) for natural `n`.
    -/
    def getBound.baseExpr: Expr :=
      unionExpr 500 nat
        (Expr.Un 501
          (pairExpr
            (pairExpr (pairExpr 500 501) anyExpr)
            (pairExpr 500 501)))
    
    /-
      Contains (arr, (n, p)) such that `arr` is a list containing
      (n, p).
    -/
    def getBound: Nat := 33
    def getBound.expr: Expr :=
      Expr.un
        getBound.baseExpr
        (Expr.Un 500
          (Expr.Un 501
            (pairExpr
              (pairExpr
                (pairExpr (Expr.cpl 500) anyExpr)
                501)
              (pairExpr
                500
                (callExpr 502
                  (callExpr 503 getBound 501)
                  500)))))
    
    /-
      Contains (bound, expr, p) where bound is an array of
      variable-pair pairs (bound vars), `expr` is an expression
      and `p` is a member of the interpretation of `expr` with
      `theSet` (below) serving as the valuation (of free variables).
      
      The triple is contained strongly iff `p` is a definitive
      member of the interpretation, else it is contained
      weakly.
    -/
    def interpretation: Nat := 34
    
    /-
      Contains (expr, s) where `s` is the interpretation of `expr`
      with `theSet` serving as the valuation.
    -/
    def freeInterpretation := 35
    
    /-
      A set of pairs (n, s) where `n` is a natural number. For
      every definable triset of pairs `dtp`, there exists a natural
      number `n` such that for every pair `p`,
      
          (n, p) ∈ theSet = p ∈ dtp \,.
    -/
    def theSet: Nat := 36
    
    def interpretation.exprVar: Expr :=
      unionExpr 500 nat
        (Expr.Un 501
          (pairExpr
            501
            (pairExpr
              (pairExpr zeroExpr 500)
              (Expr.un
                (callExpr 502 (callExpr 503 getBound 501) 500)
                (/- if 500 is a free var -/ Expr.ifThen
                  (Expr.cpl
                    -- Turning a nonempty type into the universal
                    -- type, so that it may be complemented to test
                    -- for emptiness.
                    (Expr.ifThen
                      (callExpr 502 (callExpr 503 getBound 501) 500)
                      anyExpr))
                  (callExpr 502 theSet 500))))))
    
    def interpretation.exprZero: Expr :=
      Expr.Un 501
        (pairExpr
          501
          (pairExpr
            (pairExpr (natExpr 1) zeroExpr)
            zeroExpr))
    
    def interpretation.exprPair: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 2) (pairExpr 500 501))
                (pairExpr
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprUnion: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 3) (pairExpr 500 501))
                (Expr.un
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprIntersection: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 4) (pairExpr 500 501))
                (Expr.ir
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprCpl: Expr :=
      unionExpr 500 exprEncoding
        (Expr.Un 502
          (pairExpr
            502
            (pairExpr
              (pairExpr (natExpr 5) 500)
              (Expr.cpl
                (callExpr 503 (callExpr 504 interpretation 502) 500)))))
    
    def interpretation.exprIfThen: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 6) (pairExpr 500 501))
                (Expr.ifThen
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprArbUnion: Expr :=
      unionExpr 500 nat
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 7) (pairExpr 500 501))
                (Expr.Un 503
                  (callExpr 504
                    (callExpr 505
                      interpretation
                      (pairExpr (pairExpr 500 503) 502))
                    501))))))
    
    def interpretation.exprArbIntersection: Expr :=
      unionExpr 500 nat
        (unionExpr 501 exprEncoding
          (Expr.Un 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 8) (pairExpr 500 501))
                (Expr.Ir 503
                  (callExpr 504
                    (callExpr 505
                      interpretation
                      (pairExpr (pairExpr 500 503) 502))
                    501))))))
    
    def interpretation.exprList: List Expr := [
      exprVar,
      exprZero,
      exprPair,
      exprUnion,
      exprIntersection,
      exprCpl,
      exprIfThen,
      exprArbUnion,
      exprArbIntersection,
    ]
    
    def interpretation.expr: Expr := finUnExpr exprList
    
    def freeInterpretation.expr :=
      callExpr 502 interpretation zeroExpr
    
    def theSet.expr: Expr :=
      unionExpr 500 nat
        (pairExpr 500
          (callExpr 501
            freeInterpretation
            (callExpr 502 theDefList 500)))
    
    def defList.getDef: Nat → Expr
    | 0 => nat.expr
    | 1 => natPairAA.expr
    | 2 => natLe.expr
    | 3 => exprEncoding.var.expr
    | 4 => exprEncoding.zero.expr
    | 5 => exprEncoding.binary.expr
    | 6 => exprEncoding.quantifier.expr
    | 7 => exprEncoding.expr
    | 8 => defEncoding.expr
    | 9 => pairDictLt.expr
    | 10 => natLeFn.expr
    | 11 => pairOfDepth.expr
    | 12 => natLt.expr
    | 13 => sameDepth.expr
    | 14 => pairLt.expr
    | 15 => defEncodingLt.expr
    | 16 => defEncodingMinDist2.expr
    | 17 => nextDef.expr
    | 18 => nthDefList.expr
    | 19 => incrVarsExpr.var.expr
    | 20 => incrVarsExpr.expr
    | 21 => incrVarsDefEncoding.expr
    | 22 => shiftDefEncoding.expr
    | 23 => lastExpr.base.expr
    | 24 => lastExpr.expr
    | 25 => upToLast.expr
    | 26 => arrayAppend.expr
    | 27 => arrayLength.expr
    | 28 => append.expr
    | 29 => enumUpTo.expr
    | 30 => defListToSet.expr
    | 31 => theDlPrefixes.expr
    | 32 => theDefList.expr
    | 33 => getBound.expr
    | 34 => interpretation.expr
    | 35 => freeInterpretation.expr
    | 36 => theSet.expr
    | _rest + 37 => zeroExpr
    
    def defList.usedVarsLt38
      (usedVar: IsFreeVar (getDef a) Set.empty)
    :
      usedVar.val < 38
    :=
      let prf
        (x: Nat)
        (fv: List Nat)
        (fvEq: (freeVars (getDef x)).val = fv)
        (allLe: ∀ {x} (_: x ∈ fv), x ≤ 37)
        (usedByX: IsFreeVar (getDef x) Set.empty)
      :
        usedByX.val < 38
      :=
        let freeVars := freeVars (getDef x)
        let xIn: ↑usedByX ∈ fv := fvEq ▸ freeVars.property usedByX
        Nat.lt_succ_of_le (allLe xIn)
      
      match a with
      | 0 => prf 0 [ 0 ] rfl (by simp) usedVar
      | 1 => prf 1 [ 0 ] rfl (by simp) usedVar
      | 2 => prf 2 [ 1, 2 ] rfl (by simp[leN37]) usedVar
      | 3 => prf 3 [ 0 ] rfl (by simp) usedVar
      | 4 => prf 4 [] rfl (by simp) usedVar
      | 5 => prf 5 [] rfl (by simp) usedVar
      | 6 => prf 6 [] rfl (by simp) usedVar
      | 7 => prf 7 [ 3, 4, 5, 7, 6, 0 ] rfl (by simp[leN37]) usedVar
      | 8 => prf 8 [ 7, 8 ] rfl (by simp[leN37]) usedVar
      | 9 => prf 9 [ 9 ] rfl (by simp[leN37]) usedVar
      | 10 => prf 10 [ 2 ] rfl (by simp[leN37]) usedVar
      | 11 => prf 11 [ 0, 11, 10 ] rfl (by simp[leN37]) usedVar
      | 12 => prf 12 [ 2 ] rfl (by simp[leN37]) usedVar
      | 13 => prf 13 [ 0, 11 ] rfl (by simp[leN37]) usedVar
      | 14 => prf 14 [ 13, 9, 12, 11 ] rfl (by simp[leN37]) usedVar
      | 15 => prf 15 [ 14, 8 ] rfl (by simp[leN37]) usedVar
      | 16 => prf 16 [ 15 ] rfl (by simp[leN37]) usedVar
      | 17 => prf 17 [ 15, 16 ] rfl (by simp[leN37]) usedVar
      | 18 => prf 18 [ 18, 17 ] rfl (by simp[leN37]) usedVar
      | 19 => prf 19 [ 0 ] rfl (by simp[leN37]) usedVar
      | 20 => prf 20 [ 19, 4, 5, 7, 20, 6, 0 ] rfl (by simp[leN37]) usedVar
      | 21 => prf 21 [ 7, 8, 20, 21 ] rfl (by simp[leN37]) usedVar
      | 22 => prf 22 [ 8, 0, 21, 22 ] rfl (by simp[leN37]) usedVar
      | 23 => prf 23 [ 7 ] rfl (by simp[leN37]) usedVar
      | 24 => prf 24 [ 23, 24, 7 ] rfl (by simp[leN37]) usedVar
      | 25 => prf 25 [ 7, 25 ] rfl (by simp[leN37]) usedVar
      | 26 => prf 26 [ 8, 26, 25, 24 ] rfl (by simp[leN37]) usedVar
      | 27 => prf 27 [ 27 ] rfl (by simp[leN37]) usedVar
      | 28 => prf 28 [ 8, 26, 22, 27 ] rfl (by simp[leN37]) usedVar
      | 29 => prf 29 [ 0, 28, 29, 18 ] rfl (by simp[leN37]) usedVar
      | 30 => prf 30 [ 7, 8, 0, 30 ] rfl (by simp[leN37]) usedVar
      | 31 => prf 31 [ 0, 29 ] rfl (by simp[leN37]) usedVar
      | 32 => prf 32 [ 31, 30 ] rfl (by simp[leN37]) usedVar
      | 33 => prf 33 [ 0, 33 ] rfl (by simp[leN37]) usedVar
      | 34 => prf 34 [ 0, 33, 36, 7, 34 ] rfl (by simp[leN37]) usedVar
      | 35 => prf 35 [ 34 ] rfl (by simp[leN37]) usedVar
      | 36 => prf 36 [ 0, 35, 32 ] rfl (by simp[leN37]) usedVar
    
    def defList.hasFiniteBounds
      (dependsOn: DefList.DependsOn getDef a b)
    :
      b < max a.succ 38
    :=
      -- Git gud @ termination showing, Lean.
      -- match dependsOn with
      -- | DefList.DependsOn.Refl x =>
      --   lt_max_of_lt_left (Nat.lt_succ_self x)
      -- | DefList.DependsOn.Uses aUsesB bUsesC =>
      --   let ih := hasFiniteBounds bUsesC
      --   ...
      
      dependsOn.rec
        (fun x => lt_max_of_lt_left (Nat.lt_succ_self x))
        (fun aUsesB _ ih =>
          let bLt37 := usedVarsLt38 ⟨_, aUsesB⟩
          let maxEq := max_eq_right (Nat.succ_le_of_lt bLt37)
          lt_max_of_lt_right (maxEq ▸ ih))
    
    def defList:
      FinBoundedDL pairSignature
    := {
      getDef := defList.getDef
      
      isFinBounded :=
        fun x => ⟨
          max x.succ 38,
          defList.hasFiniteBounds,
        ⟩
    }
    
    noncomputable def wfModel :=
      defList.wellFoundedModel pairSalgebra
    
  end uniDefList  
end Pair
