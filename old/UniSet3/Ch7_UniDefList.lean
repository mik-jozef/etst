/-
  Volume 1: The Universal Set
  # Chapter 7: The Definition List of a Universal Triset
  
  Recall from Chapter 4 the definition of a definable triset
  (`Salgebra.IsDefinable`). In the chapters of this folder, we
  show that there exists a definable triset `uniSet3: Set3 Pair`
  that in a sense "contains" all definable trisets of pairs.
  
  More precisely, `uniSet3` is such that for any definable triset
  `tDef`, there exists an `index: Pair` such that for any `p`,
  
      p ∈ tDef ↔ (index, p) ∈ uniSet3 \,,
  
  where the above equivalence holds for both the definitive and
  possible membership.
  
  We show that `uniSet3` is itself definable by constructing a
  definition list that defines it. The traditional contradictions
  a la Russell are avoided thanks to the three-valued nature of
  trisets -- one cannot obtain a contradiction by diagonalization
  because the undetermined elements of a triset are undetermined
  in its complement as well.
  
  The existence of a triset with this property is the only result
  of this volume that we will use in the rest of the project. Those
  willing to skip the proof of correctness of the construction may
  skip all its chapters but this one, while those happy with just
  knowing that such a triset exists may skip the whole volume.
-/

import old.Utils.LeN37
import old.Utils.PairExpr
import old.Utils.PairFreeVars
import old.WFC.Ch6_S1_AProofSystem


namespace Pair
  open pairSignature
  open Expr
  open PairExpr
  
  instance exprOfNat: (n: Nat) → OfNat Expr n :=
    PairExpr.exprOfNat
  
  /-
    Here, we define the definitions of our definition list.
    
    By convention, bound variables start at 500. Also recall that
    in Chapter 5, we defined an encoding of natural numbers as
    pairs (`IsNatEncoding`).
  -/
  namespace uniDefList
    /-
      Contains exactly the pairs that encode natural numbers.
      
          nat = () | (nat, ())
    -/
    def nat: Nat := 0
    def nat.expr := unExpr zeroExpr (pairExpr nat zeroExpr)
    
    /-
      Contains (n, n) iff n is a natural number.
      
          natPairAA = Un n: nat, (n, n)
    -/
    def natPairAA: Nat := 1
    def natPairAA.expr := unionExpr 500 nat (pairExpr 500 500)
    
    /-
      Contains (n, m) iff n and m are naturals st. n ≤ m.
      
          natLe = natPairAA | Ex (n, m): natLe, (n, succ m)
    -/
    def natLe: Nat := 2
    def natLe.expr :=
      unExpr
        natPairAA
        (unionExpr 500 natLe
          (pairExpr
            (zthMember 501 500)
            (succExpr (fstMember 501 500))))
    
    -- Contains (0, n) for every natural n.
    def exprEncoding.var: Nat := 3
    def exprEncoding.var.expr: Expr :=
      (pairExpr zeroExpr nat)
    
    -- Contains (1, ()).
    def exprEncoding.zero: Nat := 4
    def exprEncoding.zero.expr: Expr :=
      (pairExpr (natExpr 1) zeroExpr)
    
    -- Contains the triset { 2, 3, 4 }.
    def exprEncoding.binary: Nat := 5
    def exprEncoding.binary.expr: Expr :=
      unExpr (natExpr 2) (unExpr (natExpr 3) (natExpr 4))
    
    -- Contains the triset { 5, 6, 7 }.
    def exprEncoding.unary: Nat := 6
    def exprEncoding.unary.expr: Expr :=
      unExpr (natExpr 5) (unExpr (natExpr 6) (natExpr 7))
    
    -- Contains the triset { 8, 9 }.
    def exprEncoding.quantifier: Nat := 7
    def exprEncoding.quantifier.expr: Expr :=
      unExpr (natExpr 8) (natExpr 9)
    
    -- Helpers for `exprEncoding.expr` below.
    def exprEncoding: Nat := 8
    def exprEncoding.unaryExpr :=
      pairExpr exprEncoding.unary exprEncoding
    def exprEncoding.binExpr :=
      pairExpr
        exprEncoding.binary
        (pairExpr exprEncoding exprEncoding)
    def exprEncoding.quantifierExpr :=
      pairExpr
        exprEncoding.quantifier
        (pairExpr nat exprEncoding)
    
    /-
      Contains all pairs that encode an expression.
      
      Expressions are encoded like this:
      | var (x: Nat)                 => (0, x)
      | zero                         => (1, ())
      | pair (left rite: Expr sig)   => (2, (left, rite))
      | un (left rite: Expr sig)     => (3, (left, rite))
      | ir (left rite: Expr sig)     => (4, (left, rite))
      | cpl (expr: Expr sig)         => (5, expr)
      | condSome (cond: Expr sig)    => (6, cond)
      | condFull (cond: Expr sig)    => (7, cond)
      | Un (x: Nat) (body: Expr sig) => (8, (x, body))
      | Ir (x: Nat) (body: Expr sig) => (9, (x, body))
    -/
    def exprEncoding.exprList: List Expr :=
      [
        Expr.var exprEncoding.var,
        Expr.var exprEncoding.zero,
        binExpr,
        unaryExpr,
        quantifierExpr,
      ]
    def exprEncoding.expr := finUnExpr exprList
    
    /-
      Contains all pairs that encode a prefix of a definition
      list -- ie. a list of expressions.
      
      The empty list is encoded as (), and `head :: tail` as
      `pair head tailEncoding`.
    -/
    def defEncoding: Nat := 9
    def defEncoding.expr: Expr :=
      unExpr zeroExpr (pairExpr exprEncoding defEncoding)
    
    /-
      Contains (a, b) with a and b being pairs such that a < b
      in the dictionary order. (Base case: () < (a, b).)
    -/
    def pairDictLt: Nat := 10
    def pairDictLt.zeroPair: Expr :=
      pairExpr zeroExpr (pairExpr anyExpr anyExpr)
    def pairDictLt.ltLeft: Expr :=
      unionExpr 500 pairDictLt
        (pairExpr
          (pairExpr (zthMember 502 500) anyExpr)
          (pairExpr (fstMember 502 500) anyExpr))
    def pairDictLt.eqLeft: Expr :=
      unionExpr 500 pairDictLt
        (Expr.arbUn 501
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
    def natLeFn: Nat := 11
    def natLeFn.expr: Expr :=
      unionExpr 500 natLe
        (pairExpr (fstMember 501 500) (zthMember 501 500))
    
    /-
      Contains (n, p) such that p is a pair and n an encoding of
      its depth.
    -/
    def pairOfDepth: Nat := 12
    def pairOfDepth.expr: Expr :=
      unExpr
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nat
          (unionExpr 501 (callExpr 502 pairOfDepth 500)
            (unionExpr 502
              (callExpr 503 pairOfDepth (callExpr 504 natLeFn 500))
              (unExpr
                (pairExpr (succExpr 500) (pairExpr 501 502))
                (pairExpr (succExpr 500) (pairExpr 502 501))))))
    
    /-
      The "less than" relation on natural numbers.
    -/
    def natLt: Nat := 13
    def natLt.expr: Expr :=
      irExpr natLe (Expr.cpl (Expr.arbUn 500 (pairExpr 500 500)))
    
    /-
      Contains (a, b) if the pairs `a` and `b` have the same depth.
    -/
    def sameDepth: Nat := 14
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
    def pairLt: Nat := 15
    def pairLt.expr: Expr :=
      unExpr
        (irExpr sameDepth pairDictLt)
        (unionExpr 500 natLt
          (pairExpr
            (callExpr 501 pairOfDepth (zthMember 502 500))
            (callExpr 501 pairOfDepth (fstMember 502 500))))
    
    /-
      The ordering `pairLt` restricted to deflist encodings.
    -/
    def defEncodingLt: Nat := 16
    def defEncodingLt.expr: Expr :=
      irExpr pairLt (pairExpr defEncoding defEncoding)
    
    /-
      Contains (a, b) iff `a < x < b` for some deflist encodings
      `a`, `b` and `x`.
    -/
    def defEncodingMinDist2: Nat := 17
    def defEncodingMinDist2.expr: Expr :=
      Expr.arbUn 500
        (Expr.arbUn 501
          (Expr.arbUn 502
            (ifThenExpr
              (pairExpr
                (irExpr defEncodingLt (pairExpr 500 501))
                (irExpr defEncodingLt (pairExpr 501 502)))
              (pairExpr 500 502))))
    
    /-
      Contains (a, b) where `b` is the least defEncoding greater
      than `a`.
    -/
    def nextDef: Nat := 18
    def nextDef.expr: Expr :=
      irExpr
        defEncodingLt
        (Expr.cpl defEncodingMinDist2)
    
    /-
      Contains (n, dl), where `dl` is the `n`th least deflist
      encoding in the `defEncodingLt` order.
    -/
    def nthDefList: Nat := 19
    def nthDefList.expr: Expr :=
      unExpr
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nthDefList
          (pairExpr
            (succExpr (zthMember 501 500))
            (callExpr 501 nextDef (fstMember 502 500))))
    
    -- See incrVarsExpr.
    def incrVarsExpr.var: Nat := 20
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
    def incrVarsExpr: Nat := 21
    
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
    
    def incrVarsExpr.unaryExpr: Expr :=
      unionExpr 500 exprEncoding.unary
        (unionExpr 501 exprEncoding
          (pairExpr
            (pairExpr 500 501)
            (pairExpr 500
              (callExpr 503 incrVarsExpr 501))))
    
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
      unaryExpr,
      quantifierExpr,
    ]
    
    def incrVarsExpr.expr: Expr := finUnExpr exprList
    
    /-
      (dlIn, dlOut) where `dlIn` equals `dlOut` except that the
      variables of `dlOut` are incremented by 1.
    -/
    def incrVarsDefEncoding: Nat := 22
    def incrVarsDefEncoding.expr: Expr :=
      unExpr
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
    def shiftDefEncoding: Nat := 23
    def shiftDefEncoding.expr: Expr :=
      unExpr
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
      (dl, expr), where `dl` is (an encoding of) a prefix of
      a definition list of length one, and `expr` is the only its
      expression.
    -/
    def lastExpr.base: Nat := 24
    def lastExpr.base.expr: Expr :=
      unionExpr 500 exprEncoding
        (pairExpr
          (pairExpr 500 zeroExpr)
          500)
    
    /-
      (dl, expr), where `expr` is the last expression of (the
      encoding of) a prefix of a definition list `dl`.
    -/
    def lastExpr: Nat := 25
    def lastExpr.expr: Expr :=
      unExpr
        lastExpr.base
        (unionExpr 500 lastExpr
          (pairExpr
            (pairExpr exprEncoding (zthMember 501 500))
            (fstMember 501 500)))
    
    /-
      (dlIn, dlOut), where `dlOut` contains all but the last
      definition of `dlIn`.
      
      For every list of expressions `dl`,
      
          dl = [ ...upToLast(dl), lastExpr(dl) ] \,.
    -/
    def upToLast: Nat := 26
    def upToLast.expr: Expr :=
      unExpr
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
    def arrayAppend: Nat := 27
    def arrayAppend.expr: Expr :=
      (unExpr
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
    def arrayLength: Nat := 28
    def arrayLength.expr: Expr :=
      unExpr
        (pairExpr zeroExpr zeroExpr)
        (Expr.arbUn 500
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
    def append: Nat := 29
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
      Contains (n, dl), such that dl is a prefix of a definition
      list consisting of the zeroth n definition list prefixes
      joined together. (Deflist prefixes are ordered by
      `defEncodingLt`.)
      
      Equivalently,
      
          enumUpTo(0)   = []
          enumUpTo(n+1) = [ ...enumUpTo[n], nthDefList[n] ] \,.
      
      For any two deflists returned by `enumUpTo`, one is a prefix
      of the other. Every prefix of every definition list is
      contained in some deflist prefix returned by `enumUpTo`.
    -/
    def enumUpTo: Nat := 30
    def enumUpTo.expr: Expr :=
      unExpr
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nat
          (pairExpr
            (succExpr 500)
            (callExpr 501
              (callExpr 502 append
                (callExpr 503 enumUpTo 500))
              (callExpr 502 nthDefList 500))))
    
    /-
      Contains (dl, (n, e)) such that `e` is the nth expression
      of the definition list encoding `dl`.
    -/
    def defListToSet: Nat := 31
    def defListToSet.expr: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 defEncoding
          (unExpr
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
      Contains all definition list prefixes of enumUpTo.
      
      Recall that for every two elements of enumUpTo, one is
      a prefix of the other. This guarantees that for any two
      definition list prefixes of `theDlPrefixes` (of sufficient
      length), and any n, their nth expressions are the same.
      
      This in turn means that `theDlPrefixes` represents a unique
      definition list. It also contains all definitions up to
      structural equivalence. Every definable triset is therefore
      defined in this definition list. We'll call it the internal
      definition list.
    -/
    def theDlPrefixes: Nat := 32
    def theDlPrefixes.expr: Expr :=
      unionExpr 500 nat
        (callExpr 501 enumUpTo 500)
    
    /-
      Contains (n, expr) where `expr` is the `n`th expression in
      any `dl` in `theDlPrefixes`.
      
      This is a different representation of the definition list
      represented by `theDlPrefixes`. While `theDlPrefixes` contains
      its prefixes, `theDefList` contains its index-expression
      pairs.
    -/
    def theDefList: Nat := 33
    def theDefList.expr: Expr :=
      unionExpr 500 theDlPrefixes
        (callExpr 501 defListToSet 500)
    
    /-
      Contains ([(n, p), ...], (n, p)) for natural `n`.
    -/
    def getBound.baseExpr: Expr :=
      unionExpr 500 nat
        (Expr.arbUn 501
          (pairExpr
            (pairExpr (pairExpr 500 501) anyExpr)
            (pairExpr 500 501)))
    
    /-
      Contains (arr, (n, p)) such that `arr` is a list containing
      (n, p).
    -/
    def getBound: Nat := 34
    def getBound.expr: Expr :=
      unExpr
        getBound.baseExpr
        (Expr.arbUn 500
          (Expr.arbUn 501
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
    def interpretation: Nat := 35
    
    /-
      A set of pairs (n, p) where `n` is a natural number, and
      `p` is a member of the interpretation of the `n`th definition
      of the definition list represented by `theDefList`.
      
      The pair is contained strongly iff `p` is a definitive member
      of the interpretation, else it is contained weakly.
      
      For every definable triset of pairs `tDef`, there exists
      (an encoding of) a natural number `n` such that for every
      pair `p`,
      
          p ∈ tDef ↔ (n, p) ∈ theSet \,,
      
      where the above equivalence holds for both the definitive
      and possible membership.
      
      As we'll prove in the next chapters, this triset is an
      encoding of the well-founded model of the definition list
      represented by `theDefList`.
    -/
    def theSet: Nat := 36
    
    def interpretation.exprVarBoundOrFree: Expr :=
      -- Assuming 500 is a var, and 501 is bound vars.
      unExpr
        -- The case where 500 is a bound var.
        (callExpr 502 (callExpr 503 getBound 501) 500)
        -- The case where 500 is a free var.
        (irExpr
          -- Ensure that 500 is not a bound var.
          (negCondExpr
            (callExpr 502 (callExpr 503 getBound 501) 500))
          (callExpr 502 theSet 500))
    
    def interpretation.exprVar: Expr :=
      unionExpr 500 nat
        (Expr.arbUn 501
          (pairExpr
            501
            (pairExpr
              (pairExpr zeroExpr 500)
              exprVarBoundOrFree)))
    
    def interpretation.exprZero: Expr :=
      Expr.arbUn 501
        (pairExpr
          501
          (pairExpr
            (pairExpr (natExpr 1) zeroExpr)
            zeroExpr))
    
    def interpretation.exprPair: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.arbUn 502
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
          (Expr.arbUn 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 3) (pairExpr 500 501))
                (unExpr
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprIntersection: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 exprEncoding
          (Expr.arbUn 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 4) (pairExpr 500 501))
                (irExpr
                  (callExpr 503 (callExpr 504 interpretation 502) 500)
                  (callExpr 503 (callExpr 504 interpretation 502) 501))))))
    
    def interpretation.exprCpl: Expr :=
      unionExpr 500 exprEncoding
        (Expr.arbUn 502
          (pairExpr
            502
            (pairExpr
              (pairExpr (natExpr 5) 500)
              (Expr.cpl
                (callExpr 503 (callExpr 504 interpretation 502) 500)))))
    
    def interpretation.exprCondSome: Expr :=
      unionExpr 500 exprEncoding
        (Expr.arbUn 502
          (pairExpr
            502
            (pairExpr
              (pairExpr (natExpr 6) 500)
              (condSomeExpr
                (callExpr 503 (callExpr 504 interpretation 502) 500)))))
    
    def interpretation.exprCondFull: Expr :=
      unionExpr 500 exprEncoding
        (Expr.arbUn 502
          (pairExpr
            502
            (pairExpr
              (pairExpr (natExpr 7) 500)
              (condFullExpr
                (callExpr 503 (callExpr 504 interpretation 502) 500)))))
    
    def interpretation.exprArbUnion: Expr :=
      unionExpr 500 nat
        (unionExpr 501 exprEncoding
          (Expr.arbUn 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 8) (pairExpr 500 501))
                (Expr.arbUn 503
                  (callExpr 504
                    (callExpr 505
                      interpretation
                      (pairExpr (pairExpr 500 503) 502))
                    501))))))
    
    def interpretation.exprArbIntersection: Expr :=
      unionExpr 500 nat
        (unionExpr 501 exprEncoding
          (Expr.arbUn 502
            (pairExpr
              502
              (pairExpr
                (pairExpr (natExpr 9) (pairExpr 500 501))
                (Expr.arbIr 503
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
      exprCondSome,
      exprCondFull,
      exprArbUnion,
      exprArbIntersection,
    ]
    
    def interpretation.expr: Expr := finUnExpr exprList
    
    def theSet.expr: Expr :=
      unionExpr 500 nat
        (pairExpr 500
          (callExpr 501
            (callExpr 502 interpretation zeroExpr)
            (callExpr 502 theDefList 500)))
    
    -- The definitions of the definition list.
    def defList.getDef: Nat → Expr
    | 0 => nat.expr
    | 1 => natPairAA.expr
    | 2 => natLe.expr
    | 3 => exprEncoding.var.expr
    | 4 => exprEncoding.zero.expr
    | 5 => exprEncoding.binary.expr
    | 6 => exprEncoding.unary.expr
    | 7 => exprEncoding.quantifier.expr
    | 8 => exprEncoding.expr
    | 9 => defEncoding.expr
    | 10 => pairDictLt.expr
    | 11 => natLeFn.expr
    | 12 => pairOfDepth.expr
    | 13 => natLt.expr
    | 14 => sameDepth.expr
    | 15 => pairLt.expr
    | 16 => defEncodingLt.expr
    | 17 => defEncodingMinDist2.expr
    | 18 => nextDef.expr
    | 19 => nthDefList.expr
    | 20 => incrVarsExpr.var.expr
    | 21 => incrVarsExpr.expr
    | 22 => incrVarsDefEncoding.expr
    | 23 => shiftDefEncoding.expr
    | 24 => lastExpr.base.expr
    | 25 => lastExpr.expr
    | 26 => upToLast.expr
    | 27 => arrayAppend.expr
    | 28 => arrayLength.expr
    | 29 => append.expr
    | 30 => enumUpTo.expr
    | 31 => defListToSet.expr
    | 32 => theDlPrefixes.expr
    | 33 => theDefList.expr
    | 34 => getBound.expr
    | 35 => interpretation.expr
    | 36 => theSet.expr
    | _rest => zeroExpr
    
    /-
      All free variables of the definition list are less than 38.
      From this, it follows that the definition list is finitely
      bounded.
    -/
    def defList.usedVarsLt38
      (usedVar: IsFreeVar (getDef a) (fun x => x ∈ []))
    :
      usedVar.val < 38
    :=
      let prf
        (i: Nat)
        (eq: (freeVarsLt (getDef i) [] 38).toBool = true)
        (usedVar: IsFreeVar (getDef i) (fun x => x ∈ []))
      :
        usedVar.val < 38
      :=
        match h: freeVarsLt (getDef i) [] 38 with
        | .isTrue isLe => isLe usedVar
        | .none => Bool.noConfusion (h ▸ eq)
      
      match a with
      | 00 => prf 00 rfl usedVar
      | 01 => prf 01 rfl usedVar
      | 02 => prf 02 rfl usedVar
      | 03 => prf 03 rfl usedVar
      | 04 => prf 04 rfl usedVar
      | 05 => prf 05 rfl usedVar
      | 06 => prf 06 rfl usedVar
      | 07 => prf 07 rfl usedVar
      | 08 => prf 08 rfl usedVar
      | 09 => prf 09 rfl usedVar
      | 10 => prf 10 rfl usedVar
      | 11 => prf 11 rfl usedVar
      | 12 => prf 12 rfl usedVar
      | 13 => prf 13 rfl usedVar
      | 14 => prf 14 rfl usedVar
      | 15 => prf 15 rfl usedVar
      | 16 => prf 16 rfl usedVar
      | 17 => prf 17 rfl usedVar
      | 18 => prf 18 rfl usedVar
      | 19 => prf 19 rfl usedVar
      | 20 => prf 20 rfl usedVar
      | 21 => prf 21 rfl usedVar
      | 22 => prf 22 rfl usedVar
      | 23 => prf 23 rfl usedVar
      | 24 => prf 24 rfl usedVar
      | 25 => prf 25 rfl usedVar
      | 26 => prf 26 rfl usedVar
      | 27 => prf 27 rfl usedVar
      | 28 => prf 28 rfl usedVar
      | 29 => prf 29 rfl usedVar
      | 30 => prf 30 rfl usedVar
      | 31 => prf 31 rfl usedVar
      | 32 => prf 32 rfl usedVar
      | 33 => prf 33 rfl usedVar
      | 34 => prf 34 rfl usedVar
      | 35 => prf 35 rfl usedVar
      | 36 => prf 36 rfl usedVar
    
    def defList.hasFiniteBounds
      (dependsOn: DefList.DependsOn getDef a b)
    :
      b < 38
    :=
      let eq := list_mem_empty_eq_set_empty
      -- Structural recursion was unsupported as of writing, see
      -- commit history.
      dependsOn.rec
        (fun aUsesB => usedVarsLt38 ⟨_, eq ▸ aUsesB⟩)
        (fun _ _ => id)
    
    /-
      The definition list that defines the universal triset (under
      the name `theSet`.)
      
      It is called the *external* definition list to disambiguate
      it from the *internal* definition list that is represented
      by the definition `theDefList`.
    -/
    def theExternalDefList:
      FinBoundedDL pairSignature
    := {
      getDef := defList.getDef
      
      isFinBounded :=
        fun _ => ⟨38, defList.hasFiniteBounds⟩
    }
    
    -- The well-founded model of the external definition list.
    noncomputable def theExternalWfm :=
      theExternalDefList.wellFoundedModel pairSalgebra
    
    def decodeValuation
      (s3: Set3 Pair)
    :
      Valuation Pair
    :=
      fun n => Set3.pairCallJust s3 (fromNat n)
    
    def internalOfExternal
      (v: Valuation Pair)
    :
      Valuation Pair
    :=
      decodeValuation (v theSet)
    
    /-
      An encoding of the well-founded model of the internal
      definition list. The internal definition list itself
      is defined in Chapter 8, section 13.
      
      That this encoding actually encodes the well-founded
      model is proven in Chapter 9.
    -/
    def theInternalWfmEncoding: Valuation Pair :=
      internalOfExternal theExternalWfm
    
  end uniDefList  
end Pair
