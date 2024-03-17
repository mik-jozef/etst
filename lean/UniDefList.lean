import ExampleWFCs
import PairFreeVars
import LeN35
import Operators
import Wfm

/-
  In this file, we define the triset of all definable
  trisets of pairs, in the sense that for any definable
  triset tDef, there exists a triset tIndex such that
  
    setOfAllDef & (tIndex, Any) = { tDef }  .
  
  We show that this triset is itself definable.
-/

def Nat.setLeN.isFinite (n: Nat):
  Set.IsFinite (fun x => x ≤ n)
:=
  match n with
  | zero => ⟨
      [ 0 ],
      fun m =>
        let eqZero := Nat.le_zero.mp m.property
        eqZero ▸ List.Mem.head []
    ⟩
  | succ pred =>
      let isFinPred := isFinite pred
      let listPred := isFinPred.unwrap
      
      ⟨
        succ pred :: listPred,
        fun m =>
          let leOrEq := Nat.le_or_eq_of_le_succ m.property
          leOrEq.elim
            (fun le =>
              let mInList := listPred.property ⟨m, le⟩
              List.Mem.tail (succ pred) mInList)
            (fun eq =>
              by rewrite [eq]; exact List.Mem.head listPred.val),
      ⟩

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
      natLe = natPairAA | Ex (a, b): natPairAA, (a, succ b)
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
      Contains all pairs that encode a finite prefix of
      a definition list
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
      Contains (n, m) such that m ≤ n.
    -/
    def natLeFn: Nat := 10
    def natLeFn.expr: Expr :=
      unionExpr 500 natLe
        (pairExpr (fstMember 501 500) (zthMember 501 500))
    
    /-
      Contains (n, p) such that p is a pair and n its
      depth.
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
      The "less than" relation on natural numbers
    -/
    def natLt: Nat := 12
    def natLt.expr: Expr :=
      Expr.ir natLe (Expr.cpl (Expr.Un 500 (pairExpr 500 500)))
    
    /-
      Contains (a, b) if a and b have the same depth.
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
      Contains (a, b) iff a < x < b for some deflist
      encoding x.
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
      Contains (a, b) where b is the least defEncoding
      greater than a.
    -/
    def nextDef: Nat := 17
    def nextDef.expr: Expr :=
      Expr.ir
        defEncodingLt
        (Expr.cpl defEncodingMinDist2)
    
    /-
      Contains (n, dl), where dl is the nth least
      deflist in the `defEncodingLt` order.
    -/
    def nthDefList: Nat := 18
    def nthDefList.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nthDefList
          (pairExpr
            (succExpr (zthMember 501 500))
            (callExpr 501 nextDef (fstMember 502 500))))
    
    -- See shiftExprEncoding.
    def shiftExprEncoding.var: Nat := 19
    def shiftExprEncoding.var.expr: Expr :=
      unionExpr 500 nat
        (pairExpr
          (pairExpr zeroExpr 500)
          (pairExpr zeroExpr (succExpr 500)))
    
    /-
      Contains (eIn, eOut) such that eIn is an encoding
      of an expression and eOut is eIn with variables
      incremented by 1.
    -/
    def shiftExprEncoding: Nat := 20
    def shiftExprEncoding.expr: Expr :=
      finUnExpr [
        shiftExprEncoding.var,
        
        pairExpr exprEncoding.zero exprEncoding.zero,
        
        unionExpr 501 exprEncoding
          (unionExpr 502 exprEncoding
            (pairExpr
              (pairExpr
                exprEncoding.binary
                (pairExpr 501 502))
              (pairExpr
                exprEncoding.binary
                (pairExpr
                  (callExpr 503 shiftExprEncoding 501)
                  (callExpr 503 shiftExprEncoding 502))))),
        
        unionExpr 501 exprEncoding
          (pairExpr
            (pairExpr (natExpr 5) 501)
            (pairExpr (natExpr 5)
              (callExpr 503 shiftExprEncoding 501))),
        
        unionExpr 501 exprEncoding
          (unionExpr 502 nat
            (pairExpr
              (pairExpr
                exprEncoding.quantifier
                (pairExpr 502 501))
              (pairExpr
                exprEncoding.quantifier
                (pairExpr
                  502
                  (callExpr 503 shiftExprEncoding 501))))),
      ]
    
    /-
      (dlIn, dlOut) where dlIn equals dlOut except that
      the variables of dlOut are incremented by 1.
    -/
    def shiftDefEncoding.incrementExprs: Nat := 21
    def shiftDefEncoding.incrementExprs.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 exprEncoding
          (unionExpr 501 defEncoding
            (pairExpr
              (pairExpr 500 501)
              (pairExpr
                (callExpr 502 shiftExprEncoding 500)
                (callExpr 502 shiftDefEncoding.incrementExprs 501)))))
    
    /-
      (expr, (dlIn, dlOut)) where dlOut = [ expr, ...shift(dlIn) ]
      and the shift function increments every variable
      in every expression of dlIn, so that the semantics
      of the definitions is preserved.
    -/
    def shiftDefEncoding: Nat := 22
    def shiftDefEncoding.expr: Expr :=
      unionExpr 500 exprEncoding
        (unionExpr 501 defEncoding
          (pairExpr
            500
            (pairExpr
              501
              (pairExpr
                500
                (callExpr 502
                  shiftDefEncoding.incrementExprs
                  501)))))
    
    /-
      (dl, expr), where dl is a definition list of length
      one and expr is the only its expression.
    -/
    def lastExpr.base: Nat := 23
    def lastExpr.base.expr: Expr :=
      unionExpr 500 exprEncoding
        (pairExpr
          (pairExpr 500 zeroExpr)
          500)
    
    /-
      (dl, expr), where expr is the last expression
      of the definition list dl
    -/
    def lastExpr: Nat := 24
    def lastExpr.expr: Expr :=
      Expr.un
        lastExpr.base
        (unionExpr 500 lastExpr
          (pairExpr
            (pairExpr exprEncoding (zthMember 501 500))
            (fstMember 501 lastExpr)))
    
    /-
      (dlIn, dlOut), where dlOut contains all but the
      last definition.
    -/
    def upToLast: Nat := 25
    def upToLast.expr: Expr :=
      Expr.un
        (pairExpr exprEncoding zeroExpr)
        (unionExpr 500 upToLast
          (unionExpr 501 exprEncoding
            (pairExpr
              (pairExpr 501 500)
              (pairExpr 501 500))))
    
    /-
      ([], (dl, dl)) for dl ∈ defEncoding
    -/
    def append.base: Nat := 26
    def append.base.expr: Expr :=
      pairExpr
        zeroExpr
        (unionExpr 500 defEncoding
          (pairExpr 500 500))
    
    /-
      (dlA, (dlB, dlRes)), where dlRes = [ ...dlA, ...dlB ]
    -/
    def append: Nat := 27
    def append.expr: Expr :=
      Expr.un
        append.base
        (unionExpr 500 defEncoding
          (unionExpr 501 defEncoding
            (callExpr 502
              (callExpr 503 append (callExpr 504 upToLast 500))
              (callExpr 503
                (callExpr 504 shiftDefEncoding (callExpr 504 lastExpr 500))
                501))))
    
    /-
      Contains (n, dl), such that dl is a (finite prefix
      of a) definition list consisting of the zeroth
      n definition list prefixes joined together.
      
      (Deflist prefixes are ordered by `defEncodingLt`.)
      
      For any two deflists returned by `enumUpTo`,
      one is a prefix of the other.
      Every finite prefix of any definition list is
      in some deflist prefix returned by `enumUpTo`.
    -/
    def enumUpTo: Nat := 28
    def enumUpTo.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nat
          (pairExpr
            500
            (callExpr 501
              (callExpr 502 append
                (callExpr 503 enumUpTo (zthMember 504 500)))
              (callExpr 502 nthDefList (zthMember 504 500)))))
    
    /-
      Contains (dl, (n, e)) such that e is the nth
      expression of dl ∈ defEncoding.
    -/
    def defListToSet: Nat := 29
    def defListToSet.expr: Expr :=
      unionExpr 500 exprEncoding
        (Expr.un
          (pairExpr
            (pairExpr 500 zeroExpr) -- A length-one deflist.
            (pairExpr zeroExpr 500))
          (unionExpr 501 defEncoding
            (unionExpr 502 nat
              (pairExpr
                (pairExpr 500 501)
                (pairExpr
                  (succExpr 502)
                  (callExpr 503 (callExpr 504 defListToSet 501) 502))))))
    
    /-
      Contains all deflists of enumUpTo.
    -/
    def theDlPrefixes: Nat := 30
    def theDlPrefixes.expr: Expr :=
      unionExpr 500 nat
        (callExpr 501 enumUpTo 500)
    
    /-
      Contains (n, expr) where expr is the nth expression
      in any dl from `enumUpTo` whose length is greater
      than n.
      
      Defines definitions of all definable trisets.
    -/
    def theDefList: Nat := 31
    def theDefList.expr: Expr :=
      unionExpr 500 theDlPrefixes
        (callExpr 501 defListToSet 500)
    
    /-
      ([(n, p), ...], (n, p)).
    -/
    def getBound.base: Nat := 32
    def getBound.base.expr: Expr :=
      unionExpr 500 nat
        (Expr.Un 501
          (pairExpr
            (pairExpr (pairExpr 500 501) anyExpr)
            (pairExpr 500 501)))
    
    /-
      ((n, p)[], (n_i, p_i)) + some garbage.
    -/
    def getBound: Nat := 33
    def getBound.expr: Expr :=
      Expr.un
        getBound.base
        (unionExpr 500 nat
          (Expr.Un 501
            (pairExpr
              (pairExpr (pairExpr (Expr.cpl 500) anyExpr) 501)
              (callExpr 502 getBound 501))))
    
    /-
      (Hopefully, to be proven: )
      Contains (expr, bound, s) where expr is an expression,
      bound is an array of var-pair pairs (bound vars),
      and s is the interpretation of the nth definition
      in `theDefList`.
    -/
    def interpretation: Nat := 34
    /-
      The set of pairs (n, s) such that n is a natural number,
      and for every definable triset of pairs dtp, there exists
      a natural number n such that `theSet & (n, Any) = dtp`
    -/
    def theSet: Nat := 35
    
    def interpretation.expr: Expr :=
      /-
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
      finUnExpr [
        -- var
        unionExpr 500 nat
          (Expr.Un 501
            (pairExpr
              (pairExpr zeroExpr 500)
              (pairExpr
                501
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
                    (callExpr 502 theSet 500)))))),
        
        -- op zero
        pairExpr
          (pairExpr (natExpr 1) zeroExpr)
          (pairExpr anyExpr zeroExpr),
        
        -- op pair
        unionExpr 500 exprEncoding
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 2) (pairExpr 500 501))
                (pairExpr
                  502
                  (pairExpr
                    (callExpr 503 (callExpr 504 interpretation 500) 502)
                    (callExpr 503 (callExpr 504 interpretation 501) 502)))))),
        
        -- union
        unionExpr 500 exprEncoding
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 3) (pairExpr 500 501))
                (pairExpr
                  502
                  (Expr.un
                    (callExpr 503 (callExpr 504 interpretation 500) 502)
                    (callExpr 503 (callExpr 504 interpretation 501) 502)))))),
        
        -- intersection
        unionExpr 500 exprEncoding
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 4) (pairExpr 500 501))
                (pairExpr
                  502
                  (Expr.ir
                    (callExpr 503 (callExpr 504 interpretation 500) 502)
                    (callExpr 503 (callExpr 504 interpretation 501) 502)))))),
        
        -- complement
        unionExpr 500 exprEncoding
          (Expr.Un 502
            (pairExpr
              (pairExpr (natExpr 5) 500)
              (pairExpr
                502
                (Expr.cpl
                  (callExpr 503 (callExpr 504 interpretation 500) 502))))),
        
        -- ifThen
        unionExpr 500 exprEncoding
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 6) (pairExpr 500 501))
                (pairExpr
                  502
                  (Expr.ifThen
                    (callExpr 503 (callExpr 504 interpretation 500) 502)
                    (callExpr 503 (callExpr 504 interpretation 501) 502)))))),
        
        -- arbitrary union
        unionExpr 500 nat
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 4) (pairExpr 500 501))
                (pairExpr
                  502
                  (Expr.Un 503
                    (callExpr 503
                      (callExpr 504 interpretation 501)
                      (pairExpr (pairExpr 500 503) 502))))))),
        
        -- arbitrary intersection
        unionExpr 500 nat
          (unionExpr 501 exprEncoding
            (Expr.Un 502
              (pairExpr
                (pairExpr (natExpr 4) (pairExpr 500 501))
                (pairExpr
                  502
                  (Expr.Ir 503
                    (callExpr 503
                      (callExpr 504 interpretation 501)
                      (pairExpr (pairExpr 500 503) 502))))))),
      ]
    
    def theSet.expr: Expr :=
      unionExpr 500 nat
        (callExpr 501
          (callExpr 502 interpretation
            (callExpr 503 theDefList 500))
          zeroExpr)
    
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
    | 19 => shiftExprEncoding.var.expr
    | 20 => shiftExprEncoding.expr
    | 21 => shiftDefEncoding.incrementExprs.expr
    | 22 => shiftDefEncoding.expr
    | 23 => lastExpr.base.expr
    | 24 => lastExpr.expr
    | 25 => upToLast.expr
    | 26 => append.base.expr
    | 27 => append.expr
    | 28 => enumUpTo.expr
    | 29 => defListToSet.expr
    | 30 => theDlPrefixes.expr
    | 31 => theDefList.expr
    | 32 => getBound.base.expr
    | 33 => getBound.expr
    | 34 => interpretation.expr
    | 35 => theSet.expr
    | _rest + 36 =>
      -- This would be nice, but proving `usedNamesInBounds`
      -- below proved to be a pain.
      -- callExpr (rest + 37) theSet (natExpr rest)
      35
    
    def defList:
      DefList pairSignature
    := {
      getDef := defList.getDef
      
      isFinBounded := ⟨{
        bounds := fun _ x => x ≤ 35,
        usedNamesInBounds :=
          fun x usedByX =>
            let prf
              (defIndex: Nat)
              (fv: List Nat)
              (fvEq: (freeVars (defList.getDef defIndex)).val = fv)
              (allLe: ∀ {x} (_: x ∈ fv), x ≤ 35)
              (usedByX:
                (Expr.IsFreeVar (defList.getDef defIndex) Set.empty))
            :
              usedByX.val ≤ 35
            :=
              let freeVars := freeVars (defList.getDef defIndex)
              let xIn: ↑usedByX ∈ fv := fvEq ▸ freeVars.property usedByX
              allLe xIn
            
            -- Here we are proving that each definition only
            -- uses finitely many other definitions by enumerating
            -- all used definitions of all definitions.
            match x with
            | 0 => prf 0 [ 0 ] rfl (by simp) usedByX
            | 1 => prf 1 [ 0 ] rfl (by simp) usedByX
            | 2 => prf 2 [ 1, 2 ] rfl (by simp[leN35]) usedByX
            | 3 => prf 3 [ 0 ] rfl (by simp) usedByX
            | 4 => prf 4 [] rfl (by simp) usedByX
            | 5 => prf 5 [] rfl (by simp) usedByX
            | 6 => prf 6 [] rfl (by simp) usedByX
            | 7 => prf 7 [ 3, 4, 5, 7, 6, 0 ] rfl (by simp[leN35]) usedByX
            | 8 => prf 8 [ 7, 8 ] rfl (by simp[leN35]) usedByX
            | 9 => prf 9 [ 9 ] rfl (by simp[leN35]) usedByX
            | 10 => prf 10 [ 2 ] rfl (by simp[leN35]) usedByX
            | 11 => prf 11 [ 0, 11, 10 ] rfl (by simp[leN35]) usedByX
            | 12 => prf 12 [ 2 ] rfl (by simp[leN35]) usedByX
            | 13 => prf 13 [ 0, 11 ] rfl (by simp[leN35]) usedByX
            | 14 => prf 14 [ 13, 9, 12, 11 ] rfl (by simp[leN35]) usedByX
            | 15 => prf 15 [ 14, 8 ] rfl (by simp[leN35]) usedByX
            | 16 => prf 16 [ 15 ] rfl (by simp[leN35]) usedByX
            | 17 => prf 17 [ 15, 16 ] rfl (by simp[leN35]) usedByX
            | 18 => prf 18 [ 18, 17 ] rfl (by simp[leN35]) usedByX
            | 19 => prf 19 [ 0 ] rfl (by simp[leN35]) usedByX
            | 20 => prf 20 [ 19, 4, 7, 5, 20, 0, 6 ] rfl (by simp[leN35]) usedByX
            | 21 => prf 21 [ 7, 8, 20, 21 ] rfl (by simp[leN35]) usedByX
            | 22 => prf 22 [ 7, 8, 21 ] rfl (by simp[leN35]) usedByX
            | 23 => prf 23 [ 7 ] rfl (by simp[leN35]) usedByX
            | 24 => prf 24 [ 23, 24, 7 ] rfl (by simp[leN35]) usedByX
            | 25 => prf 25 [ 7, 25 ] rfl (by simp[leN35]) usedByX
            | 26 => prf 26 [ 8 ] rfl (by simp[leN35]) usedByX
            | 27 => prf 27 [ 26, 8, 27, 25, 22, 24 ] rfl (by simp[leN35]) usedByX
            | 28 => prf 28 [ 0, 27, 28, 18 ] rfl (by simp[leN35]) usedByX
            | 29 => prf 29 [ 7, 8, 0, 29 ] rfl (by simp[leN35]) usedByX
            | 30 => prf 30 [ 0, 28 ] rfl (by simp[leN35]) usedByX
            | 31 => prf 31 [ 30, 29 ] rfl (by simp[leN35]) usedByX
            | 32 => prf 32 [ 0 ] rfl (by simp[leN35]) usedByX
            | 33 => prf 33 [ 32, 0, 33 ] rfl (by simp[leN35]) usedByX
            | 34 => prf 34 [ 0, 33, 35, 7, 34 ] rfl (by simp[leN35]) usedByX
            | 35 => prf 35 [ 0, 34, 31 ] rfl (by simp[leN35]) usedByX
            | rest + 36 =>
              let expr: Expr := 35
              
              let freeVars := freeVars expr
              let xIn: ↑usedByX ∈ [ 35 ] := freeVars.property usedByX
              let xEq: usedByX.val = 35 := List.eq_of_mem_singleton xIn
              let le35Self: 35 ≤ 35 := by simp
              xEq ▸ le35Self
        ,
        
        boundsFinite := fun _ => Nat.setLeN.isFinite 35,
        boundsTransitive := fun a b c _bLe cLe => cLe,
      }, trivial⟩
    }
    
    noncomputable def wfModel :=
      defList.wellFoundedModel pairSalgebra
    
  end uniDefList  
end Pair
