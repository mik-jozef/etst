import ExampleWFCs

/-
  In this file, we define the triset of all definable
  trisets of pairs, in the sense that for any definable
  triset tDef, there exists a triset tIndex such that
  
    setOfAllDef & (tIndex, Any) = { tDef }  .
  
  We show that this triset is itself definable.
-/

namespace Pair
  open pairSignature
  
  -- Convention: bound variables start at 500.
  
  def Expr := _root_.Expr pairSignature
  
  instance (n: Nat): OfNat Expr n where
    ofNat := Expr.var n
  
  instance coe: Coe Nat Expr where
    coe := fun n => Expr.var n
  
  
  def zeroExpr: Expr :=
    Expr.op Op.zero ArityZero.elim
  
  def pairExpr (left rite: Expr): Expr :=
    Expr.op
      Op.pair
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def anyExpr: Expr := Expr.Un 0 0
  def noneExpr: Expr := Expr.Ir 0 0
  
  -- Make sure n is not a free var in the domain expr.
  def unionExpr (n: Nat) (domain body: Expr): Expr :=
    Expr.Un n (Expr.ifThen (Expr.ir n domain) body)
  
  -- Make sure n is not a free var in the domain expr.
  -- `All t: T, b` === `All t, b | (!(t & domain) then any)`.
  def irsecExpr (n: Nat) (domain body: Expr): Expr :=
    Expr.Ir
      n
      (Expr.un
        body
        (Expr.ifThen (Expr.cpl (Expr.ir n domain)) (anyExpr)))
  
  -- Make sure n is not a free var in the expr.
  def zthMember (n: Nat) (expr: Expr): Expr :=
    Expr.Un n (Expr.ifThen (Expr.ir (pairExpr n anyExpr) expr) n)
  
  -- Make sure n is not a free var in the expr.
  def fstMember (n: Nat) (expr: Expr): Expr :=
    Expr.Un n (Expr.ifThen (Expr.ir (pairExpr anyExpr n) expr) n)
  
  -- Make sure n is not a free var in the expr.
  def callExpr (n: Nat) (fn arg: Expr): Expr :=
    fstMember n (Expr.ir fn (pairExpr arg anyExpr))
  
  def succExpr (expr: Expr): Expr := pairExpr expr zeroExpr
  
  def finUnExpr: List Expr → Expr
  | List.nil => noneExpr
  | List.cons expr List.nil => expr
  | List.cons expr0 (List.cons expr1 rest) =>
      Expr.un expr0 (finUnExpr (expr1::rest))
  
  
  def succ (pair: Pair): Pair := Pair.pair pair Pair.zero
  
  def fromNat: Nat → Pair
  | Nat.zero => Pair.zero
  | Nat.succ n => succ (fromNat n)
  
  instance ofNat n: OfNat Pair n where
    ofNat := fromNat n
  
  def natExpr: Nat → Expr
  | Nat.zero => zeroExpr
  | Nat.succ pred => succExpr (natExpr pred)
  
  
  namespace setOfAllDef
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
        (unionExpr 500 natPairAA
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
        (natExpr 1)
        (Expr.un
          (natExpr 2)
          ((Expr.un (natExpr 3) (natExpr 5))))
    
    /-
      Contains the triset { 7, 8 }.
    -/
    def exprEncoding.quantifier: Nat := 5
    def exprEncoding.quantifier.expr: Expr :=
      Expr.un (natExpr 7) (natExpr 8)
    
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
    def exprEncoding: Nat := 6
    def exprEncoding.expr: Expr :=
      finUnExpr [
        exprEncoding.var,
        exprEncoding.zero,
        pairExpr
          exprEncoding.binary
          (pairExpr exprEncoding exprEncoding),
        pairExpr (natExpr 5) exprEncoding,
        pairExpr
          exprEncoding.quantifier
          (pairExpr nat exprEncoding),
      ]
    
    /-
      Contains all pairs that encode a finite prefix of
      a definition list
    -/
    def defEncoding: Nat := 7
    def defEncoding.expr: Expr :=
      Expr.un zeroExpr (pairExpr exprEncoding defEncoding)
    
    /-
      Contains (a, b) with a and b being pairs such that a < b
      in the dictionary order. Base case: () < (a, b).
    -/
    def pairDictLt: Nat := 8
    def pairDictLt.expr: Expr :=
      finUnExpr [
        pairExpr zeroExpr (pairExpr anyExpr anyExpr),
        unionExpr 500 pairDictLt
          (pairExpr
            (pairExpr (zthMember 501 500) anyExpr)
            (pairExpr (fstMember 501 500) anyExpr)),
        unionExpr 500 pairDictLt
          (pairExpr
            (pairExpr 501 (zthMember 501 500))
            (pairExpr 501 (fstMember 501 500))),
      ]
    
    /-
      Contains (n, m) such that m ≤ n.
    -/
    def natLeFn: Nat := 9
    def natLeFn.expr: Expr :=
      unionExpr 500 natLe
        (pairExpr (fstMember 501 500) (zthMember 501 500))
    
    /-
      Contains (n, p) such that p is a pair and n its
      depth.
    -/
    def pairOfDepth: Nat := 10
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
    def natLt: Nat := 11
    def natLt.expr: Expr :=
      Expr.ir natLe (Expr.un 500 (Expr.cpl (pairExpr 500 500)))
    
    /-
      Contains (a, b) if a and b have the same depth.
    -/
    def sameDepth: Nat := 12
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
    def pairLt: Nat := 13
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
    def defEncodingLt: Nat := 14
    def defEncodingLt.expr: Expr :=
      Expr.ir pairLt defEncoding
    
    /-
      Contains (a, b) iff a < x < b for some deflist
      encoding x.
    -/
    def defEncodinMinDist2: Nat := 15
    def defEncodinMinDist2.expr: Expr :=
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
    def nextDef: Nat := 16
    def nextDef.expr: Expr :=
      Expr.ir
        defEncodingLt
        (Expr.cpl defEncodinMinDist2)
    
    /-
      Contains (n, dl), where dl is the nth least
      deflist in the `defEncodingLt` order.
    -/
    def nthDefList: Nat := 17
    def nthDefList.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 500 nthDefList
          (pairExpr
            (succExpr (zthMember 501 500))
            (callExpr 501 nextDef (fstMember 502 500))))
    
    -- See shiftExprEncoding.
    def shiftExprEncoding.var: Nat := 18
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
    def shiftExprEncoding: Nat := 19
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
    def shiftDefEncoding.incrementExprs: Nat := 20
    def shiftDefEncoding.incrementExprs.expr: Expr :=
      Expr.un
        (pairExpr zeroExpr zeroExpr)
        (unionExpr 501 exprEncoding
          (pairExpr
            (pairExpr 501 500)
            (pairExpr
              (callExpr 502 shiftExprEncoding 501)
              (callExpr 502 shiftDefEncoding.incrementExprs 500))))
    
    /-
      (expr, (dlIn, dlOut)) where dlOut = [ expr, ...shift(dlIn) ]
      and the shift function increments every variable
      in every expression of dlIn, so that the semantics
      of the definitions is preserved.
    -/
    def shiftDefEncoding: Nat := 21
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
    def lastExpr.base: Nat := 22
    def lastExpr.base.expr: Expr :=
      unionExpr 500 exprEncoding
        (pairExpr
          (pairExpr 500 zeroExpr)
          500)
    
    /-
      (dl, expr), where expr is the last expression
      of the definition list dl
    -/
    def lastExpr: Nat := 23
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
    def upToLast: Nat := 24
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
    def append.base: Nat := 25
    def append.base.expr: Expr :=
      pairExpr
        zeroExpr
        (unionExpr 500 defEncoding
          (pairExpr 500 500))
    
    /-
      (dlA, (dlB, dlRes)), where dlRes = [ ...dlA, ...dlB ]
    -/
    def append: Nat := 26
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
    def enumUpTo: Nat := 27
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
    def defListToSet: Nat := 28
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
    def theDlPrefixes: Nat := 29
    def theDlPrefixes.expr: Expr :=
      unionExpr 500 nat
        (callExpr 501 enumUpTo 500)
    
    /-
      Contains (n, expr) where expr is the nth expression
      in any dl from `enumUpTo` whose length is greater
      than n.
      
      Defines definitions of all definable trisets.
    -/
    def theDefList: Nat := 30
    def theDefList.expr: Expr :=
      unionExpr 500 theDlPrefixes
        (callExpr 501 defListToSet 500)
    
    /-
      ([(n, p), ...], (n, p)).
    -/
    def getBound.base: Nat := 31
    def getBound.base.expr: Expr :=
      unionExpr 500 nat
        (Expr.Un 501
          (pairExpr
            (pairExpr (pairExpr 500 501) anyExpr)
            (pairExpr 500 501)))
    
    /-
      ((n, p)[], (n_i, p_i)) + some garbage.
    -/
    def getBound: Nat := 32
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
    def interpretation: Nat := 33
    /-
      The set of pairs (n, s) such that n is a natural number,
      and for every definable triset of pairs dtp, there exists
      a natural number n such that `theSet & (n, Any) = dtp`
    -/
    def theSet: Nat := 34
    
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
    | 8 => pairDictLt.expr
    | 9 => natLeFn.expr
    | 10 => pairOfDepth.expr
    | 11 => natLt.expr
    | 12 => sameDepth.expr
    | 13 => pairLt.expr
    | 14 => defEncodingLt.expr
    | 15 => defEncodinMinDist2.expr
    | 16 => nextDef.expr
    | 17 => nthDefList.expr
    | 18 => shiftExprEncoding.var.expr
    | 19 => shiftExprEncoding.expr
    | 20 => shiftDefEncoding.incrementExprs.expr
    | 21 => shiftDefEncoding.expr
    | 22 => lastExpr.base.expr
    | 23 => lastExpr.expr
    | 24 => upToLast.expr
    | 25 => append.base.expr
    | 26 => append.expr
    | 27 => enumUpTo.expr
    | 28 => defListToSet.expr
    | 29 => theDlPrefixes.expr
    | 30 => theDefList.expr
    | 31 => getBound.base.expr
    | 32 => getBound.expr
    | 33 => interpretation.expr
    | 34 => theSet.expr
    | rest + 35 =>
        callExpr (rest + 36) theSet (natExpr rest)
    
    #reduce Expr.IsFreeVar (defList.getDef 0) Set.empty
    
    def defList:
      DefList pairSignature
    := {
      getDef := defList.getDef
      
      isFinBounded := ⟨{
        bounds := fun _ x => x ≤ 34,
        usedNamesInBounds :=
          fun x xUsed =>
            match x with
            | 0 =>
              sorry
            | rest => sorry
        ,
        
        boundsFinite := sorry,
        boundsTransitive := sorry,
      }, trivial⟩
    }
  end setOfAllDef
end Pair
