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
      natPairAA = Un 2: nat, (2, 2)
    -/
    def natPairAA: Nat := 1
    def natPairAA.expr := unionExpr 500 nat (pairExpr 500 500)
    
    /-
      Contains (a, b) iff a and b are naturals st. a ≤ b.
      natLe = natPairAA | Ex 500: natPairAA, (500.zth, 500.fst.succ)
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
      Contains (n, (0, m)) where m ≤ n. See also exprByBound.
      exprByBound.var = Un tmpNm0: natLe, (tmpNm0.fst, (0, tmpNm0.zth))
    -/
    def exprByBound.var: Nat := 3
    def exprByBound.var.expr: Expr :=
      unionExpr
        500
        natLe
        (pairExpr
          (fstMember 501 500)
          (pairExpr zeroExpr (zthMember 501 500)))
    
    /-
      Contains (n, (1, ())). See also exprByBound.
      exprByBound.zero = Un 500: nat, (500, (1, ()))
    -/
    def exprByBound.zero: Nat := 4
    def exprByBound.zero.expr: Expr :=
      unionExpr
        500
        nat
        (pairExpr 500 (pairExpr (natExpr 1) zeroExpr))
    
    /-
      Contains the triset { 1, 2, 3, 5 }.
    -/
    def exprByBound.binary: Nat := 5
    def exprByBound.binary.expr: Expr :=
      Expr.un
        (natExpr 1)
        (Expr.un
          (natExpr 2)
          ((Expr.un (natExpr 3) (natExpr 5))))
    
    /-
      Contains (a, (b, (x, (a, b)))), where x is
      in exprByBound.binary. See also exprByBound.
      exprByBound.pair =
        Un 500 501,
          Un 502: exprByBound.binary,
            (500, (501, (502, (500, 501))))
    -/
    def exprByBound.pair: Nat := 6
    def exprByBound.pair.expr: Expr :=
      Expr.un 500
        (Expr.un 501
          (unionExpr 502 nat
            (unionExpr 503 exprByBound.binary
              (pairExpr
                500
                (pairExpr
                  501
                  (pairExpr
                    502
                    (pairExpr
                      503
                      (pairExpr 500 501))))))))
    
    /-
      Contains (a, (n, (4, a)). See also exprByBound.
      exprByBound.zero = Un 500: nat, (500, (1, ()))
    -/
    def exprByBound.cpl: Nat := sorry
    def exprByBound.cpl.expr: Expr :=
      unionExpr
        500
        nat
        (pairExpr 500 (pairExpr (natExpr 1) zeroExpr))
    
    /-
      Contains (n, e), where n is a natural and e is an
      encoding of an expression of depth at most n that uses
      only variables of at most n.
      
      Expressions are encoded like this:
      | var (v: Nat)                 => (0, v)
      | op (op: zero) (args)         => (1, ())
      | op (op: pair) (args)         => (1, (args 0, args 1))
      | un (left rite: Expr sig)     => (2, (left, rite))
      | ir (left rite: Expr sig)     => (3, (left, rite))
      | cpl (expr: Expr sig)         => (4, expr)
      | ifThen (cond expr: Expr sig) => (5, (cond, expr))
      | Un (x: Nat) (body: Expr sig) => (6, (x, body))
      | Ir (x: Nat) (body: Expr sig) => (7, (x, body))
    -/
    def exprByBound: Nat := 3
    def exprByBound.expr: Expr :=
      Expr.un
        exprByBound.var
        (Expr.un
          exprByBound.zero
          (Expr.un
            (unionExpr 500 natLe -- Un (x, n): natLe,
              (unionExpr 501 (callExpr 503 exprByBound (fstMember 504 500))
                (unionExpr 502 nat
                  (pairExpr
                    500
                    (callExpr
                      501
                      (callExpr 502 exprByBound.pair sorry)
                      sorry)))))
            (Expr.un
              sorry
              (Expr.un
                sorry
                (Expr.un
                  sorry
                  (Expr.un
                    sorry
                    sorry))))))
    
    /-
      Contains (n, (m, e)), where:
      
      * n and m are natural numbers,
      * e is an encoding of an expression,
      * the depth of e is at most n,
      * e uses variables ≤ n,
      * for every n and m, e is unique,
      * for every a ≤ b and m, if (a, (m, e)) is
        in this type, (b, (m, e)) is too.
      * every finite portion of every definition list
        is in some (n, (m0-m1, e0-e1)).
    -/
    def setOfAllDef.defList.enumUpTo: Nat := sorry
    
    -- The set of pairs (n, s) such that s is a natural number,
    -- and for every definable triset of pairs dtp, there exists
    -- a natural number n such that `theSet & (n, Any) = dtp`
    def theSet: Nat := sorry
    
    def defList:
      DefList pairSignature
    := {
      getDef :=
        fun x => match x with
        | 0 => nat.expr
        | 1 => natPairAA.expr
        | 2 => natLe.expr
        | rest + 3 =>
            -- fstMember (rest + sorry + 1) (Expr.ir theSet (toNatLiteral rest))
            sorry
      
      isFinBounded := sorry
    }
  end setOfAllDef
end Pair
