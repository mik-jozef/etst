/-
  Defines "macro" expressions for the pair signature.
  See @file:WFC/Expr.lean for the definition of expressions.
  
  Inference rules in the style of those from
  `ExprRulesOfInference.lean` for these macros are
  also provided.
-/

import WFC.Appx0_ExprRulesOfInference
import Utils.Pair
import Utils.Set3


def Expr.intp
  (e: Expr pairSignature)
  (v: Valuation Pair)
:
  Set3 Pair
:=
  e.interpretation pairSalgebra v v

def Expr.intp2
  (e: Expr pairSignature)
  (b c: Valuation Pair)
:
  Set3 Pair
:=
  e.interpretation pairSalgebra b c

namespace PairExpr
  open Expr
  open Pair
  open pairSignature
  
  def Expr := _root_.Expr pairSignature
  
  instance exprOfNat: (n: Nat) → OfNat Expr n :=
    Expr.exprOfNat
  
  instance coe: Coe Nat (Expr) where
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
  
  def condSomeExpr (cond: Expr): Expr :=
    Expr.op Op.condSome fun _ => cond
  
  def condFullExpr (cond: Expr): Expr :=
    Expr.op Op.condFull fun _ => cond
  
  def unExpr (left rite: Expr): Expr :=
    Expr.op
      Op.un
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def irExpr (left rite: Expr): Expr :=
    Expr.op
      Op.ir
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def ifThenExpr (cond body: Expr): Expr :=
    irExpr (condSomeExpr cond) body
  
  def ifElseExpr (cond body: Expr): Expr :=
    irExpr (condFullExpr cond.cpl) body
  
  def iteExpr (cond yes no: Expr): Expr :=
    unExpr
      (ifThenExpr cond yes)
      (ifElseExpr cond no)
  
  -- Is empty if `expr` is inhabited, else is full.
  def negCondExpr (expr: Expr): Expr :=
    -- Expr.cpl (condSomeExpr expr)
    condFullExpr (expr.cpl)
  
  def pairCplExpr (a b: Expr) :=
    unExpr
      zeroExpr
      (unExpr
        (pairExpr a.cpl anyExpr)
        (pairExpr anyExpr b.cpl))
  
  
  /-
    `unionExpr x domain body` is "syntactic sugar" that represents
    an arbitrary union with a domain. The natural number `x`
    becomes a bound variable in `body`, and takes on the values
    of elements of `domain`.
    
    Due to the implementation of `unionExpr` (and necessarily so),
    `x` also becomes a bound variable in `domain`. To avoid
    unintended semantics, make sure `x` is not used (as a free
    variable) in `domain`.
  -/
  def unionExpr (x: Nat) (domain body: Expr): Expr :=
    Expr.arbUn x (ifThenExpr (irExpr x domain) body)
  
  /-
    `irsecExpr x domain body` is "syntactic sugar" that represents
    an arbitrary intersection with a domain. The natural number `x`
    becomes a bound variable in `body`, and takes on the values
    of elements of `domain`.
    
    Due to the implementation of `irsecExpr` (and necessarily so),
    `x` also becomes a bound variable in `domain`. To avoid
    unintended semantics, make sure `x` is not used (as a free
    variable) in `domain`.
  -/
  def irsecExpr (x: Nat) (domain body: Expr): Expr :=
    Expr.arbIr
      x
      (unExpr
        body
        -- "if x is outside the domain, then anyExpr"
        (ifThenExpr (Expr.cpl (irExpr x domain)) (anyExpr)))
  
  -- A union of finitely many expressions.
  def finUnExpr: List Expr → Expr
  | List.nil => noneExpr
  | List.cons expr tail =>
    unExpr expr (finUnExpr (tail))
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `zthMember n expr` then represents the set of all
    `a` such that `(a, _) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def zthMember (n: Nat) (expr: Expr): Expr :=
    Expr.arbUn n (ifThenExpr (irExpr (pairExpr n anyExpr) expr) n)
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def fstMember (n: Nat) (expr: Expr): Expr :=
    Expr.arbUn n (ifThenExpr (irExpr (pairExpr anyExpr n) expr) n)
  
  /-
    Let `fn` and `arg` be expressions that represent
    sets of pairs `sFn` and `sArg` (under some valuation).
    The expression `callExpr n fn arg` then represents
    the set of all `b` such that there exists an `a`
    such that `(a, b) ∈ sFn` and `a ∈ sArg`.
    
    `sFn` can be viewed as a function that, as a set,
    contains its input-output pairs.
    
    `n` must not be a free variable in `fn` or `arg`.
  -/
  def callExpr (n: Nat) (fn arg: Expr): Expr :=
    fstMember n (irExpr fn (pairExpr arg anyExpr))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succExpr nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.zero`.)
  -/
  def succExpr (expr: Expr): Expr := pairExpr expr zeroExpr
  
  def succ (pair: Pair): Pair := Pair.pair pair Pair.zero
  
  instance ofNat n: OfNat Pair n where
    ofNat := Pair.fromNat n
  
  /-
    Given a natural number `n`, `natExpr n` represents
    the encoding of `n` as a pair.
  -/
  def natExpr: Nat → Expr
  | Nat.zero => zeroExpr
  | Nat.succ pred => succExpr (natExpr pred)
  
  
  def InsP := Ins pairSalgebra
  def InwP := Inw pairSalgebra
  
  
  def insUnL
    (exprR: Expr)
    {exprL: Expr}
    (s: InsP b c exprL d)
  :
    InsP b c (unExpr exprL exprR) d
  :=
    Or.inl s
  
  def inwUnL
    (exprR: Expr)
    {exprL: Expr}
    (w: InwP b c exprL d)
  :
    InwP b c (unExpr exprL exprR) d
  :=
    Or.inl w
  
  
  def insUnR
    {exprR: Expr}
    (exprL: Expr)
    (s: InsP b c exprR d)
  :
    InsP b c (unExpr exprL exprR) d
  :=
    Or.inr s
  
  def inwUnR
    {exprR: Expr}
    (exprL: Expr)
    (w: InwP b c exprR d)
  :
    InwP b c (unExpr exprL exprR) d
  :=
    Or.inr w
  
  
  def insUnElim
    (s: InsP b c (unExpr exprL exprR) d)
  :
    Or
      (InsP b c exprL d)
      (InsP b c exprR d)
  :=
    s
  
  def inwUnElim
    (s: InwP b c (unExpr exprL exprR) d)
  :
    Or
      (InwP b c exprL d)
      (InwP b c exprR d)
  :=
    s
  
  
  def insIr
    (l: InsP b c exprL d)
    (r: InsP b c exprR d)
  :
    InsP b c (irExpr exprL exprR) d
  :=
    ⟨l, r⟩
  
  def inwIr
    (l: InwP b c exprL d)
    (r: InwP b c exprR d)
  :
    InwP b c (irExpr exprL exprR) d
  :=
    ⟨l, r⟩
  
  def insIrElim
    (s: InsP b c (irExpr exprL exprR) d)
  :
    And
      (InsP b c exprL d)
      (InsP b c exprR d)
  :=
    s
  
  def inwIrElim
    (s: InwP b c (irExpr exprL exprR) d)
  :
    And
      (InwP b c exprL d)
      (InwP b c exprR d)
  :=
    s
  
  
  def insCondSome
    (insExpr: InsP b c expr dE)
  :
    InsP b c (condSomeExpr expr) d
  :=
    ⟨dE, insExpr⟩
  
  def inwCondSome
    (insExpr: InwP b c expr dE)
  :
    InwP b c (condSomeExpr expr) d
  :=
    ⟨dE, insExpr⟩
  
  
  def insCondSomeElim
    (s: InsP b c (condSomeExpr expr) d)
  :
    ∃ dE, InsP b c expr dE
  :=
    let ⟨dE, insExpr⟩ := s
    ⟨dE, insExpr⟩
  
  def inwCondSomeElim
    (s: InwP b c (condSomeExpr expr) d)
  :
    ∃ dE, InwP b c expr dE
  :=
    s
  
  
  def insCondFull
    (allInsExpr: (dE: pairSalgebra.D) → InsP b c expr dE)
  :
    InsP b c (condFullExpr expr) d
  :=
    allInsExpr
  
  def inwCondFull
    (allInwExpr: (dE: pairSalgebra.D) → InwP b c expr dE)
  :
    InwP b c (condFullExpr expr) d
  :=
    allInwExpr
  
  
  def insCondFullElim
    (s: InsP b c (condFullExpr expr) d)
  :
    ∀ dE, InsP b c expr dE
  :=
    s
  
  def inwCondFullElim
    (s: InwP b c (condFullExpr expr) d)
  :
    ∀ dE, InwP b c expr dE
  :=
    s
  
  
  def insIfThen
    {cond: Expr}
    (insCond: InsP b c cond dC)
    (insBody: InsP b c body d)
  :
    InsP b c (ifThenExpr cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  def inwIfThen
    {cond: Expr}
    (insCond: InwP b c cond dC)
    (insBody: InwP b c body d)
  :
    InwP b c (ifThenExpr cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  
  def insIfThenElim
    {cond: Expr}
    (s: InsP b c (ifThenExpr cond body) d)
  :
    And
      (∃ dC, InsP b c cond dC)
      (InsP b c body d)
  :=
    let ⟨exCond, insBody⟩ := s
    
    And.intro exCond insBody
  
  def inwIfThenElim
    {cond: Expr}
    (s: InwP b c (ifThenExpr cond body) d)
  :
    And
      (∃ dC, InwP b c cond dC)
      (InwP b c body d)
  :=
    s
  
  
  /-
    This is not a mistake -- the valuation of the
    domain is updated too. It's unfortunate, but
    inevitable -- have a look at the implemetation
    of `unionExpr` to see for yourself.
  -/
  def insUnDom
    (insDomain:
      InsP (b.update x dBound) (c.update x dBound) domain dBound)
    (insBody:
      InsP (b.update x dBound) (c.update x dBound) body d)
  :
    InsP b c (unionExpr x domain body) d
  :=
    let inUpdated: ((c.update x dBound) x).defMem dBound :=
      Valuation.update.inEq.defMem c x dBound
    
    insArbUn _ ⟨⟨dBound, ⟨inUpdated, insDomain⟩⟩, insBody⟩
  
  def inwUnDom
    (inwDomain:
      InwP (b.update x dBound) (c.update x dBound) domain dBound)
    (inwBody:
      InwP (b.update x dBound) (c.update x dBound) body d)
  :
    InwP b c (unionExpr x domain body) d
  :=
    let inUpdated: ((c.update x dBound) x).posMem dBound :=
      Valuation.update.inEq.posMem c x dBound
    
    inwArbUn _ ⟨⟨dBound, ⟨inUpdated, inwDomain⟩⟩, inwBody⟩
  
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (Under the condition that any two instances are only
  -- allowed to contain the same instance, if need be).
  -- We have global choice anyway!
  structure InsUnDomElim
    (b c: Valuation Pair)
    (x: Nat)
    (dBound: Pair)
    (domain body: Expr)
    (d: Pair): Prop
  where
    insDomain:
      InsP (b.update x dBound) (c.update x dBound) domain dBound
    insBody: InsP (b.update x dBound) (c.update x dBound) body d
  
  def insUnDomElim
    (insUnDom: InsP b c (unionExpr x domain body) d)
  :
    ∃ dBound, InsUnDomElim b c x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    -- Inlining these vars causes a "failed to compute motive"
    -- error, and that's why I distrust tactics and hiding
    -- imperative code in them.
    let bUpdated := b.update x dBound
    let cUpdated := c.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      insBoundElim dInIr.property.left
    
    let insDomain:
      InsP bUpdated cUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        insDomain := insDomain
        insBody := dBound.property.right
      },
    ⟩
  
  structure InwUnDomElim
    (b c: Valuation Pair)
    (x: Nat)
    (dBound: Pair)
    (domain body: Expr)
    (d: Pair): Prop
  where
    inwDomain:
      InwP (b.update x dBound) (c.update x dBound) domain dBound
    inwBody: InwP (b.update x dBound) (c.update x dBound) body d
  
  def inwUnDomElim
    (insUnDom: InwP b c (unionExpr x domain body) d)
  :
    ∃ dBound, InwUnDomElim b c x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    let bUpdated := b.update x dBound
    let cUpdated := c.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      inwBoundElim dInIr.property.left
    
    let insDomain:
      InwP bUpdated cUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        inwDomain := insDomain
        inwBody := dBound.property.right
      },
    ⟩
  
  
  def insFinUn
    {list: List (Expr)}
    (exprIn: expr ∈ list)
    (s: InsP b c expr p)
  :
    InsP b c (finUnExpr list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ insUnL _ s)
        (fun inRest => insUnR _ (insFinUn inRest s))
  
  def inwFinUn
    {list: List (Expr)}
    (exprIn: expr ∈ list)
    (w: InwP b c expr p)
  :
    InwP b c (finUnExpr list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ inwUnL _ w)
        (fun inRest => inwUnR _ (inwFinUn inRest w))
  
  
  def InsFinUnElim
    (b c: Valuation Pair)
    (d: Pair)
    (P: Prop)
  :
    List (Expr) → Prop
  | List.nil => P
  | List.cons head tail =>
    (InsP b c head d → P) → InsFinUnElim b c d P tail
  
  def InsFinUnElim.ofP
    (list: List (Expr))
    (p: P)
  :
    InsFinUnElim b c d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def insFinUnElim
    (s: InsP b c (finUnExpr list) d)
  :
    InsFinUnElim b c d P list
  :=
    match list with
    | List.nil => False.elim (ninsNone s)
    | List.cons _head tail =>
      (insUnElim s).elim
        (fun insHead insHeadToP =>
          InsFinUnElim.ofP tail (insHeadToP insHead))
        (fun insTail _ => insFinUnElim insTail)
  
  
  def InwFinUnElim
    (b c: Valuation Pair)
    (d: Pair)
    (P: Prop)
  :
    List (Expr) → Prop
  | List.nil => P
  | List.cons head tail =>
    (InwP b c head d → P) → InwFinUnElim b c d P tail
  
  def inwFinUnElim.ofP
    (list: List (Expr))
    (p: P)
  :
    InwFinUnElim b c d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def inwFinUnElim
    (s: InwP b c (finUnExpr list) d)
  :
    InwFinUnElim b c d P list
  :=
    match list with
    | List.nil => False.elim (ninwNone s)
    | List.cons _head tail =>
      (inwUnElim s).elim
        (fun inwHead insHeadToP =>
          inwFinUnElim.ofP tail (insHeadToP inwHead))
        (fun insTail _ => inwFinUnElim insTail)
  
  
  def insZero:
    InsP b c zeroExpr Pair.zero
  :=
    rfl
  
  def insZeroElim
    (s: InsP b c zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def insZeroElim.neq
    (s: InsP b c zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def insZeroElim.nope
    (s: InsP b c zeroExpr (Pair.pair pA pB))
  :
    P
  :=
    False.elim (insZeroElim.neq s pA pB rfl)
  
  
  def inwZero:
    InwP b c zeroExpr Pair.zero
  :=
    rfl
  
  def inwZeroElim
    (s: InwP b c zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def inwZeroElim.neq
    (s: InwP b c zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def inwZeroElim.nope
    (s: InwP b c zeroExpr (Pair.pair pA pB))
  :
    P
  :=
    False.elim (inwZeroElim.neq s pA pB rfl)
  
  
  def insPair
    (insL: InsP b c exprL pairL)
    (insR: InsP b c exprR pairR)
  :
    InsP b c (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  def inwPair
    (insL: InwP b c exprL pairL)
    (insR: InwP b c exprR pairR)
  :
    InwP b c (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  
  structure InsPairElim
    (b c: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    insL: InsP b c exprL pairL
    insR: InsP b c exprR pairR
  
  def insPairElim
    (s: InsP b c (pairExpr exprL exprR) (Pair.pair pairL pairR))
  :
    InsPairElim b c exprL exprR pairL pairR
  :=
    let pl := s.unwrap
    let pr := pl.property.unwrap
    
    let plEq: pairL = pl :=
      Pair.noConfusion pr.property (fun eq _ => eq)
    let prEq: pairR = pr :=
      Pair.noConfusion pr.property (fun _ eq => eq)
    
    {
      insL := plEq ▸ pl.val.property
      insR := prEq ▸ pr.val.property
    }
  
  structure InsPairElim.Ex
    (b c: Valuation Pair)
    (exprL exprR: Expr)
    (p pairL pairR: Pair): Prop
  where
    eq: p = Pair.pair pairL pairR
    insL: InsP b c exprL pairL
    insR: InsP b c exprR pairR
  
  def insPairElim.ex
    (s: InsP b c (pairExpr exprL exprR) p)
  :
    ∃ pairL pairR: Pair,
      InsPairElim.Ex b c exprL exprR p pairL pairR
  :=
    match p with
    | Pair.zero =>
      Pair.noConfusion (s.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (insPairElim s).insL
        insR := (insPairElim s).insR
      }⟩
  
  def insPairElim.notZero
    (s: InsP b c (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex s).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def insPairElim.nope
    (s: InsP b c (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero s rfl).elim
  
  
  structure InwPairElim
    (b c: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    inwL: InwP b c exprL pairL
    inwR: InwP b c exprR pairR
  
  def inwPairElim
    (w: InwP b c (pairExpr exprL exprR) (Pair.pair pairL pairR))
  :
    InwPairElim b c exprL exprR pairL pairR
  :=
    let pl := w.unwrap
    let pr := pl.property.unwrap
    
    let plEq: pairL = pl :=
      Pair.noConfusion pr.property (fun eq _ => eq)
    let prEq: pairR = pr :=
      Pair.noConfusion pr.property (fun _ eq => eq)
    
    {
      inwL := plEq ▸ pl.val.property
      inwR := prEq ▸ pr.val.property
    }
  
  structure InwPairElim.Ex
    (b c: Valuation Pair)
    (exprL exprR: Expr)
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: InwP b c exprL pairL
    insR: InwP b c exprR pairR
  
  def inwPairElim.ex
    (w: InwP b c (pairExpr exprL exprR) p)
  :
    ∃ pairL pairR: Pair,
      InwPairElim.Ex b c exprL exprR p pairL pairR
  :=
    match p with
    | Pair.zero =>
      Pair.noConfusion (w.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (inwPairElim w).inwL
        insR := (inwPairElim w).inwR
      }⟩
  
  def inwPairElim.notZero
    (w: InwP b c (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex w).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inwPairElim.nope
    (w: InwP b c (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero w rfl).elim
  
  
  def insZthMember
    (s:
      InsP (b.update x pA) (c.update x pA) expr (Pair.pair pA pB))
  :
    InsP b c (zthMember x expr) pA
  :=
    insArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (insPair insBound insAny) s⟩,
      insBound,
    ⟩
  
  def inwZthMember
    (s:
      InwP (b.update x pA) (c.update x pA) expr (Pair.pair pA pB))
  :
    InwP b c (zthMember x expr) pA
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (inwPair inwBound inwAny) s⟩,
      inwBound,
    ⟩
  
  
  def insFstMember
    (s:
      InsP (b.update x pB) (c.update x pB) expr (Pair.pair pA pB))
  :
    InsP b c (fstMember x expr) pB
  :=
    insArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (insPair insAny insBound) s⟩,
      insBound,
    ⟩
  
  def inwFstMember
    (s:
      InwP (b.update x pB) (c.update x pB) expr (Pair.pair pA pB))
  :
    InwP b c (fstMember x expr) pB
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (inwPair inwAny inwBound) s⟩,
      inwBound,
    ⟩
  
  
  def insZthMemberElim
    (s: InsP b c (zthMember x expr) zth)
  :
    ∃ fst,
      InsP
        (b.update x zth)
        (c.update x zth)
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairXaAny, pCondInsExpr⟩⟩ := insCond
    
    match pCond with
    | Pair.zero => insPairElim.nope insPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := insPairElim insPairXaAny
      let eqPCondZth: pCondZth = pZth := insBoundElim insL
      let eqPZth: zth = pZth := insBoundElim insBody
      
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inwZthMemberElim
    (s: InwP b c (zthMember x expr) zth)
  :
    ∃ fst,
      InwP
        (b.update x zth)
        (c.update x zth)
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairXaAny, pCondInwExpr⟩⟩ := inwCond
    
    match pCond with
    | Pair.zero => inwPairElim.nope inwPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := inwPairElim inwPairXaAny
      let eqPCondZth: pCondZth = pZth := inwBoundElim insL
      let eqPZth: zth = pZth := inwBoundElim inwBody
      
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInwExpr⟩
  
  def insFstMemberElim
    (s: InsP b c (fstMember x expr) fst)
  :
    ∃ zth,
      InsP
        (b.update x fst)
        (c.update x fst)
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairAnyXa, pCondInsExpr⟩⟩ := insCond
    
    match pCond with
    | Pair.zero => insPairElim.nope insPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := insPairElim insPairAnyXa
      let eqPCondZth: pCondFst = pFst := insBoundElim insR
      let eqPZth: fst = pFst := insBoundElim insBody
      
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inwFstMemberElim
    (s: InwP b c (fstMember x expr) fst)
  :
    ∃ zth,
      InwP
        (b.update x fst)
        (c.update x fst)
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairAnyXa, pCondInwExpr⟩⟩ := inwCond
    
    match pCond with
    | Pair.zero => inwPairElim.nope inwPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := inwPairElim inwPairAnyXa
      let eqPCondZth: pCondFst = pFst := inwBoundElim insR
      let eqPZth: fst = pFst := inwBoundElim inwBody
      
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ pCondInwExpr⟩
  
  
  def insZthFstElim
    (insZth: InsP b c (zthMember xA (var xB)) zth)
    (insFst: InsP b c (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: c xB = Set3.just d)
  :
    InsP b c xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, insChosenFst⟩ := insZthMemberElim insZth
    let ⟨chosenZth, insChosenZth⟩ := insFstMemberElim insFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inDefToEqBin d
        (isUnit ▸ (insFreeElim insChosenFst neq))
        (isUnit ▸ (insFreeElim insChosenZth neq))
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ (insFreeElim insChosenZth neq)
  
  def inwZthFstElim
    (inwZth: InwP b c (zthMember xA (var xB)) zth)
    (inwFst: InwP b c (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: c xB = Set3.just d)
  :
    InwP b c xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, inwChosenFst⟩ := inwZthMemberElim inwZth
    let ⟨chosenZth, inwChosenZth⟩ := inwFstMemberElim inwFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inPosToEqBin d
        (isUnit ▸ (inwFreeElim inwChosenFst neq))
        (isUnit ▸ (inwFreeElim inwChosenZth neq))
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ (inwFreeElim inwChosenZth neq)
  
  
  def insCallExpr
    (insFn:
      InsP (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
    (insArg:
      InsP (b.update x pB) (c.update x pB) arg pA)
  :
    InsP b c (callExpr x fn arg) pB
  :=
    insFstMember (insIr insFn (insPair insArg insAny))
  
  def inwCallExpr
    (inwFn:
      InwP (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
    (inwArg:
      InwP (b.update x pB) (c.update x pB) arg pA)
  :
    InwP b c (callExpr x fn arg) pB
  :=
    inwFstMember (inwIr inwFn (inwPair inwArg inwAny))
  
  
  def insCallExprElim
    (s: InsP b c (callExpr x fn arg) pB)
  :
    ∃ pA,
      And
        (InsP (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
        (InsP (b.update x pB) (c.update x pB) arg pA)
  :=
    let ⟨zth, insIr⟩ := insFstMemberElim s
    let ⟨insFn, insP⟩ := insIrElim insIr
    
    ⟨zth, And.intro insFn (insPairElim insP).insL⟩
  
  def inwCallExprElim
    (w: InwP b c (callExpr x fn arg) bA)
  :
    ∃ pA,
      And
        (InwP (b.update x bA) (c.update x bA) fn (Pair.pair pA bA))
        (InwP (b.update x bA) (c.update x bA) arg pA)
  :=
    let ⟨zth, inwIr⟩ := inwFstMemberElim w
    let ⟨inwFn, inwP⟩ := inwIrElim inwIr
    
    ⟨zth, And.intro inwFn (inwPairElim inwP).inwL⟩
  
  def insCallElimBound
    (s: InsP b c (callExpr x fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
    (neq: x ≠ arg)
  :
    InsP (b.update x pB) (c.update x pB) fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨insFn, insArg⟩⟩ := insCallExprElim s
    
    let insVArg: (c arg).defMem aAlias := insFreeElim insArg neq
    let eq: aAlias = pA := Set3.just.inDefToEq (isUnit ▸ insVArg)
    
    eq ▸ insFn
  
  def inwCallElimBound
    (w: InwP b c (callExpr x fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
    (neq: x ≠ arg)
  :
    InwP (b.update x pB) (c.update x pB) fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim w
    
    let inwVArg: (c arg).posMem aAlias := inwFreeElim inwArg neq
    let eq: aAlias = pA := Set3.just.inPosToEq (isUnit ▸ inwVArg)
    
    eq ▸ inwFn
  
  
  def insNatExpr b c n
  :
    InsP b c (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => insZero
    | Nat.succ pred => insPair (insNatExpr b c pred) insZero
  
  def inwNatExpr b c n
  :
    InwP b c (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => inwZero
    | Nat.succ pred => inwPair (inwNatExpr b c pred) inwZero
  
  def inwNatExprElim
    (w: InwP b c (natExpr n) p)
  :
    p = fromNat n
  :=
    match n, p with
    | Nat.zero, _ => inwZeroElim w ▸ rfl
    | Nat.succ _, zero => inwPairElim.nope w
    | Nat.succ _, pair _ _ =>
      let ⟨l, r⟩ := inwPairElim w
      (inwNatExprElim l) ▸ (inwZeroElim r) ▸ rfl
  
  def insNatExprElim
    (s: InsP b c (natExpr n) p)
  :
    p = fromNat n
  :=
    inwNatExprElim s.toInw
  
  def inwNatExprElimNope
    (w: InwP b c (natExpr n) (fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    (neq (fromNat.injEq (Eq.symm (inwNatExprElim w)))).elim
  
  def insNatExprElimNope
    (s: InsP b c (natExpr n) (fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    inwNatExprElimNope s.toInw neq
  
  def inwNatExprElimDepth
    (w: InwP b c (natExpr n) p)
  :
    depth p = n
  :=
    (inwNatExprElim w) ▸ (fromNat.depthEq _)
  
  def insNatExprElimDecode
    (s: InsP b c (natExpr n) p)
  :
    depth p = n
  :=
    inwNatExprElimDepth s.toInw
  
  
  def pair_eq_of_eq_def
    (eqL: (exprL0.intp2 b c).defMem = (exprL1.intp2 b c).defMem)
    (eqR: (exprR0.intp2 b c).defMem = (exprR1.intp2 b c).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (pairExpr exprL0 exprR0)).defMem
      (Expr.interpretation pairSalgebra b c (pairExpr exprL1 exprR1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨l, r, eq⟩ => ⟨
          ⟨l, show (interpretation _ b c exprL1).defMem l from
            eqL ▸ l.property⟩,
          ⟨r, show (interpretation _ b c exprR1).defMem r from
            eqR ▸ r.property⟩,
          eq
        ⟩)
        (fun ⟨l, r, eq⟩ => ⟨
          ⟨l, show (interpretation _ b c exprL0).defMem l from
            eqL ▸ l.property⟩,
          ⟨r, show (interpretation _ b c exprR0).defMem r from
            eqR ▸ r.property⟩,
          eq
        ⟩)
  
  def pair_eq_of_eq_pos
    (eqL: (exprL0.intp2 b c).posMem = (exprL1.intp2 b c).posMem)
    (eqR: (exprR0.intp2 b c).posMem = (exprR1.intp2 b c).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (pairExpr exprL0 exprR0)).posMem
      (Expr.interpretation pairSalgebra b c (pairExpr exprL1 exprR1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨l, r, eq⟩ => ⟨
          ⟨l, show (interpretation _ b c exprL1).posMem l from
            eqL ▸ l.property⟩,
          ⟨r, show (interpretation _ b c exprR1).posMem r from
            eqR ▸ r.property⟩,
          eq
        ⟩)
        (fun ⟨l, r, eq⟩ => ⟨
          ⟨l, show (interpretation _ b c exprL0).posMem l from
            eqL ▸ l.property⟩,
          ⟨r, show (interpretation _ b c exprR0).posMem r from
            eqR ▸ r.property⟩,
          eq
        ⟩)
  
  def pair_eq_of_eq
    (lEq: (exprL0.intp2 b c) = (exprL1.intp2 b c))
    (rEq: (exprR0.intp2 b c) = (exprR1.intp2 b c))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (pairExpr exprL0 exprR0))
      (Expr.interpretation pairSalgebra b c (pairExpr exprL1 exprR1))
  :=
    Set3.eq
      (pair_eq_of_eq_def (Set3.def_eq lEq) (Set3.def_eq rEq))
      (pair_eq_of_eq_pos (Set3.pos_eq lEq) (Set3.pos_eq rEq))
  
  
  def un_eq_of_eq_def
    (eqL: (exprL0.intp2 b c).defMem = (exprL1.intp2 b c).defMem)
    (eqR: (exprR0.intp2 b c).defMem = (exprR1.intp2 b c).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (unExpr exprL0 exprR0)).defMem
      (Expr.interpretation pairSalgebra b c (unExpr exprL1 exprR1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun
          | Or.inl isDef => Or.inl (show Set3.defMem _ _ from eqL ▸ isDef)
          | Or.inr isDef => Or.inr (show Set3.defMem _ _ from eqR ▸ isDef))
        (fun
          | Or.inl isDef => Or.inl (show Set3.defMem _ _ from eqL.symm ▸ isDef)
          | Or.inr isDef => Or.inr (show Set3.defMem _ _ from eqR.symm ▸ isDef))
  
  def un_eq_of_eq_pos
    (eqL: (exprL0.intp2 b c).posMem = (exprL1.intp2 b c).posMem)
    (eqR: (exprR0.intp2 b c).posMem = (exprR1.intp2 b c).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (unExpr exprL0 exprR0)).posMem
      (Expr.interpretation pairSalgebra b c (unExpr exprL1 exprR1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun
          | Or.inl isPos => Or.inl (show Set3.posMem _ _ from eqL ▸ isPos)
          | Or.inr isPos => Or.inr (show Set3.posMem _ _ from eqR ▸ isPos))
        (fun
          | Or.inl isPos => Or.inl (show Set3.posMem _ _ from eqL.symm ▸ isPos)
          | Or.inr isPos => Or.inr (show Set3.posMem _ _ from eqR.symm ▸ isPos))

  def un_eq_of_eq
    (lEq: (exprL0.intp2 b c) = (exprL1.intp2 b c))
    (rEq: (exprR0.intp2 b c) = (exprR1.intp2 b c))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (unExpr exprL0 exprR0))
      (Expr.interpretation pairSalgebra b c (unExpr exprL1 exprR1))
  :=
    Set3.eq
      (un_eq_of_eq_def (Set3.def_eq lEq) (Set3.def_eq rEq))
      (un_eq_of_eq_pos (Set3.pos_eq lEq) (Set3.pos_eq rEq))
  
  
  def ir_eq_of_eq_def
    (eqL: (exprL0.intp2 b c).defMem = (exprL1.intp2 b c).defMem)
    (eqR: (exprR0.intp2 b c).defMem = (exprR1.intp2 b c).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (irExpr exprL0 exprR0)).defMem
      (Expr.interpretation pairSalgebra b c (irExpr exprL1 exprR1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨l, r⟩ => ⟨
          show Set3.defMem _ _ from eqL ▸ l,
          show Set3.defMem _ _ from eqR ▸ r,
        ⟩)
        (fun ⟨l, r⟩ => ⟨
          show Set3.defMem _ _ from eqL.symm ▸ l,
          show Set3.defMem _ _ from eqR.symm ▸ r,
        ⟩)
  
  def ir_eq_of_eq_pos
    (eqL: (exprL0.intp2 b c).posMem = (exprL1.intp2 b c).posMem)
    (eqR: (exprR0.intp2 b c).posMem = (exprR1.intp2 b c).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (irExpr exprL0 exprR0)).posMem
      (Expr.interpretation pairSalgebra b c (irExpr exprL1 exprR1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨l, r⟩ =>
          ⟨show Set3.posMem _ _ from eqL ▸ l,
            show Set3.posMem _ _ from eqR ▸ r⟩)
        (fun ⟨l, r⟩ =>
          ⟨show Set3.posMem _ _ from eqL.symm ▸ l,
            show Set3.posMem _ _ from eqR.symm ▸ r⟩)

  def ir_eq_of_eq
    (l: (exprL0.intp2 b c) = (exprL1.intp2 b c))
    (r: (exprR0.intp2 b c) = (exprR1.intp2 b c))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (irExpr exprL0 exprR0))
      (Expr.interpretation pairSalgebra b c (irExpr exprL1 exprR1))
  :=
    Set3.eq
      (ir_eq_of_eq_def (Set3.def_eq l) (Set3.def_eq r))
      (ir_eq_of_eq_pos (Set3.pos_eq l) (Set3.pos_eq r))
  
  
  def condSome_eq_of_eq_def
    (eq: (expr0.intp2 b c).defMem = (expr1.intp2 b c).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr0)).defMem
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨p, isDef⟩ => ⟨p, show Set3.defMem _ _ from eq ▸ isDef⟩)
        (fun ⟨p, isDef⟩ => ⟨p, show Set3.defMem _ _ from eq ▸ isDef⟩)
  
  def condSome_eq_of_eq_pos
    (eq: (expr0.intp2 b c).posMem = (expr1.intp2 b c).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr0)).posMem
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨p, isPos⟩ => ⟨p, show Set3.posMem _ _ from eq ▸ isPos⟩)
        (fun ⟨p, isPos⟩ => ⟨p, show Set3.posMem _ _ from eq ▸ isPos⟩)
  
  def condSome_eq_of_eq
    (eq: (expr0.intp2 b c) = (expr1.intp2 b c))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr0))
      (Expr.interpretation pairSalgebra b c (condSomeExpr expr1))
  :=
    Set3.eq
      (condSome_eq_of_eq_def (Set3.def_eq eq))
      (condSome_eq_of_eq_pos (Set3.pos_eq eq))
  
  
  def condFull_eq_of_eq_def
    (eq: (expr0.intp2 b c).defMem = (expr1.intp2 b c).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condFullExpr expr0)).defMem
      (Expr.interpretation pairSalgebra b c (condFullExpr expr1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDef p => show Set3.defMem _ _ from eq ▸ isDef p)
        (fun isDef p => show Set3.defMem _ _ from eq ▸ isDef p)
  
  def condFull_eq_of_eq_pos
    (eq: (expr0.intp2 b c).posMem = (expr1.intp2 b c).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condFullExpr expr0)).posMem
      (Expr.interpretation pairSalgebra b c (condFullExpr expr1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPos p => show Set3.posMem _ _ from eq ▸ isPos p)
        (fun isPos p => show Set3.posMem _ _ from eq ▸ isPos p)

  def condFull_eq_of_eq
    (eq: (expr0.intp2 b c) = (expr1.intp2 b c))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (condFullExpr expr0))
      (Expr.interpretation pairSalgebra b c (condFullExpr expr1))
  :=
    Set3.eq
      (condFull_eq_of_eq_def (Set3.def_eq eq))
      (condFull_eq_of_eq_pos (Set3.pos_eq eq))
  
  
  def cpl_eq_of_eq_def
    (eq: (expr0.intp2 b b).posMem = (expr1.intp2 b b).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr0)).defMem
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDef isPos => isDef (show Set3.posMem _ _ from eq ▸ isPos))
        (fun isDef isPos => isDef (show Set3.posMem _ _ from eq ▸ isPos))
  
  def cpl_eq_of_eq_pos
    {b: Valuation Pair}
    (c := b)
    (eq: (expr0.intp2 b b).defMem = (expr1.intp2 b b).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr0)).posMem
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPos isDef => isPos (show Set3.defMem _ _ from eq ▸ isDef))
        (fun isPos isDef => isPos (show Set3.defMem _ _ from eq ▸ isDef))

  def cpl_eq_of_eq
    {b: Valuation Pair}
    (c := b)
    (eq: (expr0.intp2 b b) = (expr1.intp2 b b))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr0))
      (Expr.interpretation pairSalgebra b c (Expr.cpl expr1))
  :=
    Set3.eq
      (cpl_eq_of_eq_def (c := c) (Set3.pos_eq eq))
      (cpl_eq_of_eq_pos (c := c) (Set3.def_eq eq))
  
  
  def arbUn_eq_of_eq_def
    (x: Nat)
    (eq:
      (p: Pair) →
      Eq
        (expr0.intp2 (b.update x p) (c.update x p)).defMem
        (expr1.intp2 (b.update x p) (c.update x p)).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr0)).defMem
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨p, isDef⟩ => ⟨p, show Set3.defMem _ _ from eq p ▸ isDef⟩)
        (fun ⟨p, isDef⟩ => ⟨p, show Set3.defMem _ _ from eq p ▸ isDef⟩)
  
  def arbUn_eq_of_eq_pos
    (x: Nat)
    (eq:
      (p: Pair) →
      Eq
        (expr0.intp2 (b.update x p) (c.update x p)).posMem
        (expr1.intp2 (b.update x p) (c.update x p)).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr0)).posMem
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨p, isPos⟩ => ⟨p, show Set3.posMem _ _ from eq p ▸ isPos⟩)
        (fun ⟨p, isPos⟩ => ⟨p, show Set3.posMem _ _ from eq p ▸ isPos⟩)

  def arbUn_eq_of_eq
    (x: Nat)
    (eq:
      (p: Pair) →
      (expr0.intp2 (b.update x p) (c.update x p)) =
      (expr1.intp2 (b.update x p) (c.update x p)))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr0))
      (Expr.interpretation pairSalgebra b c (Expr.arbUn x expr1))
  :=
    Set3.eq
      (arbUn_eq_of_eq_def x (fun p => Set3.def_eq (eq p)))
      (arbUn_eq_of_eq_pos x (fun p => Set3.pos_eq (eq p)))
  
  
  def arbIr_eq_of_eq_def
    (x: Nat)
    (eq:
      (p: Pair) →
      Eq
        (expr0.intp2 (b.update x p) (c.update x p)).defMem
        (expr1.intp2 (b.update x p) (c.update x p)).defMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr0)).defMem
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr1)).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDef p => show Set3.defMem _ _ from eq p ▸ isDef p)
        (fun isDef p => show Set3.defMem _ _ from eq p ▸ isDef p)
  
  def arbIr_eq_of_eq_pos
    (x: Nat)
    (eq:
      (p: Pair) →
      Eq
        (expr0.intp2 (b.update x p) (c.update x p)).posMem
        (expr1.intp2 (b.update x p) (c.update x p)).posMem)
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr0)).posMem
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr1)).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPos p => show Set3.posMem _ _ from eq p ▸ isPos p)
        (fun isPos p => show Set3.posMem _ _ from eq p ▸ isPos p)

  def arbIr_eq_of_eq
    (x: Nat)
    (eq:
      (p: Pair) →
      (expr0.intp2 (b.update x p) (c.update x p)) =
      (expr1.intp2 (b.update x p) (c.update x p)))
  :
    Eq
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr0))
      (Expr.interpretation pairSalgebra b c (Expr.arbIr x expr1))
  :=
    Set3.eq
      (arbIr_eq_of_eq_def x (fun p => Set3.def_eq (eq p)))
      (arbIr_eq_of_eq_pos x (fun p => Set3.pos_eq (eq p)))
  
  
  def cpl_zero_eq_def
    (v: Valuation Pair)
  :
    Eq
      (zeroExpr.cpl.intp v).defMem
      ((pairExpr anyExpr anyExpr).intp v).defMem
  :=
    Set.ext fun p =>
      Iff.intro
        (fun isDefCpl =>
          match p, isDefCpl with
          | .pair pa pb, _ => ⟨⟨pa, insAny⟩, ⟨pb, insAny⟩, rfl⟩)
        (fun isDefPair =>
          match p, isDefPair with
          | .pair _ _, _ => Pair.noConfusion)
  
  def cpl_zero_eq_pos
    (v: Valuation Pair)
  :
    Eq
      (zeroExpr.cpl.intp v).posMem
      ((pairExpr anyExpr anyExpr).intp v).posMem
  :=
    -- Happens to typecheck since def and pos members agree :smile:
    cpl_zero_eq_def v
  
  def cpl_zero_eq
    (v: Valuation Pair)
  :
    zeroExpr.cpl.intp v = (pairExpr anyExpr anyExpr).intp v
  :=
    Set3.eq (cpl_zero_eq_def v) (cpl_zero_eq_pos v)
  
  
  def cpl_pair_eq_def
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((pairExpr a b).cpl.intp v).defMem
      (Expr.intp (pairCplExpr a b) v).defMem
  :=
    Set.ext fun p =>
      Iff.intro
        (fun isDefCpl =>
          match p with
          | .zero => Or.inl rfl
          | .pair pa pb =>
            let neq := isDefCpl.toAll fun _ p =>
              p.toAll fun _ => id
            if hA: ¬ (a.intp v).posMem pa then
              Or.inr (Or.inl (insPair hA insAny))
            else if hB: ¬ (b.intp v).posMem pb then
              Or.inr (Or.inr (insPair insAny hB))
            else
              False.elim (neq ⟨pa, hA.dne⟩ ⟨pb, hB.dne⟩ rfl))
        nofun
  
  def cpl_pair_eq_pos
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((pairExpr a b).cpl.intp v).posMem
      (Expr.intp (pairCplExpr a b) v).posMem
  :=
    Set.ext fun p =>
      Iff.intro
        (fun isPosCpl =>
          match p with
          | .zero => Or.inl rfl
          | .pair pa pb =>
            let neq := isPosCpl.toAll fun _ p =>
              p.toAll fun _ => id
            if hA: ¬ (a.intp v).defMem pa then
              Or.inr (Or.inl (inwPair hA inwAny))
            else if hB: ¬ (b.intp v).defMem pb then
              Or.inr (Or.inr (inwPair inwAny hB))
            else
              False.elim (neq ⟨pa, hA.dne⟩ ⟨pb, hB.dne⟩ rfl))
        nofun
  
  def cpl_pair_eq
    (v: Valuation Pair)
    (a b: Expr)
  :
    (pairExpr a b).cpl.intp v = Expr.intp (pairCplExpr a b) v
  :=
    Set3.eq (cpl_pair_eq_def v a b) (cpl_pair_eq_pos v a b)
  
  
  def cpl_un_eq_def
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((unExpr a b).cpl.intp v).defMem
      ((irExpr a.cpl b.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro Not.toAnd (fun ⟨l, r⟩ or => or.elim l r)
  
  def cpl_un_eq_pos
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((unExpr a b).cpl.intp v).posMem
      ((irExpr a.cpl b.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro Not.toAnd (fun ⟨l, r⟩ or => or.elim l r)
  
  def cpl_un_eq
    (v: Valuation Pair)
    (a b: Expr)
  :
    (unExpr a b).cpl.intp v = (irExpr a.cpl b.cpl).intp v
  :=
    Set3.eq (cpl_un_eq_def v a b) (cpl_un_eq_pos v a b)
  
  
  def cpl_ir_eq_def
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((irExpr a b).cpl.intp v).defMem
      ((unExpr a.cpl b.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro Not.toOr (fun or ⟨l, r⟩ => or.elim (· l) (· r))
  
  def cpl_ir_eq_pos
    (v: Valuation Pair)
    (a b: Expr)
  :
    Eq
      ((irExpr a b).cpl.intp v).posMem
      ((unExpr a.cpl b.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro Not.toOr (fun or ⟨l, r⟩ => or.elim (· l) (· r))
  
  def cpl_ir_eq
    (v: Valuation Pair)
    (a b: Expr)
  :
    (irExpr a b).cpl.intp v = (unExpr a.cpl b.cpl).intp v
  :=
    Set3.eq (cpl_ir_eq_def v a b) (cpl_ir_eq_pos v a b)
  
  
  def cpl_condSome_eq_def
    (v: Valuation Pair)
    (e: Expr)
  :
    Eq
      ((condSomeExpr e).cpl.intp v).defMem
      ((condFullExpr e.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDefCpl _ isPos => isDefCpl ⟨_, isPos⟩)
        (fun isDefCondFull ⟨_, isPos⟩ => isDefCondFull _ isPos)
  
  def cpl_condSome_eq_pos
    (v: Valuation Pair)
    (e: Expr)
  :
    Eq
      ((condSomeExpr e).cpl.intp v).posMem
      ((condFullExpr e.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDefCpl _ isDef => isDefCpl ⟨_, isDef⟩)
        (fun isDefCondFull ⟨_, isDef⟩ => isDefCondFull _ isDef)
  
  def cpl_condSome_eq
    (v: Valuation Pair)
    (e: Expr)
  :
    (condSomeExpr e).cpl.intp v = (condFullExpr e.cpl).intp v
  :=
    Set3.eq (cpl_condSome_eq_def v e) (cpl_condSome_eq_pos v e)
  
  
  def cpl_condFull_eq_def
    (v: Valuation Pair)
    (e: Expr)
  :
    Eq
      ((condFullExpr e).cpl.intp v).defMem
      ((condSomeExpr e.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDefCpl => isDefCpl.toEx fun _ => id)
        (fun ⟨_, ninPos⟩ isPosFull => ninPos (isPosFull _))
  
  def cpl_condFull_eq_pos
    (v: Valuation Pair)
    (e: Expr)
  :
    Eq
      ((condFullExpr e).cpl.intp v).posMem
      ((condSomeExpr e.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPosCpl => isPosCpl.toEx fun _ => id)
        (fun ⟨_, ninDef⟩ isPosFull => ninDef (isPosFull _))
  
  def cpl_condFull_eq
    (v: Valuation Pair)
    (e: Expr)
  :
    (condFullExpr e).cpl.intp v = (condSomeExpr e.cpl).intp v
  :=
    Set3.eq (cpl_condFull_eq_def v e) (cpl_condFull_eq_pos v e)
  
  
  def cpl_arbUn_eq_def
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    Eq
      ((arbUn x body).cpl.intp v).defMem
      ((arbIr x body.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDefCpl => isDefCpl.toAll fun _ => id)
        (fun isDefIr ⟨p, isPos⟩ => isDefIr p isPos)
  
  def cpl_arbUn_eq_pos
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    Eq
      ((arbUn x body).cpl.intp v).posMem
      ((arbIr x body.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPosCpl => isPosCpl.toAll fun _ => id)
        (fun isPosIr ⟨p, isDef⟩ => isPosIr p isDef)

  def cpl_arbUn_eq
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    ((arbUn x body).cpl.intp v) = ((arbIr x body.cpl).intp v)
  :=
    Set3.eq
      (cpl_arbUn_eq_def v x body)
      (cpl_arbUn_eq_pos v x body)
  
  
  def cpl_arbIr_eq_def
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    Eq
      ((arbIr x body).cpl.intp v).defMem
      ((arbUn x body.cpl).intp v).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isDefCpl => isDefCpl.toEx fun _ => id)
        (fun ⟨_, isPosUn⟩ isDef => isPosUn (isDef _))
  
  def cpl_arbIr_eq_pos
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    Eq
      ((arbIr x body).cpl.intp v).posMem
      ((arbUn x body.cpl).intp v).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun isPosCpl => isPosCpl.toEx fun _ => id)
        (fun ⟨_, isDefUn⟩ isPos => isDefUn (isPos _))

  def cpl_arbIr_eq
    (v: Valuation Pair)
    (x: Nat)
    (body: Expr)
  :
    ((arbIr x body).cpl.intp v) = ((arbUn x body.cpl).intp v)
  :=
    Set3.eq
      (cpl_arbIr_eq_def v x body)
      (cpl_arbIr_eq_pos v x body)
  
  
  def un_symm_def
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    Eq
      ((unExpr e0 e1).intp2 b c).defMem
      ((unExpr e1 e0).intp2 b c).defMem
  :=
    Set.ext fun _ => Iff.intro Or.symm Or.symm
  
  def un_symm_pos
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    Eq
      ((unExpr e0 e1).intp2 b c).posMem
      ((unExpr e1 e0).intp2 b c).posMem
  :=
    Set.ext fun _ => Iff.intro Or.symm Or.symm
  
  def un_symm
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    (unExpr e0 e1).intp2 b c = (unExpr e1 e0).intp2 b c
  :=
    Set3.eq
      (un_symm_def b c e0 e1)
      (un_symm_pos b c e0 e1)
  
  
  def un_assoc_def
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    Eq
      ((unExpr e0 (unExpr e1 e2)).intp2 b c).defMem
      ((unExpr (unExpr e0 e1) e2).intp2 b c).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun
          | Or.inl isDef => Or.inl (Or.inl isDef)
          | Or.inr (Or.inl isDef) => Or.inl (Or.inr isDef)
          | Or.inr (Or.inr isDef) => Or.inr isDef)
        (fun
          | Or.inl (Or.inl isDef) => Or.inl isDef
          | Or.inl (Or.inr isDef) => Or.inr (Or.inl isDef)
          | Or.inr isDef => Or.inr (Or.inr isDef))
  
  def un_assoc_pos
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    Eq
      ((unExpr e0 (unExpr e1 e2)).intp2 b c).posMem
      ((unExpr (unExpr e0 e1) e2).intp2 b c).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun
          | Or.inl isPos => Or.inl (Or.inl isPos)
          | Or.inr (Or.inl isPos) => Or.inl (Or.inr isPos)
          | Or.inr (Or.inr isPos) => Or.inr isPos)
        (fun
          | Or.inl (Or.inl isPos) => Or.inl isPos
          | Or.inl (Or.inr isPos) => Or.inr (Or.inl isPos)
          | Or.inr isPos => Or.inr (Or.inr isPos))

  def un_assoc
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    (unExpr e0 (unExpr e1 e2)).intp2 b c = (unExpr (unExpr e0 e1) e2).intp2 b c
  :=
    Set3.eq
      (un_assoc_def b c e0 e1 e2)
      (un_assoc_pos b c e0 e1 e2)
  
  
  def ir_symm_def
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    Eq
      ((irExpr e0 e1).intp2 b c).defMem
      ((irExpr e1 e0).intp2 b c).defMem
  :=
    Set.ext fun _ => Iff.intro And.symm And.symm

  def ir_symm_pos
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    Eq
      ((irExpr e0 e1).intp2 b c).posMem
      ((irExpr e1 e0).intp2 b c).posMem
  :=
    Set.ext fun _ => Iff.intro And.symm And.symm

  def ir_symm
    (b c: Valuation Pair)
    (e0 e1: Expr)
  :
    (irExpr e0 e1).intp2 b c = (irExpr e1 e0).intp2 b c
  :=
    Set3.eq
      (ir_symm_def b c e0 e1)
      (ir_symm_pos b c e0 e1)
  
  
  def ir_assoc_def
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    Eq
      ((irExpr e0 (irExpr e1 e2)).intp2 b c).defMem
      ((irExpr (irExpr e0 e1) e2).intp2 b c).defMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨isDef0, ⟨isDef1, isDef2⟩⟩ => ⟨⟨isDef0, isDef1⟩, isDef2⟩)
        (fun ⟨⟨isDef0, isDef1⟩, isDef2⟩ => ⟨isDef0, ⟨isDef1, isDef2⟩⟩)

  def ir_assoc_pos
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    Eq
      ((irExpr e0 (irExpr e1 e2)).intp2 b c).posMem
      ((irExpr (irExpr e0 e1) e2).intp2 b c).posMem
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ⟨isPos0, ⟨isPos1, isPos2⟩⟩ => ⟨⟨isPos0, isPos1⟩, isPos2⟩)
        (fun ⟨⟨isPos0, isPos1⟩, isPos2⟩ => ⟨isPos0, ⟨isPos1, isPos2⟩⟩)

  def ir_assoc
    (b c: Valuation Pair)
    (e0 e1 e2: Expr)
  :
    (irExpr e0 (irExpr e1 e2)).intp2 b c = (irExpr (irExpr e0 e1) e2).intp2 b c
  :=
    Set3.eq
      (ir_assoc_def b c e0 e1 e2)
      (ir_assoc_pos b c e0 e1 e2)
  
end PairExpr


def Expr.toString: Expr pairSignature → String
| .var x => s!"#{x}"
| .op pairSignature.Op.un args =>
  let left := (args ArityTwo.zth).toString
  let rite := (args ArityTwo.fst).toString
  s!"({left}) | ({rite})"
| .op pairSignature.Op.ir args =>
  let left := (args ArityTwo.zth).toString
  let rite := (args ArityTwo.fst).toString
  s!"({left}) & ({rite})"
| .op pairSignature.Op.condSome args =>
  let cond := (args ArityOne.zth).toString
  s!"(?i {cond})"
| .op pairSignature.Op.condFull args =>
  let cond := (args ArityOne.zth).toString
  s!"(?f {cond})"
| .op pairSignature.Op.zero _ =>
  "null"
| .op pairSignature.Op.pair args =>
  let left := (args ArityTwo.zth).toString
  let rite := (args ArityTwo.fst).toString
  s!"({left}, {rite})"
| .cpl expr =>
  let exprStr := expr.toString
  s!"!({exprStr})"
| .arbUn x body =>
  let bodyStr := body.toString
  s!"Ex {x}, ({bodyStr})"
| .arbIr x body =>
  let bodyStr := body.toString
  s!"All {x}, ({bodyStr})"

instance: ToString (Expr pairSignature) where
  toString := Expr.toString
