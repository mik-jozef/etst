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


namespace PairExpr
  open Expr
  open Pair
  open pairSignature
  
  @[reducible]
  def Expr Var := _root_.Expr Var pairSignature
  
  
  def zeroExpr: Expr Var :=
    Expr.op Op.zero ArityZero.elim
  
  def pairExpr (left rite: Expr Var): Expr Var :=
    Expr.op
      Op.pair
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def unExpr (left rite: Expr Var): Expr Var :=
    Expr.op
      Op.un
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def irExpr (left rite: Expr Var): Expr Var :=
    Expr.op
      Op.ir
      fun arg =>
        match arg with
        | ArityTwo.zth => left
        | ArityTwo.fst => rite
  
  def ifThenExpr (cond body: Expr Var): Expr Var :=
    Expr.op
      Op.ifThen
      fun arg =>
        match arg with
        | ArityTwo.zth => cond
        | ArityTwo.fst => body
  
  
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
  def unionExpr (x: Var) (domain body: Expr Var): Expr Var :=
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
  def irsecExpr
    [Inhabited Var]
    (x: Var)
    (domain body: Expr Var)
  :
    Expr Var
  :=
    Expr.arbIr
      x
      (unExpr
        body
        -- "if x is outside the domain, then anyExpr"
        (ifThenExpr (Expr.cpl (irExpr x domain)) (anyExpr)))
  
  -- A union of finitely many expressions.
  def finUnExpr [Inhabited Var]: List (Expr Var) → (Expr Var)
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
  def zthMember
    [Inhabited Var]
    (x: Var)
    (expr: Expr Var)
  :
    Expr Var
  :=
    Expr.arbUn x (ifThenExpr (irExpr (pairExpr x anyExpr) expr) x)
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def fstMember
    [Inhabited Var]
    (x: Var)
    (expr: Expr Var)
  :
    Expr Var
  :=
    Expr.arbUn x (ifThenExpr (irExpr (pairExpr anyExpr x) expr) x)
  
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
  def callExpr
    [Inhabited Var]
    (x: Var)
    (fn arg: Expr Var)
  :
    Expr Var
  :=
    fstMember x (irExpr fn (pairExpr arg anyExpr))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succExpr nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.zero`.)
  -/
  def succExpr (expr: Expr Var): Expr Var := pairExpr expr zeroExpr
  
  def succ (pair: Pair): Pair := Pair.pair pair Pair.zero
  
  instance ofNat n: OfNat Pair n where
    ofNat := Pair.fromNat n
  
  /-
    Given a natural number `n`, `natExpr n` represents
    the encoding of `n` as a pair.
  -/
  def natExpr: Nat → Expr Var
  | Nat.zero => zeroExpr
  | Nat.succ pred => succExpr (natExpr pred)
  
  
  def InsP Var := Ins (Var := Var) pairSalgebra
  def InwP Var := Inw (Var := Var) pairSalgebra
  
  
  def insUnL
    (exprR: Expr Var)
    {exprL: Expr Var}
    (s: InsP Var b c exprL d)
  :
    InsP Var b c (unExpr exprL exprR) d
  :=
    Or.inl s
  
  def inwUnL
    (exprR: Expr Var)
    {exprL: Expr Var}
    (w: InwP Var b c exprL d)
  :
    InwP Var b c (unExpr exprL exprR) d
  :=
    Or.inl w
  
  
  def insUnR
    {exprR: Expr Var}
    (exprL: Expr Var)
    (s: InsP Var b c exprR d)
  :
    InsP Var b c (unExpr exprL exprR) d
  :=
    Or.inr s
  
  def inwUnR
    {exprR: Expr Var}
    (exprL: Expr Var)
    (w: InwP Var b c exprR d)
  :
    InwP Var b c (unExpr exprL exprR) d
  :=
    Or.inr w
  
  
  def insUnElim
    (s: InsP Var b c (unExpr exprL exprR) d)
  :
    Or
      (InsP Var b c exprL d)
      (InsP Var b c exprR d)
  :=
    s
  
  def inwUnElim
    (s: InwP Var b c (unExpr exprL exprR) d)
  :
    Or
      (InwP Var b c exprL d)
      (InwP Var b c exprR d)
  :=
    s
  
  
  def insIr
    (l: InsP Var b c exprL d)
    (r: InsP Var b c exprR d)
  :
    InsP Var b c (irExpr exprL exprR) d
  :=
    ⟨l, r⟩
  
  def inwIr
    (l: InwP Var b c exprL d)
    (r: InwP Var b c exprR d)
  :
    InwP Var b c (irExpr exprL exprR) d
  :=
    ⟨l, r⟩
  
  def insIrElim
    (s: InsP Var b c (irExpr exprL exprR) d)
  :
    And
      (InsP Var b c exprL d)
      (InsP Var b c exprR d)
  :=
    s
  
  def inwIrElim
    (s: InwP Var b c (irExpr exprL exprR) d)
  :
    And
      (InwP Var b c exprL d)
      (InwP Var b c exprR d)
  :=
    s
  
  
  def insIfThen
    {cond: Expr Var}
    (insCond: InsP Var b c cond dC)
    (insBody: InsP Var b c body d)
  :
    InsP Var b c (ifThenExpr cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  def inwIfThen
    {cond: Expr Var}
    (insCond: InwP Var b c cond dC)
    (insBody: InwP Var b c body d)
  :
    InwP Var b c (ifThenExpr cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  
  def insIfThenElim
    {cond: Expr Var}
    (s: InsP Var b c (ifThenExpr cond body) d)
  :
    And
      (∃ dC, InsP Var b c cond dC)
      (InsP Var b c body d)
  :=
    let ⟨exCond, insBody⟩ := s
    
    And.intro exCond insBody
  
  def inwIfThenElim
    {cond: Expr Var}
    (s: InwP Var b c (ifThenExpr cond body) d)
  :
    And
      (∃ dC, InwP Var b c cond dC)
      (InwP Var b c body d)
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
      InsP Var (b.update x dBound) (c.update x dBound) domain dBound)
    (insBody:
      InsP Var (b.update x dBound) (c.update x dBound) body d)
  :
    InsP Var b c (unionExpr x domain body) d
  :=
    let inUpdated: ((c.update x dBound) x).defMem dBound :=
      Valuation.update.inEq.defMem c x dBound
    
    insArbUn _ ⟨⟨dBound, ⟨inUpdated, insDomain⟩⟩, insBody⟩
  
  def inwUnDom
    (inwDomain:
      InwP Var (b.update x dBound) (c.update x dBound) domain dBound)
    (inwBody:
      InwP Var (b.update x dBound) (c.update x dBound) body d)
  :
    InwP Var b c (unionExpr x domain body) d
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
    (b c: Valuation Var Pair)
    (x: Var)
    (dBound: Pair)
    (domain body: Expr Var)
    (d: Pair): Prop
  where
    insDomain:
      InsP Var (b.update x dBound) (c.update x dBound) domain dBound
    insBody: InsP Var (b.update x dBound) (c.update x dBound) body d
  
  def insUnDomElim
    (insUnDom: InsP Var b c (unionExpr x domain body) d)
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
      InsP Var bUpdated cUpdated domain dBound.val
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
    (b c: Valuation Var Pair)
    (x: Var)
    (dBound: Pair)
    (domain body: Expr Var)
    (d: Pair): Prop
  where
    inwDomain:
      InwP Var (b.update x dBound) (c.update x dBound) domain dBound
    inwBody: InwP Var (b.update x dBound) (c.update x dBound) body d
  
  def inwUnDomElim
    (insUnDom: InwP Var b c (unionExpr x domain body) d)
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
      InwP Var bUpdated cUpdated domain dBound.val
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
    [Inhabited Var]
    {list: List (Expr Var)}
    (exprIn: expr ∈ list)
    (s: InsP Var b c expr p)
  :
    InsP Var b c (finUnExpr list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ insUnL _ s)
        (fun inRest => insUnR _ (insFinUn inRest s))
  
  def inwFinUn
    [Inhabited Var]
    {list: List (Expr Var)}
    (exprIn: expr ∈ list)
    (w: InwP Var b c expr p)
  :
    InwP Var b c (finUnExpr list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ inwUnL _ w)
        (fun inRest => inwUnR _ (inwFinUn inRest w))
  
  
  def InsFinUnElim
    (b c: Valuation Var Pair)
    (d: Pair)
    (P: Prop)
  :
    List (Expr Var) → Prop
  | List.nil => P
  | List.cons head tail =>
    (InsP Var b c head d → P) → InsFinUnElim b c d P tail
  
  def InsFinUnElim.ofP
    (list: List (Expr Var))
    (p: P)
  :
    InsFinUnElim b c d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def insFinUnElim
    [Inhabited Var]
    (s: InsP Var b c (finUnExpr list) d)
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
    (b c: Valuation Var Pair)
    (d: Pair)
    (P: Prop)
  :
    List (Expr Var) → Prop
  | List.nil => P
  | List.cons head tail =>
    (InwP Var b c head d → P) → InwFinUnElim b c d P tail
  
  def inwFinUnElim.ofP
    (list: List (Expr Var))
    (p: P)
  :
    InwFinUnElim b c d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def inwFinUnElim
    [Inhabited Var]
    (s: InwP Var b c (finUnExpr list) d)
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
    InsP Var b c zeroExpr Pair.zero
  :=
    rfl
  
  def insZeroElim
    (s: InsP Var b c zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def insZeroElim.neq
    (s: InsP Var b c zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def insZeroElim.nope
    (s: InsP Var b c zeroExpr (Pair.pair pA pB))
  :
    P
  :=
    False.elim (insZeroElim.neq s pA pB rfl)
  
  
  def inwZero:
    InwP Var b c zeroExpr Pair.zero
  :=
    rfl
  
  def inwZeroElim
    (s: InwP Var b c zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def inwZeroElim.neq
    (s: InwP Var b c zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def inwZeroElim.nope
    (s: InwP Var b c zeroExpr (Pair.pair pA pB))
  :
    P
  :=
    False.elim (inwZeroElim.neq s pA pB rfl)
  
  
  def insPair
    (insL: InsP Var b c exprL pairL)
    (insR: InsP Var b c exprR pairR)
  :
    InsP Var b c (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  def inwPair
    (insL: InwP Var b c exprL pairL)
    (insR: InwP Var b c exprR pairR)
  :
    InwP Var b c (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  
  structure InsPairElim
    (b c: Valuation Var Pair)
    (exprL exprR: Expr Var)
    (pairL pairR: Pair): Prop
  where
    insL: InsP Var b c exprL pairL
    insR: InsP Var b c exprR pairR
  
  def insPairElim
    (s: InsP Var b c (pairExpr exprL exprR) (Pair.pair pairL pairR))
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
    (b c: Valuation Var Pair)
    (exprL exprR: Expr Var)
    (p pairL pairR: Pair): Prop
  where
    eq: p = Pair.pair pairL pairR
    insL: InsP Var b c exprL pairL
    insR: InsP Var b c exprR pairR
  
  def insPairElim.ex
    (s: InsP Var b c (pairExpr exprL exprR) p)
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
    (s: InsP Var b c (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex s).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def insPairElim.nope
    (s: InsP Var b c (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero s rfl).elim
  
  
  structure InwPairElim
    (b c: Valuation Var Pair)
    (exprL exprR: Expr Var)
    (pairL pairR: Pair): Prop
  where
    inwL: InwP Var b c exprL pairL
    inwR: InwP Var b c exprR pairR
  
  def inwPairElim
    (w: InwP Var b c (pairExpr exprL exprR) (Pair.pair pairL pairR))
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
    (b c: Valuation Var Pair)
    (exprL exprR: Expr Var)
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: InwP Var b c exprL pairL
    insR: InwP Var b c exprR pairR
  
  def inwPairElim.ex
    (w: InwP Var b c (pairExpr exprL exprR) p)
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
    (w: InwP Var b c (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex w).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inwPairElim.nope
    (w: InwP Var b c (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero w rfl).elim
  
  
  def insZthMember
    [Inhabited Var]
    (s:
      InsP Var (b.update x pA) (c.update x pA) expr (Pair.pair pA pB))
  :
    InsP Var b c (zthMember x expr) pA
  :=
    insArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (insPair insBound insAny) s⟩,
      insBound,
    ⟩
  
  def inwZthMember
    [Inhabited Var]
    (s:
      InwP Var (b.update x pA) (c.update x pA) expr (Pair.pair pA pB))
  :
    InwP Var b c (zthMember x expr) pA
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (inwPair inwBound inwAny) s⟩,
      inwBound,
    ⟩
  
  
  def insFstMember
    [Inhabited Var]
    (s:
      InsP Var (b.update x pB) (c.update x pB) expr (Pair.pair pA pB))
  :
    InsP Var b c (fstMember x expr) pB
  :=
    insArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (insPair insAny insBound) s⟩,
      insBound,
    ⟩
  
  def inwFstMember
    [Inhabited Var]
    (s:
      InwP Var (b.update x pB) (c.update x pB) expr (Pair.pair pA pB))
  :
    InwP Var b c (fstMember x expr) pB
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB,
        And.intro (inwPair inwAny inwBound) s⟩,
      inwBound,
    ⟩
  
  
  def insZthMemberElim
    [Inhabited Var]
    (s: InsP Var b c (zthMember x expr) zth)
  :
    ∃ fst,
      InsP
        Var
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
    [Inhabited Var]
    (s: InwP Var b c (zthMember x expr) zth)
  :
    ∃ fst,
      InwP
        Var
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
    [Inhabited Var]
    (s: InsP Var b c (fstMember x expr) fst)
  :
    ∃ zth,
      InsP
        Var
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
    [Inhabited Var]
    (s: InwP Var b c (fstMember x expr) fst)
  :
    ∃ zth,
      InwP
        Var
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
    [Inhabited Var]
    (insZth: InsP Var b c (zthMember xA (var xB)) zth)
    (insFst: InsP Var b c (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: c xB = Set3.just d)
  :
    InsP Var b c xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, insChosenFst⟩ := insZthMemberElim insZth
    let ⟨chosenZth, insChosenZth⟩ := insFstMemberElim insFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inDefToEqBin
        (d := d)
        (isUnit ▸ (insFreeElim insChosenFst neq))
        (isUnit ▸ (insFreeElim insChosenZth neq))
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ (insFreeElim insChosenZth neq)
  
  def inwZthFstElim
    [Inhabited Var]
    (inwZth: InwP Var b c (zthMember xA (var xB)) zth)
    (inwFst: InwP Var b c (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: c xB = Set3.just d)
  :
    InwP Var b c xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, inwChosenFst⟩ := inwZthMemberElim inwZth
    let ⟨chosenZth, inwChosenZth⟩ := inwFstMemberElim inwFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inPosToEqBin
        (d := d)
        (isUnit ▸ (inwFreeElim inwChosenFst neq))
        (isUnit ▸ (inwFreeElim inwChosenZth neq))
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ (inwFreeElim inwChosenZth neq)
  
  
  def insCallExpr
    [Inhabited Var]
    (insFn:
      InsP Var (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
    (insArg:
      InsP Var (b.update x pB) (c.update x pB) arg pA)
  :
    InsP Var b c (callExpr x fn arg) pB
  :=
    insFstMember (insIr insFn (insPair insArg insAny))
  
  def inwCallExpr
    [Inhabited Var]
    (inwFn:
      InwP Var (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
    (inwArg:
      InwP Var (b.update x pB) (c.update x pB) arg pA)
  :
    InwP Var b c (callExpr x fn arg) pB
  :=
    inwFstMember (inwIr inwFn (inwPair inwArg inwAny))
  
  
  def insCallExprElim
    [Inhabited Var]
    (s: InsP Var b c (callExpr x fn arg) pB)
  :
    ∃ pA,
      And
        (InsP Var (b.update x pB) (c.update x pB) fn (Pair.pair pA pB))
        (InsP Var (b.update x pB) (c.update x pB) arg pA)
  :=
    let ⟨zth, insIr⟩ := insFstMemberElim s
    let ⟨insFn, insP⟩ := insIrElim insIr
    
    ⟨zth, And.intro insFn (insPairElim insP).insL⟩
  
  def inwCallExprElim
    [Inhabited Var]
    (w: InwP Var b c (callExpr x fn arg) bA)
  :
    ∃ pA,
      And
        (InwP Var (b.update x bA) (c.update x bA) fn (Pair.pair pA bA))
        (InwP Var (b.update x bA) (c.update x bA) arg pA)
  :=
    let ⟨zth, inwIr⟩ := inwFstMemberElim w
    let ⟨inwFn, inwP⟩ := inwIrElim inwIr
    
    ⟨zth, And.intro inwFn (inwPairElim inwP).inwL⟩
  
  def insCallElimBound
    [Inhabited Var]
    (s: InsP Var b c (callExpr x fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
    (neq: x ≠ arg)
  :
    InsP Var (b.update x pB) (c.update x pB) fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨insFn, insArg⟩⟩ := insCallExprElim s
    
    let insVArg: (c arg).defMem aAlias := insFreeElim insArg neq
    let eq: aAlias = pA := Set3.just.inDefToEq (isUnit ▸ insVArg)
    
    eq ▸ insFn
  
  def inwCallElimBound
    [Inhabited Var]
    (w: InwP Var b c (callExpr x fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
    (neq: x ≠ arg)
  :
    InwP Var (b.update x pB) (c.update x pB) fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim w
    
    let inwVArg: (c arg).posMem aAlias := inwFreeElim inwArg neq
    let eq: aAlias = pA := Set3.just.inPosToEq (isUnit ▸ inwVArg)
    
    eq ▸ inwFn
  
  
  def insNatExpr b c n
  :
    InsP Var b c (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => insZero
    | Nat.succ pred => insPair (insNatExpr b c pred) insZero
  
  def inwNatExpr b c n
  :
    InwP Var b c (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => inwZero
    | Nat.succ pred => inwPair (inwNatExpr b c pred) inwZero
  
  def inwNatExprElim
    (w: InwP Var b c (natExpr n) p)
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
    (s: InsP Var b c (natExpr n) p)
  :
    p = fromNat n
  :=
    inwNatExprElim s.toInw
  
  def inwNatExprElimNope
    (w: InwP Var b c (natExpr n) (fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    (neq (fromNat.injEq (Eq.symm (inwNatExprElim w)))).elim
  
  def insNatExprElimNope
    (s: InsP Var b c (natExpr n) (fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    inwNatExprElimNope s.toInw neq
  
  def inwNatExprElimDepth
    (w: InwP Var b c (natExpr n) p)
  :
    depth p = n
  :=
    (inwNatExprElim w) ▸ (fromNat.depthEq _)
  
  def insNatExprElimDecode
    (s: InsP Var b c (natExpr n) p)
  :
    depth p = n
  :=
    inwNatExprElimDepth s.toInw
  
end PairExpr
