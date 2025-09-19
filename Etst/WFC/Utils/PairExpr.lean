import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Pair
import Etst.WFC.Utils.RulesOfInference

namespace Etst


abbrev PairExpr := Expr pairSignature
abbrev PairDl := DefList pairSignature

noncomputable def PairDl.wfm (dl: PairDl) :=
  DefList.wfm pairSalgebra dl

namespace PairExpr
  open Expr
  
  abbrev intp
    (e: PairExpr)
    (bv: List Pair := [])
    (v: Valuation Pair)
  :
    Set3 Pair
  :=
    e.interpretation pairSalgebra bv v v
  
  abbrev intp2
    (e: PairExpr)
    (bv: List Pair := [])
    (b c: Valuation Pair)
  :
    Set3 Pair
  :=
    e.interpretation pairSalgebra bv b c
  
  def var (x: Nat): PairExpr := Expr.var x
  def bvar (x: Nat): PairExpr := Expr.bvar x
  def cpl (e: PairExpr): PairExpr := Expr.cpl e
  def arbUn (e: PairExpr): PairExpr := Expr.arbUn e
  def arbIr (e: PairExpr): PairExpr := Expr.arbIr e
  
  def null: PairExpr := Expr.op pairSignature.Op.null nofun
  
  def pair (l r: PairExpr): PairExpr :=
    Expr.op pairSignature.Op.pair fun
      | .zth => l
      | .fst => r
  
  def un (l r: PairExpr): PairExpr :=
    Expr.op pairSignature.Op.un fun
      | .zth => l
      | .fst => r
  
  def ir (l r: PairExpr): PairExpr :=
    Expr.op pairSignature.Op.ir fun
      | .zth => l
      | .fst => r
  
  def condSome (e: PairExpr): PairExpr :=
    Expr.op pairSignature.Op.condSome fun _ => e
  
  def condFull (e: PairExpr): PairExpr :=
    Expr.op pairSignature.Op.condFull fun _ => e
  
  
  def ifThen (cond body: PairExpr): PairExpr :=
    ir (condSome cond) body
  
  def ifElse (cond body: PairExpr): PairExpr :=
    ir (condFull cond.cpl) body
  
  def ite (cond yes no: PairExpr): PairExpr :=
    un (ifThen cond yes) (ifElse cond no)
  
  def pairCpl (a b: PairExpr) :=
    un
      null
      (un
        (pair a.cpl any)
        (pair any b.cpl))
  
  
  /-
    `arbUnDom domain body` is "syntactic sugar" that represents
    an arbitrary union with a domain.
    
    Due to the implementation of `arbUnDom` (and necessarily so),
    `domain` is inside the introduced existential quantifier, meaning
    that the bound variables of `domain` need to be incremented. In
    particular, `.bvar 0` should never be used in `domain`.
  -/
  def arbUnDom (domain body: PairExpr): PairExpr :=
    arbUn (ifThen (ir (.bvar 0) domain) body)
  
  /-
    `arbIrDom domain body` is "syntactic sugar" that represents
    an arbitrary intersection with a domain.
    
    Due to the implementation of `arbIrDom` (and necessarily so),
    `domain` is inside the introduced universal quantifier, meaning
    that the bound variables of `domain` need to be incremented. In
    particular, `.bvar 0` should never be used in `domain`.
  -/
  def arbIrDom (domain body: PairExpr): PairExpr :=
    arbIr (un body (ifElse (ir (.bvar 0) domain) any))
  
  -- A union of finitely many expressions.
  def finUn: List PairExpr → PairExpr
  | List.nil => none
  | List.cons expr tail =>
    un expr (finUn (tail))
  
  /-
    Let `expr` be an expression that represets a triset of
    pairs `s3` (under some valuation). The expression
    `zthMember expr` then represents the set of all
    `a` such that `(a, _) ∈ s3`.
    
    `zthMember` introduces an existential quantifier, the
    bound variables of `expr` need to be incremented.
  -/
  def zthMember (expr: PairExpr): PairExpr :=
    arbUn (ifThen (ir (pair (.bvar 0) any) expr) (.bvar 0))
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `fstMember` introduces an existential quantifier, the
    bound variables of `expr` need to be incremented.
  -/
  def fstMember (expr: PairExpr): PairExpr :=
    arbUn (ifThen (ir (pair any (.bvar 0)) expr) (.bvar 0))
  
  /-
    Let `fn` and `arg` be expressions that represent
    sets of pairs `sFn` and `sArg` (under some valuation).
    The expression `call fn arg` then represents
    the set of all `b` such that there exists an `a`
    such that `(a, b) ∈ sFn` and `a ∈ sArg`.
    
    `sFn` can be viewed as a function that, as a set,
    contains its input-output pairs.
    
    `call` introduces an existential quantifier, the
    bound variables of `fn` and `arg` need to be incremented.
  -/
  def call (fn arg: PairExpr): PairExpr :=
    fstMember (ir fn (pair arg any))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succ nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.null`.)
  -/
  def succ (expr: PairExpr): PairExpr := pair expr null
  
  def nat: Nat → PairExpr
  | Nat.zero => null
  | Nat.succ pred => succ (nat pred)
  
  
  def InsP := Ins pairSalgebra
  def InwP := Inw pairSalgebra
  
  
  def insUnL (s: InsP bv b c exprL d):
    InsP bv b c (un exprL exprR) d
  :=
    Or.inl s
  
  def inwUnL (w: InwP bv b c exprL d):
    InwP bv b c (un exprL exprR) d
  :=
    Or.inl w
  
  
  def insUnR (s: InsP bv b c exprR d):
    InsP bv b c (un exprL exprR) d
  :=
    Or.inr s
  
  def inwUnR (w: InwP bv b c exprR d):
    InwP bv b c (un exprL exprR) d
  :=
    Or.inr w
  
  
  def insUnElim
    (s: InsP bv b c (un exprL exprR) d)
  :
    InsP bv b c exprL d ∨ InsP bv b c exprR d
  :=
    s
  
  def inwUnElim
    (s: InwP bv b c (un exprL exprR) d)
  :
    InwP bv b c exprL d ∨ InwP bv b c exprR d
  :=
    s
  
  
  def insIr
    (l: InsP bv b c exprL d)
    (r: InsP bv b c exprR d)
  :
    InsP bv b c (ir exprL exprR) d
  :=
    ⟨l, r⟩
  
  def inwIr
    (l: InwP bv b c exprL d)
    (r: InwP bv b c exprR d)
  :
    InwP bv b c (ir exprL exprR) d
  :=
    ⟨l, r⟩
  
  def insIrElim
    (s: InsP bv b c (ir exprL exprR) d)
  :
    And
      (InsP bv b c exprL d)
      (InsP bv b c exprR d)
  :=
    s
  
  def inwIrElim
    (s: InwP bv b c (ir exprL exprR) d)
  :
    And
      (InwP bv b c exprL d)
      (InwP bv b c exprR d)
  :=
    s
  
  
  def insCondSome
    (insExpr: InsP bv b c expr dE)
    (d: Pair)
  :
    InsP bv b c (condSome expr) d
  :=
    ⟨dE, insExpr⟩
  
  def inwCondSome
    (insExpr: InwP bv b c expr dE)
    (d: Pair)
  :
    InwP bv b c (condSome expr) d
  :=
    ⟨dE, insExpr⟩
  
  
  def insCondSomeElim
    (s: InsP bv b c (condSome expr) d)
  :
    ∃ dE, InsP bv b c expr dE
  :=
    let ⟨dE, insExpr⟩ := s
    ⟨dE, insExpr⟩
  
  def inwCondSomeElim
    (s: InwP bv b c (condSome expr) d)
  :
    ∃ dE, InwP bv b c expr dE
  :=
    s
  
  
  def insCondFull
    (allInsExpr: (dE: pairSalgebra.D) → InsP bv b c expr dE)
    (d: Pair)
  :
    InsP bv b c (condFull expr) d
  :=
    allInsExpr
  
  def inwCondFull
    (allInwExpr: (dE: pairSalgebra.D) → InwP bv b c expr dE)
    (d: Pair)
  :
    InwP bv b c (condFull expr) d
  :=
    allInwExpr
  
  
  def insCondFullElim
    (s: InsP bv b c (condFull expr) d)
  :
    ∀ dE, InsP bv b c expr dE
  :=
    s
  
  def inwCondFullElim
    (s: InwP bv b c (condFull expr) d)
  :
    ∀ dE, InwP bv b c expr dE
  :=
    s
  
  
  def insIfThen
    {cond: PairExpr}
    (insCond: InsP bv b c cond dC)
    (insBody: InsP bv b c body d)
  :
    InsP bv b c (ifThen cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  def inwIfThen
    {cond: PairExpr}
    (insCond: InwP bv b c cond dC)
    (insBody: InwP bv b c body d)
  :
    InwP bv b c (ifThen cond body) d
  :=
    ⟨⟨dC, insCond⟩, insBody⟩
  
  
  def insIfThenElim
    {cond: PairExpr}
    (s: InsP bv b c (ifThen cond body) d)
  :
    And
      (∃ dC, InsP bv b c cond dC)
      (InsP bv b c body d)
  :=
    let ⟨exCond, insBody⟩ := s
    
    And.intro exCond insBody
  
  def inwIfThenElim
    {cond: PairExpr}
    (s: InwP bv b c (ifThen cond body) d)
  :
    And
      (∃ dC, InwP bv b c cond dC)
      (InwP bv b c body d)
  :=
    s
  
  
  /-
    This is not a mistake -- the bound vars of the domain are updated
    too. It's unfortunate, but inevitable -- have a look at the
    implementation of `arbUnDom` to see for yourself.
  -/
  def insUnDom
    (insDomain:
      InsP (dB :: bv) b c domain dB)
    (insBody:
      InsP (dB :: bv) b c body d)
  :
    InsP bv b c (arbUnDom domain body) d
  :=
    -- let inUpdated: ((c.update x dBound) x).defMem dBound :=
    --   Valuation.in_update_bound_defMem rfl
    
    insArbUn dB ⟨⟨dB, ⟨rfl, insDomain⟩⟩, insBody⟩
  
  def inwUnDom
    (inwDomain:
      InwP (dB :: bv) b c domain dB)
    (inwBody:
      InwP (dB :: bv) b c body d)
  :
    InwP bv b c (arbUnDom domain body) d
  :=
    inwArbUn dB ⟨⟨dB, ⟨rfl, inwDomain⟩⟩, inwBody⟩
  
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (Under the condition that any two instances are only
  -- allowed to contain the same instance, if need be).
  -- We have global choice anyway!
  structure InsUnDomElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (x: Nat)
    (dB: Pair)
    (domain body: PairExpr)
    (d: Pair): Prop
  where
    insDomain: InsP (dB :: bv) b c domain dB
    insBody: InsP (dB :: bv) b c body d
  
  def insUnDomElim
    (insUnDom: InsP bv b c (arbUnDom domain body) d)
  :
    ∃ dBound, InsUnDomElim bv b c x dBound domain body d
  :=
    let ⟨dBound, ⟨_, dInIr⟩, insBody⟩ := insUnDom.unwrap
    let dEq := insBoundElim dInIr.left rfl
    let insDomain := dEq ▸ dInIr.right
    ⟨dBound, { insDomain, insBody }⟩
  
  structure InwUnDomElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (dB: Pair)
    (domain body: PairExpr)
    (d: Pair): Prop
  where
    inwDomain: InwP (dB :: bv) b c domain dB
    inwBody: InwP (dB :: bv) b c body d
  
  def inwUnDomElim
    (inwUnDom: InwP bv b c (arbUnDom domain body) d)
  :
    ∃ dBound, InwUnDomElim bv b c dBound domain body d
  :=
    let ⟨dBound, ⟨dBoundAlias, dInIr⟩, inwBody⟩ := inwUnDom.unwrap
    let dEq: dBoundAlias = dBound := inwBoundElim dInIr.left rfl
    let inwDomain := dEq ▸ dInIr.right
    ⟨dBound, { inwDomain, inwBody }⟩
  
  
  def insFinUn
    {list: List PairExpr}
    (exprIn: expr ∈ list)
    (s: InsP bv b c expr p)
  :
    InsP bv b c (finUn list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ insUnL s)
        (fun inRest => insUnR (insFinUn inRest s))
  
  def inwFinUn
    {list: List PairExpr}
    (exprIn: expr ∈ list)
    (w: InwP bv b c expr p)
  :
    InwP bv b c (finUn list) p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ inwUnL w)
        (fun inRest => inwUnR (inwFinUn inRest w))
  
  
  def InsFinUnElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (d: Pair)
    (P: Prop)
  :
    List PairExpr → Prop
  | List.nil => P
  | List.cons head tail =>
    (InsP bv b c head d → P) → InsFinUnElim bv b c d P tail
  
  def insFinUnElim
    (s: InsP bv b c (finUn list) d)
  :
    InsFinUnElim bv b c d P list
  :=
    match list with
    | List.nil => False.elim (ninsNone s)
    | List.cons _head tail =>
      (insUnElim s).elim
        (fun insHead insHeadToP =>
          let rec ofP (p: P) l: InsFinUnElim bv b c d P l :=
            match l with
            | List.nil => p
            | List.cons _head tail => fun _ => ofP p tail
          
          ofP (insHeadToP insHead) tail)
        (fun insTail _ => insFinUnElim insTail)
  
  
  def InwFinUnElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (d: Pair)
    (P: Prop)
  :
    List PairExpr → Prop
  | List.nil => P
  | List.cons head tail =>
    (InwP bv b c head d → P) → InwFinUnElim bv b c d P tail
  
  def inwFinUnElim
    (s: InwP bv b c (finUn list) d)
  :
    InwFinUnElim bv b c d P list
  :=
    match list with
    | List.nil => False.elim (ninwNone s)
    | List.cons _head tail =>
      (inwUnElim s).elim
        (fun inwHead insHeadToP =>
          let rec ofP (p: P) l: InwFinUnElim bv b c d P l :=
            match l with
            | List.nil => p
            | List.cons _head tail => fun _ => ofP p tail
          
          ofP (insHeadToP inwHead) tail)
        (fun insTail _ => inwFinUnElim insTail)
  
  
  def insNull:
    InsP bv b c null Pair.null
  :=
    rfl
  
  def insNullElim
    (s: InsP bv b c null p)
  :
    p = Pair.null
  :=
    s
  
  def insNullElim.neq
    (s: InsP bv b c null p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def insNullElim.nope
    (s: InsP bv b c null (Pair.pair pA pB))
  :
    P
  :=
    False.elim (insNullElim.neq s pA pB rfl)
  
  
  def inwNull:
    InwP bv b c null Pair.null
  :=
    rfl
  
  def inwNullElim
    (s: InwP bv b c null p)
  :
    p = Pair.null
  :=
    s
  
  def inwNullElim.neq
    (s: InwP bv b c null p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def inwNullElim.nope
    (s: InwP bv b c null (Pair.pair pA pB))
  :
    P
  :=
    False.elim (inwNullElim.neq s pA pB rfl)
  
  
  def insPair
    (insL: InsP bv b c exprL pairL)
    (insR: InsP bv b c exprR pairR)
  :
    InsP bv b c (pair exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  def inwPair
    (insL: InwP bv b c exprL pairL)
    (insR: InwP bv b c exprR pairR)
  :
    InwP bv b c (pair exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  
  structure InsPairElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: PairExpr)
    (pairL pairR: Pair): Prop
  where
    insL: InsP bv b c exprL pairL
    insR: InsP bv b c exprR pairR
  
  def insPairElim
    (s: InsP bv b c (pair exprL exprR) (Pair.pair pairL pairR))
  :
    InsPairElim bv b c exprL exprR pairL pairR
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
  
  structure InsPairElimEx
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: PairExpr)
    (p pairL pairR: Pair): Prop
  where
    eq: p = Pair.pair pairL pairR
    insL: InsP bv b c exprL pairL
    insR: InsP bv b c exprR pairR
  
  def insPairElim.ex
    (s: InsP bv b c (pair exprL exprR) p)
  :
    ∃ pairL pairR: Pair,
      InsPairElimEx bv b c exprL exprR p pairL pairR
  :=
    match p with
    | Pair.null =>
      Pair.noConfusion (s.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        __ := insPairElim s
        eq := rfl
      }⟩
  
  def insPairElim.notZero
    (s: InsP bv b c (pair exprL exprR) p)
  :
    p ≠ Pair.null
  :=
    let ⟨_pairL, prop⟩ := (ex s).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def insPairElim.nope
    (s: InsP bv b c (pair exprL exprR) Pair.null)
  :
    P
  :=
    (notZero s rfl).elim
  
  
  structure InwPairElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: PairExpr)
    (pairL pairR: Pair): Prop
  where
    inwL: InwP bv b c exprL pairL
    inwR: InwP bv b c exprR pairR
  
  def inwPairElim
    (w: InwP bv b c (pair exprL exprR) (Pair.pair pairL pairR))
  :
    InwPairElim bv b c exprL exprR pairL pairR
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
  
  structure InwPairElimEx
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: PairExpr)
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    inwL: InwP bv b c exprL pairL
    inwR: InwP bv b c exprR pairR
  
  def inwPairElim.ex
    (w: InwP bv b c (pair exprL exprR) p)
  :
    ∃ pairL pairR: Pair,
      InwPairElimEx bv b c exprL exprR p pairL pairR
  :=
    match p with
    | Pair.null =>
      Pair.noConfusion (w.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        __ := inwPairElim w
        eq := rfl
      }⟩
  
  def inwPairElim.notZero
    (w: InwP bv b c (pair exprL exprR) p)
  :
    p ≠ Pair.null
  :=
    let ⟨_pairL, prop⟩ := (ex w).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inwPairElim.nope
    (w: InwP bv b c (pair exprL exprR) Pair.null)
  :
    P
  :=
    (notZero w rfl).elim
  
  
  def insZthMember
    (s: InsP (pA :: bv) b c expr (Pair.pair pA pB))
  :
    InsP bv b c (zthMember expr) pA
  :=
    insArbUn pA ⟨
      ⟨Pair.pair pA pB, (insPair rfl insAny), s⟩,
      rfl,
    ⟩
  
  def inwZthMember
    (s: InwP (pA :: bv) b c expr (Pair.pair pA pB))
  :
    InwP bv b c (zthMember expr) pA
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB, (inwPair rfl inwAny), s⟩,
      rfl,
    ⟩
  
  
  def insFstMember
    (s: InsP (pB :: bv) b c expr (Pair.pair pA pB))
  :
    InsP bv b c (fstMember expr) pB
  :=
    insArbUn _ ⟨
      ⟨Pair.pair pA pB, (insPair insAny rfl), s⟩,
      rfl,
    ⟩
  
  def inwFstMember
    (s: InwP (pB :: bv) b c expr (Pair.pair pA pB))
  :
    InwP bv b c (fstMember expr) pB
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair pA pB, (inwPair inwAny rfl), s⟩,
      rfl,
    ⟩
  
  
  def insZthMemberElim
    (s: InsP bv b c (zthMember expr) zth)
  :
    ∃ fst,
      InsP
        (zth :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairXaAny, pCondInsExpr⟩⟩ := insCond
    
    match pCond with
    | Pair.null => insPairElim.nope insPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := insPairElim insPairXaAny
      let eqPCondZth: pCondZth = pZth := insBoundElim insL rfl
      let eqPZth: zth = pZth := insBoundElim insBody rfl
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inwZthMemberElim
    (s: InwP bv b c (zthMember expr) zth)
  :
    ∃ fst,
      InwP
        (zth :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairXaAny, pCondInwExpr⟩⟩ := inwCond
    
    match pCond with
    | Pair.null => inwPairElim.nope inwPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := inwPairElim inwPairXaAny
      let eqPCondZth: pCondZth = pZth := inwBoundElim insL rfl
      let eqPZth: zth = pZth := inwBoundElim inwBody rfl
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInwExpr⟩
  
  def insFstMemberElim
    (s: InsP bv b c (fstMember expr) fst)
  :
    ∃ zth,
      InsP
        (fst :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairAnyXa, pCondInsExpr⟩⟩ := insCond
    
    match pCond with
    | Pair.null => insPairElim.nope insPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := insPairElim insPairAnyXa
      let eqPCondZth: pCondFst = pFst := insBoundElim insR rfl
      let eqPZth: fst = pFst := insBoundElim insBody rfl
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inwFstMemberElim
    (s: InwP bv b c (fstMember expr) fst)
  :
    ∃ zth,
      InwP
        (fst :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairAnyXa, pCondInwExpr⟩⟩ := inwCond
    
    match pCond with
    | Pair.null => inwPairElim.nope inwPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := inwPairElim inwPairAnyXa
      let eqPCondZth: pCondFst = pFst := inwBoundElim insR rfl
      let eqPZth: fst = pFst := inwBoundElim inwBody rfl
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ pCondInwExpr⟩
  
  
  def insZthFstElim
    (insZth: InsP bv b c (zthMember (var x)) zth)
    (insFst: InsP bv b c (fstMember (var x)) fst)
    (isUnit: c x = Set3.just d)
  :
    InsP bv b c (var x) (Pair.pair zth fst)
  :=
    let ⟨chosenFst, insChosenFst⟩ := insZthMemberElim insZth
    let ⟨chosenZth, insChosenZth⟩ := insFstMemberElim insFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inDefToEqBin d
        (isUnit ▸ insChosenFst)
        (isUnit ▸ insChosenZth)
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ insChosenZth
  
  def inwZthFstElim
    (inwZth: InwP bv b c (zthMember (var x)) zth)
    (inwFst: InwP bv b c (fstMember (var x)) fst)
    (isUnit: c x = Set3.just d)
  :
    InwP bv b c (var x) (Pair.pair zth fst)
  :=
    let ⟨chosenFst, inwChosenFst⟩ := inwZthMemberElim inwZth
    let ⟨chosenZth, inwChosenZth⟩ := inwFstMemberElim inwFst
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inPosToEqBin d
        (isUnit ▸ inwChosenFst)
        (isUnit ▸ inwChosenZth)
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ inwChosenZth
  
  
  def insCall
    (insFn: InsP (pB :: bv) b c fn (Pair.pair pA pB))
    (insArg: InsP (pB :: bv) b c arg pA)
  :
    InsP bv b c (call fn arg) pB
  :=
    insFstMember (insIr insFn (insPair insArg insAny))
  
  def inwCall
    (inwFn: InwP (pB :: bv) b c fn (Pair.pair pA pB))
    (inwArg: InwP (pB :: bv) b c arg pA)
  :
    InwP bv b c (call fn arg) pB
  :=
    inwFstMember (inwIr inwFn (inwPair inwArg inwAny))
  
  
  def insCallElim
    (s: InsP bv b c (call fn arg) pB)
  :
    ∃ pA,
      And
        (InsP (pB :: bv) b c fn (Pair.pair pA pB))
        (InsP (pB :: bv) b c arg pA)
  :=
    let ⟨zth, insIr⟩ := insFstMemberElim s
    let ⟨insFn, insP⟩ := insIrElim insIr
    
    ⟨zth, And.intro insFn (insPairElim insP).insL⟩
  
  def inwCallElim
    (w: InwP bv b c (call fn arg) pB)
  :
    ∃ pA,
      And
        (InwP (pB :: bv) b c fn (Pair.pair pA pB))
        (InwP (pB :: bv) b c arg pA)
  :=
    let ⟨zth, inwIr⟩ := inwFstMemberElim w
    let ⟨inwFn, inwP⟩ := inwIrElim inwIr
    
    ⟨zth, And.intro inwFn (inwPairElim inwP).inwL⟩
  
  def insCallElimBound
    (s: InsP bv b c (call fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
  :
    InsP (pB :: bv) b c fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨insFn, insArg⟩⟩ := insCallElim s
    let eq: aAlias = pA := Set3.just.inDefToEq (isUnit ▸ insArg)
    eq ▸ insFn
  
  def inwCallElimBound
    (w: InwP bv b c (call fn (var arg)) pB)
    (isUnit: c arg = Set3.just pA)
  :
    InwP (pB :: bv) b c fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨inwFn, inwArg⟩⟩ := inwCallElim w
    let eq: aAlias = pA := Set3.just.inPosToEq (isUnit ▸ inwArg)
    eq ▸ inwFn
  
  
  def insNatExpr b c n
  :
    InsP bv b c (nat n) (Pair.fromNat n)
  :=
    match n with
    | Nat.zero => insNull
    | Nat.succ pred => insPair (insNatExpr b c pred) insNull
  
  def inwNatExpr b c n
  :
    InwP bv b c (nat n) (Pair.fromNat n)
  :=
    match n with
    | Nat.zero => inwNull
    | Nat.succ pred => inwPair (inwNatExpr b c pred) inwNull
  
  def inwNatExprElim
    (w: InwP bv b c (nat n) p)
  :
    p = Pair.fromNat n
  :=
    match n, p with
    | Nat.zero, _ => inwNullElim w ▸ rfl
    | Nat.succ _, .null => inwPairElim.nope w
    | Nat.succ _, .pair _ _ =>
      let ⟨l, r⟩ := inwPairElim w
      (inwNatExprElim l) ▸ (inwNullElim r) ▸ rfl
  
  def insNatExprElim
    (s: InsP bv b c (nat n) p)
  :
    p = .fromNat n
  :=
    inwNatExprElim s.toInw
  
  def inwNatExprElimNope
    (w: InwP bv b c (nat n) (.fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    (neq (Pair.fromNat_inj_eq (Eq.symm (inwNatExprElim w)))).elim
  
  def insNatExprElimNope
    (s: InsP bv b c (nat n) (Pair.fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    inwNatExprElimNope s.toInw neq
  
  def inwNatExprElimDepth
    (w: InwP bv b c (nat n) p)
  :
    p.depth = n
  :=
    (inwNatExprElim w) ▸ (Pair.fromNat_depth_eq n)
  
  def insNatExprElimDecode
    (s: InsP bv b c (nat n) p)
  :
    p.depth = n
  :=
    inwNatExprElimDepth s.toInw
  
end PairExpr
