module
public import Etst.WFC.Ch3_WellFoundedModel
public import Etst.WFC.Utils.Pair
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst

variable
  {E: Type*}
  {x: Nat}
  {p pA pB pC: Pair}
  {fv: List Pair}
  {b c: Valuation Pair}
  {lane: Set3.Lane}


namespace Expr
  exposed def impl (left rite: Expr E) := un left.compl rite
  
  exposed def ifThen (cond body: Expr E): Expr E :=
    ir (some cond) body
  
  exposed def ifElse (cond body: Expr E): Expr E :=
    ir (full cond.compl) body
  
  exposed def ite (cond yes no: Expr E): Expr E :=
    un (ifThen cond yes) (ifElse cond no)
  
  
  /-
    `arbUnDom domain body` is "syntactic sugar" that represents
    an arbitrary union with a domain.
    
    Due to the implementation of `arbUnDom` (and necessarily so),
    `domain` is inside the introduced existential quantifier, meaning
    that the variables of `domain` need to be incremented. In
    particular, `.var 0` should never be used in `domain`.
  -/
  def arbUnDom (domain body: Expr E): Expr E :=
    arbUn (ifThen (ir (.var 0) domain) body)
  
  /-
    `arbIrDom domain body` is "syntactic sugar" that represents
    an arbitrary intersection with a domain.
    
    Due to the implementation of `arbIrDom` (and necessarily so),
    `domain` is inside the introduced universal quantifier, meaning
    that the variables of `domain` need to be incremented. In
    particular, `.var 0` should never be used in `domain`.
  -/
  def arbIrDom (domain body: Expr E): Expr E :=
    arbIr (un body (ifElse (ir (.var 0) domain) any))
  
  -- A union of finitely many expressions.
  def finUn: List (Expr E) → Expr E
  | [] => none
  | [expr] => expr
  | expr :: tail =>
    un expr (finUn tail)
  
  /-
    Let `expr` be an expression that represets a triset of
    pairs `s3` (under some valuation). The expression
    `zth expr` then represents the set of all
    `a` such that `(a, _) ∈ s3`.
    
    `zth` introduces an existential quantifier, the
    variables of `expr` need to be incremented.
  -/
  exposed def zth (expr: Expr E): Expr E :=
    arbUn (ifThen (ir (prod (var 0) any) expr) (var 0))
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fst expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `fst` introduces an existential quantifier, the
    variables of `expr` need to be incremented.
  -/
  exposed def fst (expr: Expr E): Expr E :=
    arbUn (ifThen (ir (prod any (var 0)) expr) (var 0))
  
  /-
    Assumes `expr` codes a triset of n-tuples, (zero-tuple
    being null, n+1-tuple being `(value, n-tuple)`).
  -/
  def nth (n: Nat) (expr: Expr E): Expr E :=
    match n with
    | 0 => zth expr
    | n+1 => nth n (fst expr)
  
  /-
    Let `fn` and `arg` be expressions that represent
    sets of pairs `sFn` and `sArg` (under some valuation).
    The expression `call fn arg` then represents
    the set of all `b` such that there exists an `a`
    such that `(a, b) ∈ sFn` and `a ∈ sArg`.
    
    `sFn` can be viewed as a function that, as a set,
    contains its input-output pairs.
    
    `call` introduces an existential quantifier, the
    variables of `fn` and `arg` need to be incremented.
  -/
  exposed def call (fn arg: Expr E): Expr E :=
    arbUn (ifThen (ir fn (prod arg (var 0))) (var 0))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succ nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.null`.)
  -/
  exposed def succ (expr: Expr E): Expr E := prod expr null
  
  exposed def nat: Nat → Expr E
  | Nat.zero => null
  | Nat.succ pred => succ (nat pred)
  
  /-
    `nonemptify x = null | (x, null)`, guaranteeing nonemptiness,
    and reversibility (with `zth`).
  -/
  def nonemptify {E} (expr: Expr E): Expr E :=
    un null (prod expr null)
  
  def losslessProd (left rite: Expr E): Expr E :=
    prod (nonemptify left) (nonemptify rite)
  
  /-
    The cartesian product `T0 × T1 × ... × Tn` represents the empty
    set if any of the `Ti` are empty, losing information about the
    other non-empty components.
    
    To encode N values completely independently of each other, we can
    represent them as
    
        nonemptify T0 × nonemptify T1 × ... × nonemptify Tn \,.
    
    Usage for `n = 3`:
    
        losslessProdCons expr0
          (losslessProdCons expr1
            (losslessProdCons expr2
              null))
  -/
  def losslessProdCons (head tail: Expr E): Expr E :=
    prod (nonemptify head) tail

  def losslessProdList: List (Expr E) → Expr E
  | [] => null
  | head :: tail => losslessProdCons head (losslessProdList tail)
  
  -- Like `nth`, but works with lossless products.
  def losslessProdAt (n: Nat) (expr: Expr E): Expr E :=
    zth (nth n expr)
end Expr


namespace SingleLaneExpr
  open Expr
  variable {expr exprA exprB domain body: SingleLaneExpr}
  
  theorem inImpl
    -- Note the swapped valuations in the domain.
    (inFn: p ∈ intp2 exprA fv c b → p ∈ intp2 exprB fv b c)
  :
    p ∈ intp2 (impl exprA exprB) fv b c
  :=
    match Classical.em (p ∈ intp2 exprA fv c b) with
    | Or.inl inA => inUnR (inFn inA)
    | Or.inr notInA => inUnL notInA
  
  theorem inImplElim
    (inImpl: p ∈ intp2 (impl exprA exprB) fv b c)
  :
    -- Note the swapped valuations in the domain.
    (p ∈ intp2 exprA fv c b → p ∈ intp2 exprB fv b c)
  :=
    fun inA =>
      (inUnElim inImpl).elim
        (fun inComplA => (inComplElim inComplA inA).elim)
        id
  
  
  theorem inIfThen
    {cond: SingleLaneExpr}
    (inCond: pC ∈ intp2 cond fv b c)
    (inBody: p ∈ intp2 body fv b c)
  :
    p ∈ intp2 (ifThen cond body) fv b c
  :=
    inIr (inSome pC inCond) inBody
  
  theorem inIfThenElim
    {cond: SingleLaneExpr}
    (inIfThen: p ∈ intp2 (ifThen cond body) fv b c)
  :
    And
      (∃ pC, pC ∈ intp2 cond fv b c)
      (p ∈ intp2 body fv b c)
  :=
    let ⟨inCond, inBody⟩ := inIrElim inIfThen
    And.intro (inSomeElim inCond) inBody
  
  
  /-
    This is not a mistake -- the vars of the domain are updated
    too. It's unfortunate, but inevitable -- have a look at the
    implementation of `arbUnDom` to see for yourself.
  -/
  theorem inUnDom {pDom}
    (inDomain: pDom ∈ intp2 domain (pDom :: fv) b c)
    (inBody: p ∈ intp2 body (pDom :: fv) b c)
  :
    p ∈ intp2 (arbUnDom domain body) fv b c
  :=
    inArbUn pDom (inIr (inSome pDom ⟨rfl, inDomain⟩) inBody)
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (Under the condition that any two instances are only
  -- allowed to contain the same instance, if need be).
  -- We have global choice anyway!
  structure InsUnDomElim
    (fv: List Pair)
    (b c: Valuation Pair)
    (x: Nat)
    (pBnd: Pair)
    (domain body: SingleLaneExpr)
    (p: Pair): Prop
  where
    inDomain: pBnd ∈ intp2 domain (pBnd :: fv) b c
    inBody: p ∈ intp2 body (pBnd :: fv) b c
  
  theorem inUnDomElim
    (inUnDom: p ∈ intp2 (arbUnDom domain body) fv b c)
  :
    ∃ pBound, InsUnDomElim fv b c x pBound domain body p
  :=
    let ⟨pBound, inIfThen⟩ := inArbUnElim inUnDom
    let ⟨⟨_pC, inFvDom⟩, inBody⟩ := inIfThenElim inIfThen
    let ⟨inFv, inDom⟩ := inIrElim inFvDom
    let fvEq := inVarElim inFv rfl
    ⟨pBound, { inDomain := fvEq ▸ inDom, inBody }⟩
  
  
  theorem inFinUn
    {list: List SingleLaneExpr}
    (exprIn: expr ∈ list)
    (inExpr: p ∈ intp2 expr fv b c)
  :
    p ∈ intp2 (finUn list) fv b c
  :=
    match list with
    | [_e0] =>
      exprIn.elim
        (fun eq => eq ▸ inExpr)
        (fun inRest => (List.not_mem_nil inRest).elim)
    | List.cons _e0 (_e1 :: _rest) =>
      exprIn.elim
        (fun eq => eq ▸ inUnL inExpr)
        (fun inRest => inUnR (inFinUn inRest inExpr))
  
  /-
    The return type of `inFinUnElim`.
    Like the type of `Or.elim p`, but n-ary instead of binary.
  -/
  exposed def InFinUnElim
    (fv: List Pair)
    (b c: Valuation Pair)
    (p: Pair)
    (P: Prop)
  :
    List SingleLaneExpr → Prop
  | List.nil => P
  | List.cons head tail =>
    (p ∈ intp2 head fv b c → P) → InFinUnElim fv b c p P tail
  
  theorem inFinUnElim {P list}
    (inFinUn: p ∈ intp2 (finUn list) fv b c)
  :
    InFinUnElim fv b c p P list
  :=
    match list with
    | List.nil => False.elim (ninNone inFinUn)
    | [_head] =>
      fun inHeadToP => inHeadToP inFinUn
    | List.cons _head (_e1 :: _tail) =>
      (inUnElim inFinUn).elim
        (fun inHead inHeadToP =>
          let rec ofP (proof: P) l: InFinUnElim fv b c p P l :=
            match l with
            | List.nil => proof
            | List.cons _head tail => fun _ => ofP proof tail
          
          ofP (inHeadToP inHead) _)
        (fun inTail _ => inFinUnElim inTail)
  
  
  
  theorem inZth
    (inExpr: .pair pA pB ∈ intp2 expr (pA :: fv) b c)
  :
    pA ∈ intp2 (zth expr) fv b c
  :=
    inArbUn pA (inIfThen (inIr (inProd rfl inAny) inExpr) rfl)
  
  
  theorem inFst
    (inExpr: .pair pA pB ∈ intp2 expr (pB :: fv) b c)
  :
    pB ∈ intp2 (fst expr) fv b c
  :=
    inArbUn pB (inIfThen (inIr (inProd inAny rfl) inExpr) rfl)
  
  
  theorem inZthElim {p0}
    (inZth: p0 ∈ intp2 (zth expr) fv b c)
  :
    ∃ p1, .pair p0 p1 ∈ intp2 expr (p0 :: fv) b c
  :=
    let ⟨pZth, ⟨inCond, inBody⟩⟩ := inArbUnElim inZth
    let ⟨pCond, ⟨inProdCond, pCondInExpr⟩⟩ := inSomeElim inCond
    
    match pCond with
    | Pair.null => inProdElimNope inProdCond
    | Pair.pair pCondZth pCondFst =>
      let ⟨inL, _insR⟩ := inProdElim inProdCond
      let eqPCondZth: pCondZth = pZth := inVarElim inL rfl
      let eqPZth: p0 = pZth := inVarElim inBody rfl
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInExpr⟩
  
  theorem inFstElim {p1}
    (inFst: p1 ∈ intp2 (fst expr) fv b c)
  :
    ∃ p0, .pair p0 p1 ∈ intp2 expr (p1 :: fv) b c
  :=
    let ⟨pFst, ⟨inCond, inBody⟩⟩ := inArbUnElim inFst
    let ⟨pCond, ⟨inProdCond, pCondInExpr⟩⟩ := inSomeElim inCond
    
    match pCond with
    | Pair.null => inProdElimNope inProdCond
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, inR⟩ := inProdElim inProdCond
      let eqPCondFst: pCondFst = pFst := inVarElim inR rfl
      let eqPFst: p1 = pFst := inVarElim inBody rfl
      ⟨pCondZth, eqPFst ▸ eqPCondFst ▸ pCondInExpr⟩
  
  theorem inZthFstElim {p0 p1}
    (inZth: p0 ∈ intp2 (zth (const lane x)) fv b c)
    (inFst: p1 ∈ intp2 (fst (const lane x)) fv b c)
    (isUnit: c x = Set3.just p)
  :
    .pair p0 p1 ∈ intp2 (Expr.const lane x) fv b c
  :=
    let ⟨fstB, inFstB⟩ := inZthElim inZth
    let ⟨zthB, inZthB⟩ := inFstElim inFst
    
    let eq:
      Pair.pair p0 fstB = Pair.pair zthB p1
    :=
      open Set3.just in
      match lane with
      | .defLane => inDefToEqBin p (isUnit ▸ inFstB) (isUnit ▸ inZthB)
      | .posLane => inPosToEqBin p (isUnit ▸ inFstB) (isUnit ▸ inZthB)
    
    let eqR: p0 = zthB := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ inZthB
  
  
  theorem inCall {fn arg}
    (inFn: .pair pA pB ∈ intp2 fn (pB :: fv) b c)
    (inArg: pA ∈ intp2 arg (pB :: fv) b c)
  :
    pB ∈ intp2 (call fn arg) fv b c
  :=
    inArbUn
      pB
      (inIfThen
        (inIr inFn (inProd inArg (inVar rfl)))
        (inVar rfl))
  
  
  theorem inCallElim {fn arg}
    (inCall: pB ∈ intp2 (call fn arg) fv b c)
  :
    ∃ pA,
      And
        (.pair pA pB ∈ intp2 fn (pB :: fv) b c)
        (pA ∈ intp2 arg (pB :: fv) b c)
  :=
    let ⟨_res, inIfThen⟩ := inArbUnElim inCall
    let ⟨⟨fnP, inFn, inProdFn⟩, inVarRes⟩ := inIfThenElim inIfThen
    let pbEq := inVarElim inVarRes rfl
    match fnP with
    | .null => inProdElimNope inProdFn
    | .pair _fnArg _fnRes =>
      let ⟨inFnArg, inFnRes⟩ := inProdElim inProdFn
      let fnResEq := inVarElim inFnRes rfl
      ⟨_, And.intro (pbEq ▸ fnResEq ▸ inFn) (pbEq ▸ inFnArg)⟩
  
  theorem inCallElimSingle {fn arg}
    (inCall: pB ∈ intp2 (call fn arg) fv b c)
    (isSingleton: intp2 arg (pB :: fv) b c = {pA})
  :
    .pair pA pB ∈ intp2 fn (pB :: fv) b c
  :=
    let ⟨aAlias, ⟨inFn, inArg⟩⟩ := inCallElim inCall
    let eq: aAlias = pA :=
      by rw [isSingleton] at inArg; exact inArg
    eq ▸ inFn
  
  
  theorem inNat {b c}
    (n: Nat)
  :
    .nat n ∈ intp2 (nat n) fv b c
  :=
    match n with
    | Nat.zero => inNull
    | Nat.succ pred => inProd (inNat pred) inNull
  
  theorem inNatElim {n p}
    (inNatExpr: p ∈ intp2 (nat n) fv b c)
  :
    p = Pair.nat n
  :=
    match n, p with
    | Nat.zero, _ => inNullElim inNatExpr ▸ rfl
    | Nat.succ _, .null => inProdElimNope inNatExpr
    | Nat.succ _, .pair _ _ =>
      let ⟨l, r⟩ := inProdElim inNatExpr
      (inNatElim l) ▸ (inNullElim r) ▸ rfl
  
  def inNatElimNope {P n m}
    (inNat: .nat m ∈ intp2 (nat n) fv b c)
    (neq: n ≠ m)
  :
    P
  :=
    (neq (Pair.nat_inj_eq (Eq.symm (inNatElim inNat)))).elim
  
  theorem inNatElimDepth {n p}
    (inNat: p ∈ intp2 (nat n) fv b c)
  :
    p.depth = n
  :=
    (inNatElim inNat) ▸ (Pair.nat_depth_eq n)
  
  theorem inNatElimDecode {n p}
    (inNatExpr: p ∈ intp2 (nat n) fv b c)
  :
    p.depth = n
  :=
    inNatElimDepth inNatExpr
  
  
  theorem inToExpr {lane fv b c}
    (p: Pair)
  :
    p ∈ (p.toExpr.toLane lane).intp2 fv b c
  :=
    match p with
    | .null => inNull
    | .pair l r => inProd (inToExpr l) (inToExpr r)
  
  theorem inToExprElim {lane fv b c}
    {pExpr p: Pair}
    (inExpr: p ∈ (pExpr.toExpr.toLane lane).intp2 fv b c)
  :
    pExpr = p
  :=
    match pExpr, p, inExpr with
    | .null, _, inExpr => (inNullElim inExpr).symm
    | .pair _ _, .pair _ _, inExpr =>
      let ⟨inL, inR⟩ := inProdElim inExpr
      (Pair.eq (inToExprElim inL) (inToExprElim inR))
  
  theorem intp2_toExpr_eq_singleton {lane fv b c}
    (p: Pair)
  :
    intp2 (p.toExpr.toLane lane) fv b c = {p}
  :=
    Set.ext fun _ => Iff.intro
      (fun inExpr => (inToExprElim inExpr).symm)
      (fun eq => eq ▸ inToExpr p)
  
end SingleLaneExpr
