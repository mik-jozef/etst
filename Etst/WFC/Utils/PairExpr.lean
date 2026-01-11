import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Pair
import Etst.WFC.Utils.RulesOfInference

namespace Etst


namespace Expr
  def impl (left rite: Expr E) := un left.compl rite
  
  def ifThen (cond body: Expr E): Expr E :=
    ir (condSome cond) body
  
  def ifElse (cond body: Expr E): Expr E :=
    ir (condFull cond.compl) body
  
  def ite (cond yes no: Expr E): Expr E :=
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
  | List.nil => none
  | List.cons expr tail =>
    un expr (finUn (tail))
  
  /-
    Let `expr` be an expression that represets a triset of
    pairs `s3` (under some valuation). The expression
    `zthMember expr` then represents the set of all
    `a` such that `(a, _) ∈ s3`.
    
    `zthMember` introduces an existential quantifier, the
    variables of `expr` need to be incremented.
  -/
  def zthMember (expr: Expr E): Expr E :=
    arbUn (ifThen (ir (pair (.var 0) any) expr) (.var 0))
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `fstMember` introduces an existential quantifier, the
    variables of `expr` need to be incremented.
  -/
  def fstMember (expr: Expr E): Expr E :=
    arbUn (ifThen (ir (pair any (.var 0)) expr) (.var 0))
  
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
  def call (fn arg: Expr E): Expr E :=
    fstMember (ir fn (pair arg any))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succ nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.null`.)
  -/
  def succ (expr: Expr E): Expr E := pair expr null
  
  def nat: Nat → Expr E
  | Nat.zero => null
  | Nat.succ pred => succ (nat pred)
end Expr


namespace SingleLaneExpr
  open Expr
  
  def inImpl
    -- Note the swapped valuations in the domain.
    (inFn: intp2 exprA bv c b d → intp2 exprB bv b c d)
  :
    intp2 (impl exprA exprB) bv b c d
  :=
    match Classical.em (intp2 exprA bv c b d) with
    | Or.inl inA => inUnR (inFn inA)
    | Or.inr notInA => inUnL notInA
  
  def inImplElim
    (inImpl: intp2 (impl exprA exprB) bv b c d)
  :
    -- Note the swapped valuations in the domain.
    (intp2 exprA bv c b d → intp2 exprB bv b c d)
  :=
    fun inA =>
      (inUnElim inImpl).elim
        (fun inComplA => (inComplElim inComplA inA).elim)
        id
  
  
  def inIfThen
    {cond: SingleLaneExpr}
    (inCond: intp2 cond bv b c dC)
    (inBody: intp2 body bv b c d)
  :
    intp2 (ifThen cond body) bv b c d
  :=
    inIr (inCondSome dC inCond) inBody
  
  def inIfThenElim
    {cond: SingleLaneExpr}
    (inIfThen: intp2 (ifThen cond body) bv b c d)
  :
    And
      (∃ dC, intp2 cond bv b c dC)
      (intp2 body bv b c d)
  :=
    let ⟨inCond, inBody⟩ := inIrElim inIfThen
    And.intro (inCondSomeElim inCond) inBody
  
  
  /-
    This is not a mistake -- the vars of the domain are updated
    too. It's unfortunate, but inevitable -- have a look at the
    implementation of `arbUnDom` to see for yourself.
  -/
  def inUnDom
    (inDomain:
      intp2 domain (dB :: bv) b c dB)
    (inBody:
      intp2 body (dB :: bv) b c d)
  :
    intp2 (arbUnDom domain body) bv b c d
  :=
    inArbUn dB (inIr (inCondSome dB ⟨rfl, inDomain⟩) inBody)
  
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
    (domain body: SingleLaneExpr)
    (d: Pair): Prop
  where
    inDomain: intp2 domain (dB :: bv) b c dB
    inBody: intp2 body (dB :: bv) b c d
  
  def inUnDomElim
    (inUnDom: intp2 (arbUnDom domain body) bv b c d)
  :
    ∃ dBound, InsUnDomElim bv b c x dBound domain body d
  :=
    let ⟨dBound, inIfThen⟩ := inArbUnElim inUnDom
    let ⟨⟨_dC, inBvDom⟩, inBody⟩ := inIfThenElim inIfThen
    let ⟨inBv, inDom⟩ := inIrElim inBvDom
    let bvEq := inVarElim inBv rfl
    ⟨dBound, { inDomain := bvEq ▸ inDom, inBody }⟩
  
  
  def inFinUn
    {list: List SingleLaneExpr}
    (exprIn: expr ∈ list)
    (inExpr: intp2 expr bv b c p)
  :
    intp2 (finUn list) bv b c p
  :=
    match list with
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ inUnL inExpr)
        (fun inRest => inUnR (inFinUn inRest inExpr))
  
  def InFinUnElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (d: Pair)
    (P: Prop)
  :
    List SingleLaneExpr → Prop
  | List.nil => P
  | List.cons head tail =>
    (intp2 head bv b c d → P) → InFinUnElim bv b c d P tail
  
  def inFinUnElim
    (inFinUn: intp2 (finUn list) bv b c d)
  :
    InFinUnElim bv b c d P list
  :=
    match list with
    | List.nil => False.elim (ninNone inFinUn)
    | List.cons _head tail =>
      (inUnElim inFinUn).elim
        (fun inHead inHeadToP =>
          let rec ofP (p: P) l: InFinUnElim bv b c d P l :=
            match l with
            | List.nil => p
            | List.cons _head tail => fun _ => ofP p tail
          
          ofP (inHeadToP inHead) tail)
        (fun inTail _ => inFinUnElim inTail)
  
  
  
  def inZthMember
    (inExpr: intp2 expr (pA :: bv) b c (Pair.pair pA pB))
  :
    intp2 (zthMember expr) bv b c pA
  :=
    inArbUn pA (inIfThen (inIr (inPair rfl inAny) inExpr) rfl)
  
  
  def inFstMember
    (inExpr: intp2 expr (pB :: bv) b c (Pair.pair pA pB))
  :
    intp2 (fstMember expr) bv b c pB
  :=
    inArbUn pB (inIfThen (inIr (inPair inAny rfl) inExpr) rfl)
  
  
  def inZthMemberElim
    (inZthMember: intp2 (zthMember expr) bv b c zth)
  :
    ∃ fst, intp2 expr (zth :: bv) b c (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨inCond, inBody⟩⟩ := inArbUnElim inZthMember
    let ⟨pCond, ⟨inPair, pCondInExpr⟩⟩ := inCondSomeElim inCond
    
    match pCond with
    | Pair.null => inPairElimNope inPair
    | Pair.pair pCondZth pCondFst =>
      let ⟨inL, _insR⟩ := inPairElim inPair
      let eqPCondZth: pCondZth = pZth := inVarElim inL rfl
      let eqPZth: zth = pZth := inVarElim inBody rfl
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInExpr⟩
  
  def inFstMemberElim
    (inFstMember: intp2 (fstMember expr) bv b c fst)
  :
    ∃ zth, intp2 expr (fst :: bv) b c (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨inCond, inBody⟩⟩ := inArbUnElim inFstMember
    let ⟨pCond, ⟨inPair, pCondInExpr⟩⟩ := inCondSomeElim inCond
    
    match pCond with
    | Pair.null => inPairElimNope inPair
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, inR⟩ := inPairElim inPair
      let eqPCondFst: pCondFst = pFst := inVarElim inR rfl
      let eqPFst: fst = pFst := inVarElim inBody rfl
      ⟨pCondZth, eqPFst ▸ eqPCondFst ▸ pCondInExpr⟩
  
  def inZthFstElim
    (inZth: intp2 (zthMember (Expr.const lane x)) bv b c zth)
    (inFst: intp2 (fstMember (Expr.const lane x)) bv b c fst)
    (isUnit: c x = Set3.just d)
  :
    intp2 (Expr.const lane x) bv b c (Pair.pair zth fst)
  :=
    let ⟨fstB, inFstB⟩ := inZthMemberElim inZth
    let ⟨zthB, inZthB⟩ := inFstMemberElim inFst
    
    let eq:
      Pair.pair zth fstB = Pair.pair zthB fst
    :=
      open Set3.just in
      match lane with
      | .defLane => inDefToEqBin d (isUnit ▸ inFstB) (isUnit ▸ inZthB)
      | .posLane => inPosToEqBin d (isUnit ▸ inFstB) (isUnit ▸ inZthB)
    
    let eqR: zth = zthB := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ inZthB
  
  
  def inCall
    (inFn: intp2 fn (pB :: bv) b c (Pair.pair pA pB))
    (inArg: intp2 arg (pB :: bv) b c pA)
  :
    intp2 (call fn arg) bv b c pB
  :=
    inFstMember (inIr inFn (inPair inArg inAny))
  
  
  def inCallElim
    (inCall: intp2 (call fn arg) bv b c pB)
  :
    ∃ pA,
      And
        (intp2 fn (pB :: bv) b c (Pair.pair pA pB))
        (intp2 arg (pB :: bv) b c pA)
  :=
    let ⟨zth, inIr⟩ := inFstMemberElim inCall
    let ⟨inFn, inP⟩ := inIrElim inIr
    
    ⟨zth, And.intro inFn (inPairElim inP).left⟩
  
  def inCallElimBound
    (inCall: intp2 (call fn (Expr.const lane arg)) bv b c pB)
    (isUnit: c arg = Set3.just pA)
  :
    intp2 fn (pB :: bv) b c (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨inFn, inArg⟩⟩ := inCallElim inCall
    let eq: aAlias = pA :=
      match lane with
      | .defLane => Set3.just.inDefToEq (isUnit ▸ inArg)
      | .posLane => Set3.just.inPosToEq (isUnit ▸ inArg)
    eq ▸ inFn
  
  
  def inNat b c n
  :
    intp2 (nat n) bv b c (Pair.fromNat n)
  :=
    match n with
    | Nat.zero => inNull
    | Nat.succ pred => inPair (inNat b c pred) inNull
  
  def inNatElim
    (inNatExpr: intp2 (nat n) bv b c p)
  :
    p = Pair.fromNat n
  :=
    match n, p with
    | Nat.zero, _ => inNullElim inNatExpr ▸ rfl
    | Nat.succ _, .null => inPairElimNope inNatExpr
    | Nat.succ _, .pair _ _ =>
      let ⟨l, r⟩ := inPairElim inNatExpr
      (inNatElim l) ▸ (inNullElim r) ▸ rfl
  
  def inNatElimNope
    (inNat: intp2 (nat n) bv b c (.fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    (neq (Pair.fromNat_inj_eq (Eq.symm (inNatElim inNat)))).elim
  
  def inNatElimDepth
    (inNat: intp2 (nat n) bv b c p)
  :
    p.depth = n
  :=
    (inNatElim inNat) ▸ (Pair.fromNat_depth_eq n)
  
  def inNatElimDecode
    (inNatExpr: intp2 (nat n) bv b c p)
  :
    p.depth = n
  :=
    inNatElimDepth inNatExpr
  
end SingleLaneExpr
