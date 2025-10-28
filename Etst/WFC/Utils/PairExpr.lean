import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Pair
import Etst.WFC.Utils.RulesOfInference

namespace Etst


abbrev PairExpr E := Expr E pairSignature
abbrev BasicPairExpr := BasicExpr pairSignature
abbrev SingleLanePairExpr := SingleLaneExpr pairSignature
abbrev PairDl := DefList pairSignature

noncomputable def PairDl.wfm (dl: PairDl) :=
  DefList.wfm pairSalgebra dl

namespace BasicExpr
  abbrev triIntp2
    (expr: BasicPairExpr)
    (bv: List Pair := [])
    (b c: Valuation Pair)
  :
    Set3 Pair
  :=
    expr.interpretation pairSalgebra bv b c
  
  abbrev triIntp
    (expr: BasicPairExpr)
    (bv: List Pair := [])
    (v: Valuation Pair)
  :
    Set3 Pair
  :=
    triIntp2 expr bv v v
end BasicExpr

namespace SingleLaneExpr
  abbrev intp2
    (expr: SingleLanePairExpr)
    (bv: List Pair := [])
    (b c: Valuation Pair)
  :
    Set Pair
  :=
    expr.interpretation pairSalgebra bv b c
  
  abbrev intp
    (expr: SingleLanePairExpr)
    (bv: List Pair := [])
    (v: Valuation Pair)
  :
    Set Pair
  :=
    intp2 expr bv v v
  
end SingleLaneExpr

namespace PairExpr
  open Expr
  open SingleLaneExpr
  
  
  def null: PairExpr E := Expr.op pairSignature.Op.null nofun
  
  def pair (l r: PairExpr E): PairExpr E :=
    Expr.op pairSignature.Op.pair fun
      | .zth => l
      | .fst => r
  
  def un (l r: PairExpr E): PairExpr E :=
    Expr.op pairSignature.Op.un fun
      | .zth => l
      | .fst => r
  
  def ir (l r: PairExpr E): PairExpr E :=
    Expr.op pairSignature.Op.ir fun
      | .zth => l
      | .fst => r
  
  def condSome (body: PairExpr E): PairExpr E :=
    Expr.op pairSignature.Op.condSome fun _ => body

  def condFull (body: PairExpr E): PairExpr E :=
    Expr.op pairSignature.Op.condFull fun _ => body

  
  def ifThen (cond body: PairExpr E): PairExpr E :=
    ir (condSome cond) body
  
  def ifElse (cond body: PairExpr E): PairExpr E :=
    ir (condFull cond.compl) body
  
  def ite (cond yes no: PairExpr E): PairExpr E :=
    un (ifThen cond yes) (ifElse cond no)
  
  def pairCompl (a b: PairExpr E) :=
    un
      null
      (un
        (pair a.compl any)
        (pair any b.compl))
  
  
  /-
    `arbUnDom domain body` is "syntactic sugar" that represents
    an arbitrary union with a domain.
    
    Due to the implementation of `arbUnDom` (and necessarily so),
    `domain` is inside the introduced existential quantifier, meaning
    that the bound variables of `domain` need to be incremented. In
    particular, `.bvar 0` should never be used in `domain`.
  -/
  def arbUnDom (domain body: PairExpr E): PairExpr E :=
    arbUn (ifThen (ir (.bvar 0) domain) body)
  
  /-
    `arbIrDom domain body` is "syntactic sugar" that represents
    an arbitrary intersection with a domain.
    
    Due to the implementation of `arbIrDom` (and necessarily so),
    `domain` is inside the introduced universal quantifier, meaning
    that the bound variables of `domain` need to be incremented. In
    particular, `.bvar 0` should never be used in `domain`.
  -/
  def arbIrDom (domain body: PairExpr E): PairExpr E :=
    arbIr (un body (ifElse (ir (.bvar 0) domain) any))
  
  -- A union of finitely many expressions.
  def finUn: List (PairExpr E) → PairExpr E
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
  def zthMember (expr: PairExpr E): PairExpr E :=
    arbUn (ifThen (ir (pair (.bvar 0) any) expr) (.bvar 0))
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `fstMember` introduces an existential quantifier, the
    bound variables of `expr` need to be incremented.
  -/
  def fstMember (expr: PairExpr E): PairExpr E :=
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
  def call (fn arg: PairExpr E): PairExpr E :=
    fstMember (ir fn (pair arg any))
  
  /-
    For an encoding `nEnc` of a natural number `n`,
    `succ nEnc` represents the encoding of `n + 1`.
    (Note 0 is reprezented by `Pair.null`.)
  -/
  def succ (expr: PairExpr E): PairExpr E := pair expr null
  
  def nat: Nat → PairExpr E
  | Nat.zero => null
  | Nat.succ pred => succ (nat pred)
  
  
  def InP
    (bv: List Pair)
    (b c: Valuation Pair)
    (expr: SingleLaneExpr pairSignature)
    (d: Pair)
  :=
    expr.interpretation pairSalgebra bv b c d
  
  
  def inUnL (inL: InP bv b c exprL d):
    InP bv b c (un exprL exprR) d
  :=
    Or.inl inL
  
  def inUnR (inR: InP bv b c exprR d):
    InP bv b c (un exprL exprR) d
  :=
    Or.inr inR
  
  def inUnElim
    (inUn: InP bv b c (un exprL exprR) d)
  :
    InP bv b c exprL d ∨ InP bv b c exprR d
  :=
    inUn
  
  
  def inIr
    (l: InP bv b c exprL d)
    (r: InP bv b c exprR d)
  :
    InP bv b c (ir exprL exprR) d
  :=
    ⟨l, r⟩
  
  def inIrElim
    (inIr: InP bv b c (ir exprL exprR) d)
  :
    And
      (InP bv b c exprL d)
      (InP bv b c exprR d)
  :=
    inIr
  
  
  def inCondSome
    (inExpr: InP bv b c expr dE)
    (d: Pair)
  :
    InP bv b c (condSome expr) d
  :=
    ⟨dE, inExpr⟩
  
  def inCondSomeElim
    (inCondSome: InP bv b c (condSome expr) d)
  :
    ∃ dE, InP bv b c expr dE
  :=
    let ⟨dE, inExpr⟩ := inCondSome
    ⟨dE, inExpr⟩
  
  
  def inCondFull
    (allInExpr: (dE: pairSalgebra.D) → InP bv b c expr dE)
    (d: Pair)
  :
    InP bv b c (condFull expr) d
  :=
    allInExpr
  
  def inCondFullElim
    (inCondFull: InP bv b c (condFull expr) d)
  :
    ∀ dE, InP bv b c expr dE
  :=
    inCondFull
  
  
  def inIfThen
    {cond: SingleLanePairExpr}
    (inCond: InP bv b c cond dC)
    (inBody: InP bv b c body d)
  :
    InP bv b c (ifThen cond body) d
  :=
    ⟨⟨dC, inCond⟩, inBody⟩
  
  def inIfThenElim
    {cond: SingleLanePairExpr}
    (inIfThen: InP bv b c (ifThen cond body) d)
  :
    And
      (∃ dC, InP bv b c cond dC)
      (InP bv b c body d)
  :=
    let ⟨exCond, inBody⟩ := inIfThen
    And.intro exCond inBody
  
  
  /-
    This is not a mistake -- the bound vars of the domain are updated
    too. It's unfortunate, but inevitable -- have a look at the
    implementation of `arbUnDom` to see for yourself.
  -/
  def inUnDom
    (inDomain:
      InP (dB :: bv) b c domain dB)
    (inBody:
      InP (dB :: bv) b c body d)
  :
    InP bv b c (arbUnDom domain body) d
  :=
    -- let inUpdated: ((c.update x dBound) x).defMem dBound :=
    --   Valuation.in_update_bound_defMem rfl
    
    inArbUn dB ⟨⟨dB, ⟨rfl, inDomain⟩⟩, inBody⟩
  
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
    (domain body: SingleLanePairExpr)
    (d: Pair): Prop
  where
    inDomain: InP (dB :: bv) b c domain dB
    inBody: InP (dB :: bv) b c body d
  
  def inUnDomElim
    (inUnDom: InP bv b c (arbUnDom domain body) d)
  :
    ∃ dBound, InsUnDomElim bv b c x dBound domain body d
  :=
    let ⟨dBound, ⟨_, dInIr⟩, inBody⟩ := inUnDom.unwrap
    let dEq := inBvarElim dInIr.left rfl
    let inDomain := dEq ▸ dInIr.right
    ⟨dBound, { inDomain, inBody }⟩
  
  
  def inFinUn
    {list: List SingleLanePairExpr}
    (exprIn: expr ∈ list)
    (inExpr: InP bv b c expr p)
  :
    InP bv b c (finUn list) p
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
    List SingleLanePairExpr → Prop
  | List.nil => P
  | List.cons head tail =>
    (InP bv b c head d → P) → InFinUnElim bv b c d P tail
  
  def inFinUnElim
    (inFinUn: InP bv b c (finUn list) d)
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
  
  
  def inNull:
    InP bv b c null Pair.null
  :=
    rfl
  
  def inNullElim
    (inNull: InP bv b c null p)
  :
    p = Pair.null
  :=
    inNull
  
  def inNullElim.neq
    (inNull: InP bv b c null p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (inNull.symm.trans eq)
  
  def inNullElim.nope
    (inNull: InP bv b c null (Pair.pair pA pB))
  :
    P
  :=
    False.elim (inNullElim.neq inNull pA pB rfl)
  
  
  def inPair
    (inL: InP bv b c exprL pairL)
    (inR: InP bv b c exprR pairR)
  :
    InP bv b c (pair exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, inL⟩, ⟨pairR, inR⟩, rfl⟩
  
  structure InPairElim
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: SingleLanePairExpr)
    (pairL pairR: Pair): Prop
  where
    inL: InP bv b c exprL pairL
    inR: InP bv b c exprR pairR
  
  def inPairElim
    (inPair: InP bv b c (pair exprL exprR) (Pair.pair pairL pairR))
  :
    InPairElim bv b c exprL exprR pairL pairR
  :=
    let pl := inPair.unwrap
    let pr := pl.property.unwrap
    
    let plEq: pairL = pl :=
      Pair.noConfusion pr.property (fun eq _ => eq)
    let prEq: pairR = pr :=
      Pair.noConfusion pr.property (fun _ eq => eq)
    
    {
      inL := plEq ▸ pl.val.property
      inR := prEq ▸ pr.val.property
    }
  
  structure InPairElimEx
    (bv: List Pair)
    (b c: Valuation Pair)
    (exprL exprR: SingleLanePairExpr)
    (p pairL pairR: Pair)
  :
    Prop
  where
    eq: p = Pair.pair pairL pairR
    inL: InP bv b c exprL pairL
    inR: InP bv b c exprR pairR
  
  def inPairElim.ex
    (inPair: InP bv b c (pair exprL exprR) p)
  :
    ∃ pairL pairR: Pair,
      InPairElimEx bv b c exprL exprR p pairL pairR
  :=
    match p with
    | Pair.null =>
      Pair.noConfusion (inPair.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        __ := inPairElim inPair
        eq := rfl
      }⟩
  
  def inPairElim.notZero
    (inPair: InP bv b c (pair exprL exprR) p)
  :
    p ≠ Pair.null
  :=
    let ⟨_pairL, prop⟩ := (ex inPair).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inPairElim.nope
    (inPair: InP bv b c (pair exprL exprR) Pair.null)
  :
    P
  :=
    (notZero inPair rfl).elim
  
  
  def inZthMember
    (inExpr: InP (pA :: bv) b c expr (Pair.pair pA pB))
  :
    InP bv b c (zthMember expr) pA
  :=
    inArbUn pA ⟨
      ⟨Pair.pair pA pB, (inPair rfl inAny), inExpr⟩,
      rfl,
    ⟩
  
  
  def inFstMember
    (inExpr: InP (pB :: bv) b c expr (Pair.pair pA pB))
  :
    InP bv b c (fstMember expr) pB
  :=
    inArbUn _ ⟨
      ⟨Pair.pair pA pB, (inPair inAny rfl), inExpr⟩,
      rfl,
    ⟩
  
  
  def inZthMemberElim
    (inZthMember: InP bv b c (zthMember expr) zth)
  :
    ∃ fst,
      InP
        (zth :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨inCond, inBody⟩⟩ := inZthMember
    let ⟨pCond, ⟨InPairXaAny, pCondInsExpr⟩⟩ := inCond
    
    match pCond with
    | Pair.null => inPairElim.nope InPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨inL, _insR⟩ := inPairElim InPairXaAny
      let eqPCondZth: pCondZth = pZth := inBvarElim inL rfl
      let eqPZth: zth = pZth := inBvarElim inBody rfl
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inFstMemberElim
    (inFstMember: InP bv b c (fstMember expr) fst)
  :
    ∃ zth,
      InP
        (fst :: bv)
        b
        c
        expr
        (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨inCond, inBody⟩⟩ := inFstMember
    let ⟨pCond, ⟨InPairAnyXa, pCondInsExpr⟩⟩ := inCond
    
    match pCond with
    | Pair.null => inPairElim.nope InPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, inR⟩ := inPairElim InPairAnyXa
      let eqPCondZth: pCondFst = pFst := inBvarElim inR rfl
      let eqPZth: fst = pFst := inBvarElim inBody rfl
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ pCondInsExpr⟩
  
  def inZthFstElim
    (inZth: InP bv b c (zthMember (Expr.var lane x)) zth)
    (inFst: InP bv b c (fstMember (Expr.var lane x)) fst)
    (isUnit: c x = Set3.just d)
  :
    InP bv b c (Expr.var lane x) (Pair.pair zth fst)
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
    (inFn: InP (pB :: bv) b c fn (Pair.pair pA pB))
    (inArg: InP (pB :: bv) b c arg pA)
  :
    InP bv b c (call fn arg) pB
  :=
    inFstMember (inIr inFn (inPair inArg inAny))
  
  
  def inCallElim
    (inCall: InP bv b c (call fn arg) pB)
  :
    ∃ pA,
      And
        (InP (pB :: bv) b c fn (Pair.pair pA pB))
        (InP (pB :: bv) b c arg pA)
  :=
    let ⟨zth, inIr⟩ := inFstMemberElim inCall
    let ⟨inFn, inP⟩ := inIrElim inIr
    
    ⟨zth, And.intro inFn (inPairElim inP).inL⟩
  
  def inCallElimBound
    (inCall: InP bv b c (call fn (Expr.var lane arg)) pB)
    (isUnit: c arg = Set3.just pA)
  :
    InP (pB :: bv) b c fn (Pair.pair pA pB)
  :=
    let ⟨aAlias, ⟨inFn, inArg⟩⟩ := inCallElim inCall
    let eq: aAlias = pA :=
      match lane with
      | .defLane => Set3.just.inDefToEq (isUnit ▸ inArg)
      | .posLane => Set3.just.inPosToEq (isUnit ▸ inArg)
    eq ▸ inFn
  
  
  def inNat b c n
  :
    InP bv b c (nat n) (Pair.fromNat n)
  :=
    match n with
    | Nat.zero => inNull
    | Nat.succ pred => inPair (inNat b c pred) inNull
  
  def inNatElim
    (inNatExpr: InP bv b c (nat n) p)
  :
    p = Pair.fromNat n
  :=
    match n, p with
    | Nat.zero, _ => inNullElim inNatExpr ▸ rfl
    | Nat.succ _, .null => inPairElim.nope inNatExpr
    | Nat.succ _, .pair _ _ =>
      let ⟨l, r⟩ := inPairElim inNatExpr
      (inNatElim l) ▸ (inNullElim r) ▸ rfl
  
  def inNatElimNope
    (inNat: InP bv b c (nat n) (.fromNat m))
    (neq: n ≠ m)
  :
    P
  :=
    (neq (Pair.fromNat_inj_eq (Eq.symm (inNatElim inNat)))).elim
  
  def inNatElimDepth
    (inNat: InP bv b c (nat n) p)
  :
    p.depth = n
  :=
    (inNatElim inNat) ▸ (Pair.fromNat_depth_eq n)
  
  def inNatElimDecode
    (inNatExpr: InP bv b c (nat n) p)
  :
    p.depth = n
  :=
    inNatElimDepth inNatExpr
  
  
  def null_eq_null:
    Eq
      (Expr.op (sig := pairSignature) pairSignature.Op.null args0)
      (Expr.op pairSignature.Op.null args1)
  :=
    congr rfl (funext nofun)
  
  
end PairExpr


def Expr.toString (serializeVar: E → Nat → String):
  Expr E pairSignature → String
| .var info x => serializeVar info x
| .bvar x => s!"b{x}"
| .op pairSignature.Op.un args =>
  let left := (args ArityTwo.zth).toString serializeVar
  let rite := (args ArityTwo.fst).toString serializeVar
  s!"({left}) | ({rite})"
| .op pairSignature.Op.ir args =>
  let left := (args ArityTwo.zth).toString serializeVar
  let rite := (args ArityTwo.fst).toString serializeVar
  s!"({left}) & ({rite})"
| .op pairSignature.Op.condSome args =>
  let cond := (args ArityOne.zth).toString serializeVar
  s!"(?i {cond})"
| .op pairSignature.Op.condFull args =>
  let cond := (args ArityOne.zth).toString serializeVar
  s!"(?f {cond})"
| .op pairSignature.Op.null _ =>
  "null"
| .op pairSignature.Op.pair args =>
  let left := (args ArityTwo.zth).toString serializeVar
  let rite := (args ArityTwo.fst).toString serializeVar
  s!"({left}, {rite})"
| .compl expr =>
  let exprStr := expr.toString serializeVar
  s!"!({exprStr})"
| .arbUn body =>
  let bodyStr := body.toString serializeVar
  s!"Ex ({bodyStr})"
| .arbIr body =>
  let bodyStr := body.toString serializeVar
  s!"All ({bodyStr})"

def BasicPairExpr.toString: BasicPairExpr → String :=
  Expr.toString fun _ x => s!"{x}"

def SingleLanePairExpr.toString: SingleLanePairExpr → String :=
  Expr.toString fun
    | .defLane, x => s!":{x}"
    | .posLane, x => s!".{x}"

instance: ToString BasicPairExpr where
  toString := BasicPairExpr.toString

instance: ToString SingleLanePairExpr where
  toString := SingleLanePairExpr.toString

instance: ToString (PairExpr Unit) := instToStringBasicPairExpr
instance: ToString (PairExpr SingleLaneVarType) := instToStringSingleLanePairExpr
