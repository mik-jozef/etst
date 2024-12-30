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
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `zthMember n expr` then represents the set of all
    `a` such that `(a, _) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def zthMember (n: Nat) (expr: Expr): Expr :=
    Expr.arbUn n (Expr.ifThen (Expr.ir (pairExpr n anyExpr) expr) n)
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def fstMember (n: Nat) (expr: Expr): Expr :=
    Expr.arbUn n (Expr.ifThen (Expr.ir (pairExpr anyExpr n) expr) n)
  
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
    fstMember n (Expr.ir fn (pairExpr arg anyExpr))
  
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
  
end PairExpr
