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
    Expr.Un n (Expr.ifThen (Expr.ir (pairExpr n anyExpr) expr) n)
  
  /-
    Let `expr` be an expression that represets a set of
    pairs `s3` (under some valuation). The expression
    `fstMember n expr` then represents the set of all
    `b` such that `(_, b) ∈ s3`.
    
    `n` must not be a free variable in `expr`.
  -/
  def fstMember (n: Nat) (expr: Expr): Expr :=
    Expr.Un n (Expr.ifThen (Expr.ir (pairExpr anyExpr n) expr) n)
  
  /-
    Let `fn` and `arg` be expressions that represent
    sets of pairs `sFn` and `sArg` (under some valuation).
    The expression `callExpr n fn arg` then represents
    the set of all `b` such that there exists an `a`
    such that `(a, b) ∈ sFn` and `a ∈ sArg`.
    
    `sFn` can be viewed as a function that, as a set,
    contains its input-output pairs.
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
  
  
  def insZero:
    Ins pairSalgebra v zeroExpr Pair.zero
  :=
    rfl
  
  def insZeroElim
    (s: Ins pairSalgebra v zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def insZeroElim.neq
    (s: Ins pairSalgebra v zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def insZeroElim.nope
    (s: Ins pairSalgebra v zeroExpr (Pair.pair a b))
  :
    P
  :=
    False.elim (insZeroElim.neq s a b rfl)
  
  
  def inwZero:
    Inw pairSalgebra v zeroExpr Pair.zero
  :=
    rfl
  
  def inwZeroElim
    (s: Inw pairSalgebra v zeroExpr p)
  :
    p = Pair.zero
  :=
    s
  
  def inwZeroElim.neq
    (s: Inw pairSalgebra v zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (s.symm.trans eq)
  
  def inwZeroElim.nope
    (s: Inw pairSalgebra v zeroExpr (Pair.pair a b))
  :
    P
  :=
    False.elim (inwZeroElim.neq s a b rfl)
  
  
  def insPair
    (insL: Ins pairSalgebra v exprL pairL)
    (insR: Ins pairSalgebra v exprR pairR)
  :
    Ins pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  def inwPair
    (insL: Inw pairSalgebra v exprL pairL)
    (insR: Inw pairSalgebra v exprR pairR)
  :
    Inw pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  
  structure InsPairElim
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    insL: Ins pairSalgebra v exprL pairL
    insR: Ins pairSalgebra v exprR pairR
  
  def insPairElim
    (s: Ins pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR))
  :
    InsPairElim v exprL exprR pairL pairR
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
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (p pairL pairR: Pair): Prop
  where
    eq: p = Pair.pair pairL pairR
    insL: Ins pairSalgebra v exprL pairL
    insR: Ins pairSalgebra v exprR pairR
  
  def insPairElim.ex
    (s: Ins pairSalgebra v (pairExpr exprL exprR) p)
  :
    ∃ pairL pairR: Pair, InsPairElim.Ex v exprL exprR p pairL pairR
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
    (s: Ins pairSalgebra v (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex s).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def insPairElim.nope
    (s: Ins pairSalgebra v (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero s rfl).elim
  
  
  structure InwPairElim
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    inwL: Inw pairSalgebra v exprL pairL
    inwR: Inw pairSalgebra v exprR pairR
  
  def inwPairElim
    (w: Inw pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR))
  :
    InwPairElim v exprL exprR pairL pairR
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
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: Inw pairSalgebra v exprL pairL
    insR: Inw pairSalgebra v exprR pairR
  
  def inwPairElim.ex
    (w: Inw pairSalgebra v (pairExpr exprL exprR) p)
  :
    ∃ pairL pairR: Pair, InwPairElim.Ex v exprL exprR p pairL pairR
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
    (w: Inw pairSalgebra v (pairExpr exprL exprR) p)
  :
    p ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex w).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inwPairElim.nope
    (w: Inw pairSalgebra v (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero w rfl).elim
  
  
  def insZthMember
    (s: Ins pairSalgebra (v.update x a) expr (Pair.pair a b))
  :
    Ins pairSalgebra v (zthMember x expr) a
  :=
    insArbUn _ ⟨
      ⟨Pair.pair a b,
        And.intro (insPair insBound insAny) s⟩,
      insBound,
    ⟩
  
  def inwZthMember
    (s: Inw pairSalgebra (v.update x a) expr (Pair.pair a b))
  :
    Inw pairSalgebra v (zthMember x expr) a
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair a b,
        And.intro (inwPair inwBound inwAny) s⟩,
      inwBound,
    ⟩
  
  
  def insFstMember
    (s: Ins pairSalgebra (v.update x b) expr (Pair.pair a b))
  :
    Ins pairSalgebra v (fstMember x expr) b
  :=
    insArbUn _ ⟨
      ⟨Pair.pair a b,
        And.intro (insPair insAny insBound) s⟩,
      insBound,
    ⟩
  
  def inwFstMember
    (s: Inw pairSalgebra (v.update x b) expr (Pair.pair a b))
  :
    Inw pairSalgebra v (fstMember x expr) b
  :=
    inwArbUn _ ⟨
      ⟨Pair.pair a b,
        And.intro (inwPair inwAny inwBound) s⟩,
      inwBound,
    ⟩
  
  
  def insZthMemberElim
    (s: Ins pairSalgebra v (zthMember x expr) zth)
  :
    ∃ fst, Ins pairSalgebra (v.update x zth) expr (Pair.pair zth fst)
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
    (s: Inw pairSalgebra v (zthMember x expr) zth)
  :
    ∃ fst, Inw pairSalgebra (v.update x zth) expr (Pair.pair zth fst)
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
    (s: Ins pairSalgebra v (fstMember x expr) fst)
  :
    ∃ zth, Ins pairSalgebra (v.update x fst) expr (Pair.pair zth fst)
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
    (s: Inw pairSalgebra v (fstMember x expr) fst)
  :
    ∃ zth, Inw pairSalgebra (v.update x fst) expr (Pair.pair zth fst)
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
    (insZth: Ins pairSalgebra v (zthMember xA (var xB)) zth)
    (insFst: Ins pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: v xB = Set3.just d)
  :
    Ins pairSalgebra v xB (Pair.pair zth fst)
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
    (inwZth: Inw pairSalgebra v (zthMember xA (var xB)) zth)
    (inwFst: Inw pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: v xB = Set3.just d)
  :
    Inw pairSalgebra v xB (Pair.pair zth fst)
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
    (insFn: Ins pairSalgebra (v.update x b) fn (Pair.pair a b))
    (insArg: Ins pairSalgebra (v.update x b) arg a)
  :
    Ins pairSalgebra v (callExpr x fn arg) b
  :=
    insFstMember (insIr insFn (insPair insArg insAny))
  
  def inwCallExpr
    (inwFn: Inw pairSalgebra (v.update x b) fn (Pair.pair a b))
    (inwArg: Inw pairSalgebra (v.update x b) arg a)
  :
    Inw pairSalgebra v (callExpr x fn arg) b
  :=
    inwFstMember (inwIr inwFn (inwPair inwArg inwAny))
  
  
  def insCallExprElim
    (s: Ins pairSalgebra v (callExpr x fn arg) b)
  :
    ∃ a,
      And
        (Ins pairSalgebra (v.update x b) fn (Pair.pair a b))
        (Ins pairSalgebra (v.update x b) arg a)
  :=
    let ⟨zth, insIr⟩ := insFstMemberElim s
    let ⟨insFn, insP⟩ := insIrElim insIr
    
    ⟨zth, And.intro insFn (insPairElim insP).insL⟩
  
  def inwCallExprElim
    (w: Inw pairSalgebra v (callExpr x fn arg) b)
  :
    ∃ a,
      And
        (Inw pairSalgebra (v.update x b) fn (Pair.pair a b))
        (Inw pairSalgebra (v.update x b) arg a)
  :=
    let ⟨zth, inwIr⟩ := inwFstMemberElim w
    let ⟨inwFn, inwP⟩ := inwIrElim inwIr
    
    ⟨zth, And.intro inwFn (inwPairElim inwP).inwL⟩
  
  def insCallElimBound
    (s: Ins pairSalgebra v (callExpr x fn (var arg)) b)
    (isUnit: v arg = Set3.just a)
    (neq: x ≠ arg)
  :
    Ins pairSalgebra (v.update x b) fn (Pair.pair a b)
  :=
    let ⟨aAlias, ⟨insFn, insArg⟩⟩ := insCallExprElim s
    
    let insVArg: (v arg).defMem aAlias := insFreeElim insArg neq
    let eq: aAlias = a := Set3.just.inDefToEq (isUnit ▸ insVArg)
    
    eq ▸ insFn
  
  def inwCallElimBound
    (w: Inw pairSalgebra v (callExpr x fn (var arg)) b)
    (isUnit: v arg = Set3.just a)
    (neq: x ≠ arg)
  :
    Inw pairSalgebra (v.update x b) fn (Pair.pair a b)
  :=
    let ⟨aAlias, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim w
    
    let inwVArg: (v arg).posMem aAlias := inwFreeElim inwArg neq
    let eq: aAlias = a := Set3.just.inPosToEq (isUnit ▸ inwVArg)
    
    eq ▸ inwFn
  
  
  def insNatExpr v n
  :
    Ins pairSalgebra v (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => insZero
    | Nat.succ pred => insPair (insNatExpr v pred) insZero
  
  def inwNatExpr v n
  :
    Inw pairSalgebra v (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => inwZero
    | Nat.succ pred => inwPair (inwNatExpr v pred) inwZero
  
  def inwNatExprElim
    (w: Inw pairSalgebra v (natExpr n) p)
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
    (s: Ins pairSalgebra v (natExpr n) p)
  :
    p = fromNat n
  :=
    inwNatExprElim s.toInw
  
  def inwNatExprElimDepth
    (w: Inw pairSalgebra v (natExpr n) p)
  :
    depth p = n
  :=
    (inwNatExprElim w) ▸ (fromNat.depthEq _)
  
  def insNatExprElimDecode
    (s: Ins pairSalgebra v (natExpr n) p)
  :
    depth p = n
  :=
    inwNatExprElimDepth s.toInw
  
end PairExpr
