import Operators
import ExampleWFCs

namespace Expr
  def anyExpr: Expr sig := Expr.Un 0 0
  def noneExpr: Expr sig := Expr.Ir 0 0
  
  -- Make sure n is not a free var in the domain expr.
  def unionExpr (n: Nat) (domain body: Expr sig): Expr sig :=
    Expr.Un n (Expr.ifThen (Expr.ir n domain) body)
  
  -- Make sure n is not a free var in the domain expr.
  -- `All t: T, b` === `All t, b | (!(t & domain) then any)`.
  def irsecExpr (n: Nat) (domain body: Expr sig): Expr sig :=
    Expr.Ir
      n
      (Expr.un
        body
        (Expr.ifThen (Expr.cpl (Expr.ir n domain)) (anyExpr)))
  
  def finUnExpr: List (Expr sig) → (Expr sig)
  | List.nil => noneExpr
  | List.cons expr List.nil => expr
  | List.cons expr0 (List.cons expr1 rest) =>
      Expr.un expr0 (finUnExpr (expr1::rest))
  
  
  instance exprOfNat (n: Nat): OfNat (Expr sig) n where
    ofNat := Expr.var n
  
  instance coe: Coe Nat (Expr sig) where
    coe := fun n => Expr.var n
  
  
  -- "in strong". `d "∈s" t` iff `d ∈ t.defMem`. See also `inw`.
  def ins
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg v v).defMem
  
  -- "in weak". `d "∈s" t` iff `d ∈ t.posMem`. See also `ins`.
  def inw
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg v v).posMem
  
  def ins.toInw (s: ins salg v expr d):
    inw salg v expr d
  :=
    (Expr.interpretation salg v v expr).defLePos s
  
  
  def ins.unL
    {exprL: Expr sig}
    (s: ins salg v exprL d)
    (exprR: Expr sig)
  :
    ins salg v (Expr.un exprL exprR) d
  :=
    Or.inl s
  
  def ins.unR
    {exprR: Expr sig}
    (exprL: Expr sig)
    (s: ins salg v exprR d)
  :
    ins salg v (Expr.un exprL exprR) d
  :=
    Or.inr s
  
  def ins.unElim
    (s: ins salg v (Expr.un exprL exprR) d)
  :
    Or
      (ins salg v exprL d)
      (ins salg v exprR d)
  :=
    s
  
  def ins.arbUn
    (s: ins salg (v.update x dBound) body d)
  :
    ins salg v (Expr.Un x body) d
  :=
    ⟨dBound, s⟩
  
  def ins.arbUnElim
    (s: ins salg v (Expr.Un x body) d)
  :
    ∃ dBound, ins salg (v.update x dBound) body d
  :=
    s
  
  
  def insBound {v: Valuation salg.D}:
    ins salg (v.update x dBound) (var x) dBound
  :=
    Valuation.update.inEq.defMem v x dBound
  
  def insBoundEq
    {v: Valuation salg.D}
    (s: ins salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inDef.eq s
  
  def inwBoundEq
    {v: Valuation salg.D}
    (s: inw salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inPos.eq s
  
  def insFree
    {v: Valuation salg.D}
    {d: salg.D}
    (isDef: (v x).defMem d)
    (neq: xB ≠ x)
  :
    ins salg (v.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.defMem v neq isDef
  
  def inwFree
    {v: Valuation salg.D}
    {d: salg.D}
    (isPos: (v x).posMem d)
    (neq: xB ≠ x)
  :
    inw salg (v.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.posMem v neq isPos
  
  def insFreeElim
    (s: ins salg (v.update xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    ins salg v (var x) d
  :=
    Valuation.update.inNeqElim.defMem s neq
  
  def inwFreeElim
    (s: inw salg (v.update xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    inw salg v (var x) d
  :=
    Valuation.update.inNeqElim.posMem s neq
  
  
  /-
    This is not a mistake -- the valuation of the
    domain is updated too. It's unfortunate, but
    inevitable -- have a look at the implemetation
    of `unionExpr` to see for yourself.
  -/
  def ins.unDom
    (insDomain: ins salg (v.update x dBound) domain dBound)
    (insBody: ins salg (v.update x dBound) body d)
  :
    ins salg v (unionExpr x domain body) d
  :=
    let inUpdated: ((v.update x dBound) x).defMem dBound :=
      Valuation.update.inEq.defMem v x dBound
    
    ins.arbUn ⟨⟨dBound, ⟨inUpdated, insDomain⟩⟩, insBody⟩
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (under the condition that any two instances are only
  -- allowed to contain the same instance). We have global
  -- choice anyway!
  structure ins.UnDomElim
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (x: Nat)
    (dBound: salg.D)
    (domain body: Expr sig)
    (d: salg.D): Prop
  where
    insDomain: ins salg (v.update x dBound) domain dBound
    insBody: ins salg (v.update x dBound) body d
  
  def ins.unDomElim
    (insUnDom: ins salg v (unionExpr x domain body) d)
  :
    ∃ dBound, ins.UnDomElim salg v x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    let vUpdated := v.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      insBoundEq dInIr.property.left
    
    let insDomain:
      ins salg vUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        insDomain := insDomain
        insBody := dBound.property.right
      },
    ⟩
  
  structure inw.UnDomElim
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (x: Nat)
    (dBound: salg.D)
    (domain body: Expr sig)
    (d: salg.D): Prop
  where
    insDomain: inw salg (v.update x dBound) domain dBound
    insBody: inw salg (v.update x dBound) body d
  
  def inw.unDomElim
    (insUnDom: inw salg v (unionExpr x domain body) d)
  :
    ∃ dBound, inw.UnDomElim salg v x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    let vUpdated := v.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      inwBoundEq dInIr.property.left
    
    let insDomain:
      inw salg vUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        insDomain := insDomain
        insBody := dBound.property.right
      },
    ⟩
  
  
  def insVar
    {v: Valuation salg.D}
    {d: salg.D}
    (s: (v x).defMem d)
  :
    ins salg v (var x) d
  :=
    s
  
end Expr


namespace PairExpr
  open Expr
  open pairSignature
  
  def Expr := _root_.Expr pairSignature
  
  -- TODO why do these two need to be duplicated?
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
  
  
  def insZeroEq v:
    ins pairSalgebra v zeroExpr = Set.just Pair.zero
  :=
    rfl
  
  def insZeroIff v d:
    ins pairSalgebra v zeroExpr d ↔ d = Pair.zero
  :=
    Iff.of_eq (insZeroEq v ▸ rfl)
  
  def insZero v:
    ins pairSalgebra v zeroExpr Pair.zero
  :=
    (insZeroIff v Pair.zero).mpr rfl
  
  def inwZero v:
    inw pairSalgebra v zeroExpr = Set.just Pair.zero
  :=
    rfl
  
  def inwZeroIff v d:
    inw pairSalgebra v zeroExpr d ↔ d = Pair.zero
  :=
    Iff.of_eq (inwZero v ▸ rfl)
  
  
  def insPair
    (insL: ins pairSalgebra v exprL pairL)
    (insR: ins pairSalgebra v exprR pairR)
  :
    ins pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  def inwPair
    (insL: inw pairSalgebra v exprL pairL)
    (insR: inw pairSalgebra v exprR pairR)
  :
    inw pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR)
  :=
    ⟨⟨pairL, insL⟩, ⟨pairR, insR⟩, rfl⟩
  
  
  structure InsPairElim
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    insL: ins pairSalgebra v exprL pairL
    insR: ins pairSalgebra v exprR pairR
  
  def insPairElim v
    (s: ins pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR))
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
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: ins pairSalgebra v exprL pairL
    insR: ins pairSalgebra v exprR pairR
  
  def insPairElim.ex v
    (s: ins pairSalgebra v (pairExpr exprL exprR) pair)
  :
    ∃ pairL pairR: Pair, InsPairElim.Ex v exprL exprR pair pairL pairR
  :=
    match pair with
    | Pair.zero =>
      Pair.noConfusion (s.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (insPairElim v s).insL
        insR := (insPairElim v s).insR
      }⟩
  
  
  structure InwPairElim
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    inwL: inw pairSalgebra v exprL pairL
    inwR: inw pairSalgebra v exprR pairR
  
  def inwPairElim v
    (s: inw pairSalgebra v (pairExpr exprL exprR) (Pair.pair pairL pairR))
  :
    InwPairElim v exprL exprR pairL pairR
  :=
    let pl := s.unwrap
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
    insL: inw pairSalgebra v exprL pairL
    insR: inw pairSalgebra v exprR pairR
  
  def inwPairElim.ex v
    (s: inw pairSalgebra v (pairExpr exprL exprR) pair)
  :
    ∃ pairL pairR: Pair, InwPairElim.Ex v exprL exprR pair pairL pairR
  :=
    match pair with
    | Pair.zero =>
      Pair.noConfusion (s.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (inwPairElim v s).inwL
        insR := (inwPairElim v s).inwR
      }⟩
  
  
  def insPairNotZero
    (s: ins pairSalgebra v (pairExpr exprL exprR) pair)
  :
    pair ≠ Pair.zero
  :=
    let ⟨_pairL, exR⟩ := (insPairElim.ex v s).unwrap
    let ⟨_pairR, ⟨eq, _, _⟩⟩ := exR
    
    fun eqZero => (Pair.noConfusion (eqZero.symm.trans eq))
  
end PairExpr


namespace wfm
  def insWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.ins salg (dl.wellFoundedModel salg) d
  
  def inwWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.inw salg (dl.wellFoundedModel salg) d
  
  def insWfmDef.toInsWfm
    (s: insWfm salg dl (dl.getDef n) d)
  :
    insWfm salg dl n d
  := by
    unfold insWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ s
  
  def insWfm.toInsWfmDef
    {n: Nat}
    (s: insWfm salg dl n d)
  :
    insWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v n = dl.interpretation salg v v n
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v n).defMem d from eqAtN ▸ s
  
  def inwWfmDef.toInwWfm
    (s: inwWfm salg dl (dl.getDef n) d)
  :
    inwWfm salg dl n d
  := by
    unfold inwWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ s
  
  def inwWfm.toInwWfmDef
    {n: Nat}
    (s: inwWfm salg dl n d)
  :
    inwWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v n = dl.interpretation salg v v n
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v n).posMem d from eqAtN ▸ s
  
end wfm
