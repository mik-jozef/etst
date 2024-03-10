import Operators
import ExampleWFCs
import EqSwappedUnusedVar

namespace Expr
  def anyExpr: Expr sig := Expr.Un 0 0
  def noneExpr: Expr sig := Expr.cpl anyExpr
  
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
  | List.cons expr tail =>
    Expr.un expr (finUnExpr (tail))
  
  
  instance exprOfNat (n: Nat): OfNat (Expr sig) n where
    ofNat := Expr.var n
  
  instance coe: Coe Nat (Expr sig) where
    coe := fun n => Expr.var n
  
  
  -- "in strong". `d "∈s" t` iff `d ∈ t.defMem`. See also `inw`.
  def Ins
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg v v).defMem
  
  -- "in weak". `d "∈s" t` iff `d ∈ t.posMem`. See also `ins`.
  def Inw
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg v v).posMem
  
  def Ins.toInw (s: Ins salg v expr d):
    Inw salg v expr d
  :=
    (Expr.interpretation salg v v expr).defLePos s
  
  
  def insUnL
    {exprL: Expr sig}
    (s: Ins salg v exprL d)
    (exprR: Expr sig)
  :
    Ins salg v (Expr.un exprL exprR) d
  :=
    Or.inl s
  
  def inwUnL
    {exprL: Expr sig}
    (w: Inw salg v exprL d)
    (exprR: Expr sig)
  :
    Inw salg v (Expr.un exprL exprR) d
  :=
    Or.inl w
  
  
  def insUnR
    {exprR: Expr sig}
    (exprL: Expr sig)
    (s: Ins salg v exprR d)
  :
    Ins salg v (Expr.un exprL exprR) d
  :=
    Or.inr s
  
  def inwUnR
    {exprR: Expr sig}
    (exprL: Expr sig)
    (w: Inw salg v exprR d)
  :
    Inw salg v (Expr.un exprL exprR) d
  :=
    Or.inr w
  
  
  def insUnElim
    (s: Ins salg v (Expr.un exprL exprR) d)
  :
    Or
      (Ins salg v exprL d)
      (Ins salg v exprR d)
  :=
    s
  
  def inwUnElim
    (s: Inw salg v (Expr.un exprL exprR) d)
  :
    Or
      (Inw salg v exprL d)
      (Inw salg v exprR d)
  :=
    s
  
  
  def insArbUn
    (s: Ins salg (v.update x dBound) body d)
  :
    Ins salg v (Expr.Un x body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    (s: Inw salg (v.update x dBound) body d)
  :
    Inw salg v (Expr.Un x body) d
  :=
    ⟨dBound, s⟩
  
  
  def insArbUnElim
    (s: Ins salg v (Expr.Un x body) d)
  :
    ∃ dBound, Ins salg (v.update x dBound) body d
  :=
    s
  
  def inwArbUnElim
    (s: Inw salg v (Expr.Un x body) d)
  :
    ∃ dBound, Inw salg (v.update x dBound) body d
  :=
    s
  
  
  def insCpl
    (w: ¬Inw salg v expr d)
  :
    Ins salg v (Expr.cpl expr) d
  :=
    w
  
  def inwCpl
    (s: ¬Ins salg v expr d)
  :
    Inw salg v (Expr.cpl expr) d
  :=
    s
  
  def insCplElim
    (s: Ins salg v (Expr.cpl expr) d)
  :
    ¬Inw salg v expr d
  :=
    s
  
  def inwCplElim
    (w: Inw salg v (Expr.cpl expr) d)
  :
    ¬Ins salg v expr d
  :=
    w
  
  
  def ninsCpl
    (w: Inw salg v expr d)
  :
    ¬Ins salg v (Expr.cpl expr) d
  :=
    fun ins => ins w
  
  def ninwCpl
    (s: Ins salg v expr d)
  :
    ¬Inw salg v (Expr.cpl expr) d
  :=
    fun inw => inw s
  
  
  def insBound {v: Valuation salg.D}:
    Ins salg (v.update x dBound) (var x) dBound
  :=
    Valuation.update.inEq.defMem v x dBound
  
  def inwBound {v: Valuation salg.D}:
    Inw salg (v.update x dBound) (var x) dBound
  :=
    Valuation.update.inEq.posMem v x dBound
  
  def insBoundEq
    {v: Valuation salg.D}
    (s: Ins salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inDef.eq s
  
  def inwBoundEq
    {v: Valuation salg.D}
    (w: Inw salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inPos.eq w
  
  def insFree
    {v: Valuation salg.D}
    {d: salg.D}
    (isDef: (v x).defMem d)
    (neq: xB ≠ x)
  :
    Ins salg (v.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.defMem v neq isDef
  
  def inwFree
    {v: Valuation salg.D}
    {d: salg.D}
    (isPos: (v x).posMem d)
    (neq: xB ≠ x)
  :
    Inw salg (v.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.posMem v neq isPos
  
  def insFreeElim
    (s: Ins salg (v.update xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg v (var x) d
  :=
    Valuation.update.inNeqElim.defMem s neq
  
  def inwFreeElim
    (w: Inw salg (v.update xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg v (var x) d
  :=
    Valuation.update.inNeqElim.posMem w neq
  
  
  def insAny: Ins salg v anyExpr d := insArbUn insBound
  def inwAny: Inw salg v anyExpr d := inwArbUn inwBound
  
  def ninsNone: ¬Ins salg v noneExpr d := ninsCpl inwAny
  def ninwNone: ¬Inw salg v noneExpr d := ninwCpl insAny
  
  
  /-
    This is not a mistake -- the valuation of the
    domain is updated too. It's unfortunate, but
    inevitable -- have a look at the implemetation
    of `unionExpr` to see for yourself.
  -/
  def insUnDom
    (insDomain: Ins salg (v.update x dBound) domain dBound)
    (insBody: Ins salg (v.update x dBound) body d)
  :
    Ins salg v (unionExpr x domain body) d
  :=
    let inUpdated: ((v.update x dBound) x).defMem dBound :=
      Valuation.update.inEq.defMem v x dBound
    
    insArbUn ⟨⟨dBound, ⟨inUpdated, insDomain⟩⟩, insBody⟩
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (under the condition that any two instances are only
  -- allowed to contain the same instance). We have global
  -- choice anyway!
  structure insUnDomElim.Str
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (x: Nat)
    (dBound: salg.D)
    (domain body: Expr sig)
    (d: salg.D): Prop
  where
    insDomain: Ins salg (v.update x dBound) domain dBound
    insBody: Ins salg (v.update x dBound) body d
  
  def insUnDomElim
    (insUnDom: Ins salg v (unionExpr x domain body) d)
  :
    ∃ dBound, insUnDomElim.Str salg v x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    let vUpdated := v.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      insBoundEq dInIr.property.left
    
    let insDomain:
      Ins salg vUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        insDomain := insDomain
        insBody := dBound.property.right
      },
    ⟩
  
  structure inwUnDomElim.Str
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (x: Nat)
    (dBound: salg.D)
    (domain body: Expr sig)
    (d: salg.D): Prop
  where
    insDomain: Inw salg (v.update x dBound) domain dBound
    insBody: Inw salg (v.update x dBound) body d
  
  def inwUnDomElim
    (insUnDom: Inw salg v (unionExpr x domain body) d)
  :
    ∃ dBound, inwUnDomElim.Str salg v x dBound domain body d
  :=
    let dBound := insUnDom.unwrap
    let dInIr := dBound.property.left.unwrap
    
    let vUpdated := v.update x dBound
    
    let dEq: dInIr.val = dBound.val :=
      inwBoundEq dInIr.property.left
    
    let insDomain:
      Inw salg vUpdated domain dBound.val
    :=
      dEq ▸ dInIr.property.right
    
    ⟨
      dBound,
      {
        insDomain := insDomain
        insBody := dBound.property.right
      },
    ⟩
  
  
  -- TODO delete?
  def insVar
    {v: Valuation salg.D}
    {d: salg.D}
    (s: (v x).defMem d)
  :
    Ins salg v (var x) d
  :=
    s
  
  
  def insFinUn
    {list: List (Expr sig)}
    (exprIn: expr ∈ list)
    (s: Ins salg v expr p)
  :
    Ins salg v (finUnExpr list) p
  :=
    match list with
    | List.nil => List.Mem.nope exprIn
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ insUnL s _)
        (fun inRest => insUnR _ (insFinUn inRest s))
  
  def inwFinUn
    {list: List (Expr sig)}
    (exprIn: expr ∈ list)
    (w: Inw salg v expr p)
  :
    Inw salg v (finUnExpr list) p
  :=
    match list with
    | List.nil => List.Mem.nope exprIn
    | List.cons _e0 _rest =>
      exprIn.elim
        (fun eq => eq ▸ inwUnL w _)
        (fun inRest => inwUnR _ (inwFinUn inRest w))
  
  
  def insFinUnElim.Ret
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (d: salg.D)
    (P: Prop)
  :
    List (Expr sig) → Prop
  | List.nil => P
  | List.cons head tail =>
    (Ins salg v head d → P) → Ret salg v d P tail
  
  def insFinUnElim.retOfP
    (list: List (Expr sig))
    (p: P)
  :
    insFinUnElim.Ret salg v d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => retOfP tail p
  
  def insFinUnElim
    (s: Ins salg v (finUnExpr list) d)
  :
    insFinUnElim.Ret salg v d P list
  :=
    match list with
    | List.nil => False.elim (ninsNone s)
    | List.cons _head tail =>
      (insUnElim s).elim
        (fun insHead insHeadToP =>
          insFinUnElim.retOfP tail (insHeadToP insHead))
        (fun insTail _ => insFinUnElim insTail)
  
  
  def inwFinUnElim.Ret
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (d: salg.D)
    (P: Prop)
  :
    List (Expr sig) → Prop
  | List.nil => P
  | List.cons head tail =>
    (Inw salg v head d → P) → Ret salg v d P tail
  
  def inwFinUnElim.retOfP
    (list: List (Expr sig))
    (p: P)
  :
    inwFinUnElim.Ret salg v d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => retOfP tail p
  
  def inwFinUnElim
    (s: Inw salg v (finUnExpr list) d)
  :
    inwFinUnElim.Ret salg v d P list
  :=
    match list with
    | List.nil => False.elim (ninwNone s)
    | List.cons _head tail =>
      (inwUnElim s).elim
        (fun inwHead insHeadToP =>
          inwFinUnElim.retOfP tail (insHeadToP inwHead))
        (fun insTail _ => inwFinUnElim insTail)
  
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
    Ins pairSalgebra v zeroExpr = Set.just Pair.zero
  :=
    rfl
  
  def insZeroIff v d:
    Ins pairSalgebra v zeroExpr d ↔ d = Pair.zero
  :=
    Iff.of_eq (insZeroEq v ▸ rfl)
  
  def insZero v:
    Ins pairSalgebra v zeroExpr Pair.zero
  :=
    (insZeroIff v Pair.zero).mpr rfl
  
  def insZeroElim v
    (s: Ins pairSalgebra v zeroExpr p)
  :
    p = Pair.zero
  :=
    (insZeroIff v p).mp s
  
  def insZeroElim.neq v
    (s: Ins pairSalgebra v zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (((insZeroIff v p).mp s).symm.trans eq)
  
  def insZeroElim.nope v
    (s: Ins pairSalgebra v zeroExpr (Pair.pair a b))
  :
    P
  :=
    False.elim (insZeroElim.neq v s a b rfl)
  
  def inwZeroEq v:
    Inw pairSalgebra v zeroExpr = Set.just Pair.zero
  :=
    rfl
  
  def inwZeroIff v d:
    Inw pairSalgebra v zeroExpr d ↔ d = Pair.zero
  :=
    Iff.of_eq (inwZeroEq v ▸ rfl)
  
  def inwZero v:
    Inw pairSalgebra v zeroExpr Pair.zero
  :=
    (inwZeroIff v Pair.zero).mpr rfl
  
  
  def inwZeroElim v
    (s: Inw pairSalgebra v zeroExpr p)
  :
    p = Pair.zero
  :=
    (insZeroIff v p).mp s
  
  def inwZeroElim.neq v
    (s: Inw pairSalgebra v zeroExpr p)
    a b
  :
    p ≠ Pair.pair a b
  :=
    fun eq =>
      Pair.noConfusion (((insZeroIff v p).mp s).symm.trans eq)
  
  def inwZeroElim.nope v
    (s: Inw pairSalgebra v zeroExpr (Pair.pair a b))
  :
    P
  :=
    False.elim (insZeroElim.neq v s a b rfl)
  
  
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
  
  def insPairElim v
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
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: Ins pairSalgebra v exprL pairL
    insR: Ins pairSalgebra v exprR pairR
  
  def insPairElim.ex v
    (s: Ins pairSalgebra v (pairExpr exprL exprR) pair)
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
  
  def insPairElim.notZero v
    (s: Ins pairSalgebra v (pairExpr exprL exprR) pair)
  :
    pair ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex v s).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def insPairElim.nope v
    (s: Ins pairSalgebra v (pairExpr exprL exprR) Pair.zero)
  :
    p
  :=
    (notZero v s rfl).elim
  
  
  structure InwPairElim
    (v: Valuation Pair)
    (exprL exprR: Expr)
    (pairL pairR: Pair): Prop
  where
    inwL: Inw pairSalgebra v exprL pairL
    inwR: Inw pairSalgebra v exprR pairR
  
  def inwPairElim v
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
  
  def inwPairElim.ex v
    (w: Inw pairSalgebra v (pairExpr exprL exprR) pair)
  :
    ∃ pairL pairR: Pair, InwPairElim.Ex v exprL exprR pair pairL pairR
  :=
    match pair with
    | Pair.zero =>
      Pair.noConfusion (w.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (inwPairElim v w).inwL
        insR := (inwPairElim v w).inwR
      }⟩
  
  def inwPairElim.notZero v
    (w: Inw pairSalgebra v (pairExpr exprL exprR) pair)
  :
    pair ≠ Pair.zero
  :=
    let ⟨_pairL, prop⟩ := (ex v w).unwrap
    let ⟨_pairR, prop⟩ := prop.unwrap
    
    prop.eq ▸ Pair.noConfusion
  
  def inwPairElim.nope v
    (w: Inw pairSalgebra v (pairExpr exprL exprR) Pair.zero)
  :
    P
  :=
    (notZero v w rfl).elim
  
  
  def insZthMember
    (s: Ins pairSalgebra v expr (Pair.pair a b))
    (xNotFree: ¬expr.IsFreeVar Set.empty x)
  :
    Ins pairSalgebra v (zthMember x expr) a
  :=
    let eqUpdated := Expr.interpretation.eqSwappedUnused
      pairSalgebra v v expr xNotFree a
    
    let sUpd:
      Ins pairSalgebra (v.update x a) expr (Pair.pair a b)
    :=
      by unfold Ins; exact eqUpdated ▸ s
    
    insArbUn ⟨
      ⟨Pair.pair a b,
        And.intro (insPair insBound insAny) sUpd⟩,
      insBound,
    ⟩
  
  def insFstMember
    (s: Ins pairSalgebra v expr (Pair.pair a b))
    (xNotFree: ¬expr.IsFreeVar Set.empty x)
  :
    Ins pairSalgebra v (fstMember x expr) b
  :=
    let eqUpdated := Expr.interpretation.eqSwappedUnused
      pairSalgebra v v expr xNotFree b
    
    let sUpd:
      Ins pairSalgebra (v.update x b) expr (Pair.pair a b)
    :=
      by unfold Ins; exact eqUpdated ▸ s
    
    insArbUn ⟨
      ⟨Pair.pair a b,
        And.intro (insPair insAny insBound) sUpd⟩,
      insBound,
    ⟩
  
  def insZthMemberElim
    (s: Ins pairSalgebra v (zthMember xA (var xB)) zth)
    (neq: xA ≠ xB)
  :
    ∃ fst, Ins pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairXaAny, pCondInsXbUpdated⟩⟩ := insCond
    let pCondInsXb: Ins pairSalgebra v xB pCond :=
      insFreeElim pCondInsXbUpdated neq
    
    match h: pCond with
    | Pair.zero => insPairElim.nope _ insPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := insPairElim _ insPairXaAny
      let eqPCondZth: pCondZth = pZth := insBoundEq insL
      let eqPZth: zth = pZth := insBoundEq insBody
      
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ h ▸ pCondInsXb⟩
  
  def inwZthMemberElim
    (s: Inw pairSalgebra v (zthMember xA (var xB)) zth)
    (neq: xA ≠ xB)
  :
    ∃ fst, Inw pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨pZth, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairXaAny, pCondInwXbUpdated⟩⟩ := inwCond
    let pCondInwXb: Inw pairSalgebra v xB pCond :=
      inwFreeElim pCondInwXbUpdated neq
    
    match h: pCond with
    | Pair.zero => inwPairElim.nope _ inwPairXaAny
    | Pair.pair pCondZth pCondFst =>
      let ⟨insL, _insR⟩ := inwPairElim _ inwPairXaAny
      let eqPCondZth: pCondZth = pZth := inwBoundEq insL
      let eqPZth: zth = pZth := inwBoundEq inwBody
      
      ⟨pCondFst, eqPZth ▸ eqPCondZth ▸ h ▸ pCondInwXb⟩
  
  def insFstMemberElim
    (s: Ins pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
  :
    ∃ zth, Ins pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨insCond, insBody⟩⟩ := s
    let ⟨pCond, ⟨insPairAnyXa, pCondInsXbUpdated⟩⟩ := insCond
    let pCondInsXb: Ins pairSalgebra v xB pCond :=
      insFreeElim pCondInsXbUpdated neq
    
    match h: pCond with
    | Pair.zero => insPairElim.nope _ insPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := insPairElim _ insPairAnyXa
      let eqPCondZth: pCondFst = pFst := insBoundEq insR
      let eqPZth: fst = pFst := insBoundEq insBody
      
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ h ▸ pCondInsXb⟩
  
  def inwFstMemberElim
    (s: Inw pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
  :
    ∃ zth, Inw pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨pFst, ⟨inwCond, inwBody⟩⟩ := s
    let ⟨pCond, ⟨inwPairAnyXa, pCondInwXbUpdated⟩⟩ := inwCond
    let pCondInsXb: Inw pairSalgebra v xB pCond :=
      inwFreeElim pCondInwXbUpdated neq
    
    match h: pCond with
    | Pair.zero => inwPairElim.nope _ inwPairAnyXa
    | Pair.pair pCondZth pCondFst =>
      let ⟨_insL, insR⟩ := inwPairElim _ inwPairAnyXa
      let eqPCondZth: pCondFst = pFst := inwBoundEq insR
      let eqPZth: fst = pFst := inwBoundEq inwBody
      
      ⟨pCondZth, eqPZth ▸ eqPCondZth ▸ h ▸ pCondInsXb⟩
  
  
  def insZthFstElim v
    (insZth: Ins pairSalgebra v (zthMember xA (var xB)) zth)
    (insFst: Ins pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: v xB = Set3.just d)
  :
    Ins pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, insChosenFst⟩ := insZthMemberElim insZth neq
    let ⟨chosenZth, insChosenZth⟩ := insFstMemberElim insFst neq
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inDefToEq d
        (isUnit ▸ insChosenFst)
        (isUnit ▸ insChosenZth)
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ insChosenZth
  
  def inwZthFstElim v
    (inwZth: Inw pairSalgebra v (zthMember xA (var xB)) zth)
    (inwFst: Inw pairSalgebra v (fstMember xA (var xB)) fst)
    (neq: xA ≠ xB)
    (isUnit: v xB = Set3.just d)
  :
    Inw pairSalgebra v xB (Pair.pair zth fst)
  :=
    let ⟨chosenFst, inwChosenFst⟩ := inwZthMemberElim inwZth neq
    let ⟨chosenZth, inwChosenZth⟩ := inwFstMemberElim inwFst neq
    
    let eq:
      Pair.pair zth chosenFst = Pair.pair chosenZth fst
    :=
      Set3.just.inPosToEq d
        (isUnit ▸ inwChosenFst)
        (isUnit ▸ inwChosenZth)
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ inwChosenZth
end PairExpr

namespace Pair
  def IsNatEncoding: Set Pair
  | zero => True
  | pair a b => (IsNatEncoding a) ∧ b = zero
  
  def NatEncoding := { p // IsNatEncoding p }
  
  def natDecode: (p: Pair) → Nat
  | zero => 0
  | pair a _ => Nat.succ (natDecode a)
  
  def natDecode.zeroEq: natDecode Pair.zero = 0 := rfl
  def natDecode.eqZero (eqZ: p = Pair.zero):
    natDecode p = 0
  :=
    eqZ ▸ natDecode.zeroEq
  
  def natDecode.succPredEq
    (a b: Pair)
  :
    natDecode (pair a b)
      =
    Nat.succ (natDecode a)
  :=
    rfl
  
  def natDecode.injEq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (eq: natDecode a = natDecode b)
  :
    a = b
  :=
    match a, b with
    | zero, zero => rfl
    | zero, pair bA bB =>
      let eqL: 0 = natDecode (pair bA bB) :=
        natDecode.zeroEq.symm.trans eq
      let eqR := natDecode.succPredEq bA bB
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, zero =>
      let eqL: 0 = natDecode (pair aA aB) :=
        natDecode.zeroEq.symm.trans eq.symm
      let eqR := natDecode.succPredEq aA aB
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, pair bA bB =>
      let eqPred: natDecode aA = natDecode bA :=
        Nat.noConfusion eq id
      let eqA: aA = bA :=
        natDecode.injEq isNatA.left isNatB.left eqPred
      let eqB: aB = bB :=
        isNatA.right.trans isNatB.right.symm
      
      congr (congr rfl eqA) eqB
  
  def natDecode.injNeq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (neq: a ≠ b)
  :
    natDecode a ≠ natDecode b
  :=
    (natDecode.injEq isNatA isNatB).contra neq
end Pair

namespace PairExpr
  open Pair
  open Expr
  open pairSignature
  
  def insNatExpr v n
  :
    Ins pairSalgebra v (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => insZero v
    | Nat.succ pred => insPair (insNatExpr v pred) (insZero v)
  
  def inwNatExpr v n
  :
    Inw pairSalgebra v (natExpr n) (fromNat n)
  :=
    match n with
    | Nat.zero => insZero v
    | Nat.succ pred => inwPair (inwNatExpr v pred) (inwZero v)
  
  def inwNatExprElim
    (w: Inw pairSalgebra v (natExpr n) p)
  :
    p = fromNat n
  :=
    match n, p with
    | 0, _ => insZeroElim v w ▸ rfl
    | Nat.succ _, zero => inwPairElim.nope v w
    | Nat.succ _, pair _ _ =>
      let ⟨l, r⟩ := inwPairElim _ w
      (inwNatExprElim l) ▸ (inwZeroElim _ r) ▸ rfl
  
  def insNatExprElim
    (s: Ins pairSalgebra v (natExpr n) p)
  :
    p = fromNat n
  :=
    inwNatExprElim s.toInw
  
  def inwNatExprElimDecode
    (w: Inw pairSalgebra v (natExpr n) p)
  :
    natDecode p = n
  :=
    match n, p with
    | 0, _ => insZeroElim v w ▸ rfl
    | Nat.succ _, zero => inwPairElim.nope v w
    | Nat.succ _, pair _ _ =>
      inwNatExprElimDecode (inwPairElim _ w).inwL  ▸ rfl
  
  def insNatExprElimDecode
    (s: Ins pairSalgebra v (natExpr n) p)
  :
    natDecode p = n
  :=
    inwNatExprElimDecode s.toInw
  
end PairExpr


namespace wfm
  def InsWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins salg (dl.wellFoundedModel salg) d
  
  def InwWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw salg (dl.wellFoundedModel salg) d
  
  def insWfmDef.toInsWfm
    (s: InsWfm salg dl (dl.getDef n) d)
  :
    InsWfm salg dl n d
  := by
    unfold InsWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ s
  
  def insWfm.toInsWfmDef
    {n: Nat}
    (s: InsWfm salg dl n d)
  :
    InsWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v n = dl.interpretation salg v v n
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v n).defMem d from eqAtN ▸ s
  
  def inwWfmDef.toInwWfm
    (w: InwWfm salg dl (dl.getDef n) d)
  :
    InwWfm salg dl n d
  := by
    unfold InwWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ w
  
  def inwWfm.toInwWfmDef
    {n: Nat}
    (w: InwWfm salg dl n d)
  :
    InwWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v n = dl.interpretation salg v v n
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v n).posMem d from eqAtN ▸ w
  
end wfm
