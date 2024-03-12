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
    dBound
    (s: Ins salg (v.update x dBound) body d)
  :
    Ins salg v (Expr.Un x body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    dBound
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
  
  
  def insIr
    (l: Ins salg v exprL d)
    (r: Ins salg v exprR d)
  :
    Ins salg v (Expr.ir exprL exprR) d
  :=
    ⟨l, r⟩
  
  def inwIr
    (l: Inw salg v exprL d)
    (r: Inw salg v exprR d)
  :
    Inw salg v (Expr.ir exprL exprR) d
  :=
    ⟨l, r⟩
  
  def insIrElim
    (s: Ins salg v (Expr.ir exprL exprR) d)
  :
    And
      (Ins salg v exprL d)
      (Ins salg v exprR d)
  :=
    s
  
  def inwIrElim
    (s: Inw salg v (Expr.ir exprL exprR) d)
  :
    And
      (Inw salg v exprL d)
      (Inw salg v exprR d)
  :=
    s
  
  
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
  
  def insBoundElim
    {v: Valuation salg.D}
    (s: Ins salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inDef.eq s
  
  def inwBoundElim
    {v: Valuation salg.D}
    (w: Inw salg (v.update x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inPos.eq w
  
  def insFree
    {v: Valuation salg.D}
    {d: salg.D}
    (ins: Ins salg v (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg (v.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.defMem v neq ins
  
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
  
  
  def insAny: Ins salg v anyExpr d := insArbUn _ insBound
  def inwAny: Inw salg v anyExpr d := inwArbUn _ inwBound
  
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
    
    insArbUn _ ⟨⟨dBound, ⟨inUpdated, insDomain⟩⟩, insBody⟩
  
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
      insBoundElim dInIr.property.left
    
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
      inwBoundElim dInIr.property.left
    
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
  
  instance ofNat n: OfNat Pair n where
    ofNat := Pair.fromNat n
  
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
    (pair pairL pairR: Pair): Prop
  where
    eq: pair = Pair.pair pairL pairR
    insL: Ins pairSalgebra v exprL pairL
    insR: Ins pairSalgebra v exprR pairR
  
  def insPairElim.ex
    (s: Ins pairSalgebra v (pairExpr exprL exprR) pair)
  :
    ∃ pairL pairR: Pair, InsPairElim.Ex v exprL exprR pair pairL pairR
  :=
    match pair with
    | Pair.zero =>
      Pair.noConfusion (s.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (insPairElim s).insL
        insR := (insPairElim s).insR
      }⟩
  
  def insPairElim.notZero
    (s: Ins pairSalgebra v (pairExpr exprL exprR) pair)
  :
    pair ≠ Pair.zero
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
    (w: Inw pairSalgebra v (pairExpr exprL exprR) pair)
  :
    ∃ pairL pairR: Pair, InwPairElim.Ex v exprL exprR pair pairL pairR
  :=
    match pair with
    | Pair.zero =>
      Pair.noConfusion (w.unwrap.property.unwrap.property)
    | Pair.pair a b => ⟨a, b, {
        eq := rfl
        insL := (inwPairElim w).inwL
        insR := (inwPairElim w).inwR
      }⟩
  
  def inwPairElim.notZero
    (w: Inw pairSalgebra v (pairExpr exprL exprR) pair)
  :
    pair ≠ Pair.zero
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
      Set3.just.inDefToEq d
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
      Set3.just.inPosToEq d
        (isUnit ▸ (inwFreeElim inwChosenFst neq))
        (isUnit ▸ (inwFreeElim inwChosenZth neq))
    
    let eqR: zth = chosenZth := Pair.noConfusion eq fun eq _ => eq
    
    eqR ▸ (inwFreeElim inwChosenZth neq)
    
    
    def insCall
      (insFn: Ins pairSalgebra (v.update x b) fn (Pair.pair a b))
      (insArg: Ins pairSalgebra (v.update x b) arg a)
    :
      Ins pairSalgebra v (callExpr x fn arg) b
    :=
      insFstMember (insIr insFn (insPair insArg insAny))
    
    def inwCall
      (inwFn: Inw pairSalgebra (v.update x b) fn (Pair.pair a b))
      (inwArg: Inw pairSalgebra (v.update x b) arg a)
    :
      Inw pairSalgebra v (callExpr x fn arg) b
    :=
      inwFstMember (inwIr inwFn (inwPair inwArg inwAny))
    
    
    def insCallElim
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
    
    def inwCallElim
      (s: Inw pairSalgebra v (callExpr x fn arg) b)
    :
      ∃ a,
        And
          (Inw pairSalgebra (v.update x b) fn (Pair.pair a b))
          (Inw pairSalgebra (v.update x b) arg a)
    :=
      let ⟨zth, inwIr⟩ := inwFstMemberElim s
      let ⟨inwFn, inwP⟩ := inwIrElim inwIr
      
      ⟨zth, And.intro inwFn (inwPairElim inwP).inwL⟩
    
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
  
  def natDecode.eqZeroOfEqZero
    (eqZero: natDecode p = 0)
  :
    p = zero
  :=
    match p with
    | zero => rfl
    | pair _ _ => Nat.noConfusion eqZero
  
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
  
  
  def fromNat.isNatEncoding (n: Nat):
    IsNatEncoding (fromNat n)
  :=
    match n with
    | Nat.zero => trivial
    | Nat.succ pred => And.intro (isNatEncoding pred) rfl
  
  def natEncode.fromNatEq (n: Nat):
    natDecode (fromNat n) = n
  :=
    match n with
    | Nat.zero => rfl
    | Nat.succ pred => congr rfl (fromNatEq pred)
  
  
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
    | 0, _ => inwZeroElim w ▸ rfl
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
  
  def inwNatExprElimDecode
    (w: Inw pairSalgebra v (natExpr n) p)
  :
    natDecode p = n
  :=
    match n, p with
    | 0, _ => inwZeroElim w ▸ rfl
    | Nat.succ _, zero => inwPairElim.nope w
    | Nat.succ _, pair _ _ =>
      inwNatExprElimDecode (inwPairElim w).inwL  ▸ rfl
  
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
