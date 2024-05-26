import Operators
import ExampleWFCs
import PairDepthDictOrder

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
  
  
  -- "in strong". `d "∈s" t` iff `d ∈ t.defMem`. See also `Inw`.
  def Ins
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg v v).defMem
  
  -- "in weak". `d "∈s" t` iff `d ∈ t.posMem`. See also `Ins`.
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
  
  
  def insArbIr
    {salg: Salgebra sig}
    {v: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Ins salg (v.update x dBound) body d)
  :
    Ins salg v (Expr.Ir x body) d
  :=
    fun d => s d
  
  def inwArbIr
    {salg: Salgebra sig}
    {v: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Inw salg (v.update x dBound) body d)
  :
    Inw salg v (Expr.Ir x body) d
  :=
    fun d => s d
  
  
  def insArbIrElim
    (s: Ins salg v (Expr.Ir x body) d)
    (dBound: salg.D)
  :
    Ins salg (v.update x dBound) body d
  :=
    s dBound
  
  def inwArbIrElim
    (s: Inw salg v (Expr.Ir x body) d)
    (dBound: salg.D)
  :
    Inw salg (v.update x dBound) body d
  :=
    s dBound
  
  
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
  
  
  def insIfThen
    {cond: Expr sig}
    (insCond: Ins salg v cond c)
    (insBody: Ins salg v body d)
  :
    Ins salg v (Expr.ifThen cond body) d
  :=
    ⟨⟨c, insCond⟩, insBody⟩
  
  def inwIfThen
    {cond: Expr sig}
    (insCond: Inw salg v cond c)
    (insBody: Inw salg v body d)
  :
    Inw salg v (Expr.ifThen cond body) d
  :=
    ⟨⟨c, insCond⟩, insBody⟩
  
  
  def insIfThenElim
    {cond: Expr sig}
    (s: Ins salg v (Expr.ifThen cond body) d)
  :
    And
      (∃c, Ins salg v cond c)
      (Ins salg v body d)
  :=
    let ⟨exCond, insBody⟩ := s
    
    And.intro exCond insBody
  
  def inwIfThenElim
    {cond: Expr sig}
    (s: Inw salg v (Expr.ifThen cond body) d)
  :
    And
      (∃c, Inw salg v cond c)
      (Inw salg v body d)
  :=
    let ⟨exCond, insBody⟩ := s
    
    And.intro exCond insBody
  
  
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
    (isPos: Inw salg v (var x) d)
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
  
  def inwUnDom
    (inwDomain: Inw salg (v.update x dBound) domain dBound)
    (inwBody: Inw salg (v.update x dBound) body d)
  :
    Inw salg v (unionExpr x domain body) d
  :=
    let inUpdated: ((v.update x dBound) x).posMem dBound :=
      Valuation.update.inEq.posMem v x dBound
    
    inwArbUn _ ⟨⟨dBound, ⟨inUpdated, inwDomain⟩⟩, inwBody⟩
  
  
  -- I wish Lean supported anonymous structures.
  -- And also non-Prop-typed members of prop structures
  -- (under the condition that any two instances are only
  -- allowed to contain the same instance). We have global
  -- choice anyway!
  structure InsUnDomElim
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
    ∃ dBound, InsUnDomElim salg v x dBound domain body d
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
  
  structure InwUnDomElim
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (x: Nat)
    (dBound: salg.D)
    (domain body: Expr sig)
    (d: salg.D): Prop
  where
    inwDomain: Inw salg (v.update x dBound) domain dBound
    inwBody: Inw salg (v.update x dBound) body d
  
  def inwUnDomElim
    (insUnDom: Inw salg v (unionExpr x domain body) d)
  :
    ∃ dBound, InwUnDomElim salg v x dBound domain body d
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
        inwDomain := insDomain
        inwBody := dBound.property.right
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
  
  
  def InsFinUnElim
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (d: salg.D)
    (P: Prop)
  :
    List (Expr sig) → Prop
  | List.nil => P
  | List.cons head tail =>
    (Ins salg v head d → P) → InsFinUnElim salg v d P tail
  
  def InsFinUnElim.ofP
    (list: List (Expr sig))
    (p: P)
  :
    InsFinUnElim salg v d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def insFinUnElim
    (s: Ins salg v (finUnExpr list) d)
  :
    InsFinUnElim salg v d P list
  :=
    match list with
    | List.nil => False.elim (ninsNone s)
    | List.cons _head tail =>
      (insUnElim s).elim
        (fun insHead insHeadToP =>
          InsFinUnElim.ofP tail (insHeadToP insHead))
        (fun insTail _ => insFinUnElim insTail)
  
  
  def InwFinUnElim
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (d: salg.D)
    (P: Prop)
  :
    List (Expr sig) → Prop
  | List.nil => P
  | List.cons head tail =>
    (Inw salg v head d → P) → InwFinUnElim salg v d P tail
  
  def inwFinUnElim.ofP
    (list: List (Expr sig))
    (p: P)
  :
    InwFinUnElim salg v d P list
  :=
    match list with
    | List.nil => p
    | List.cons _head tail => fun _ => ofP tail p
  
  def inwFinUnElim
    (s: Inw salg v (finUnExpr list) d)
  :
    InwFinUnElim salg v d P list
  :=
    match list with
    | List.nil => False.elim (ninwNone s)
    | List.cons _head tail =>
      (inwUnElim s).elim
        (fun inwHead insHeadToP =>
          inwFinUnElim.ofP tail (insHeadToP inwHead))
        (fun insTail _ => inwFinUnElim insTail)
  
end Expr
