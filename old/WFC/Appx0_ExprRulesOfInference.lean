/-
  Appendix 0: Rules of Inference for Expressions
  
  Defines basic rules of inference for expressions.
  Since we're working in a three-valued setting, we
  have two kinds of membership relations -- strong
  membership and weak membership (See
  @file:`Main/Set3.lean` for more).
  
  These rules are analogous to the rules of inference
  for classical logic, but are applied to expressions
  from @file:`Main/Expr.lean`.
-/

import old.WFC.Ch4_Operators
import old.WFC.Ch5_PairSalgebra


namespace Expr
  -- `anyExpr` contains all elements, under any valuation.
  def anyExpr: Expr sig := Expr.arbUn 0 0
  -- `noneExpr` contains no elements, under any valuation.
  def noneExpr: Expr sig := Expr.cpl anyExpr
  
  
  def Ins
    (salg: Salgebra sig)
    (b: Valuation salg.D)
    (c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg b c).defMem
  
  def Inw
    (salg: Salgebra sig)
    (b: Valuation salg.D)
    (c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg b c).posMem
  
  def Ins.toInw (s: Ins salg b c expr d):
    Inw salg b c expr d
  :=
    s.toPos
  
  
  def Ins2
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Ins salg v v expr d
  
  def Inw2
    (salg: Salgebra sig)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Inw salg v v expr d
  
  
  def insArbUn
    dBound
    (s: Ins salg (b.update x dBound) (c.update x dBound) body d)
  :
    Ins salg b c (Expr.arbUn x body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    dBound
    (s: Inw salg (b.update x dBound) (c.update x dBound) body d)
  :
    Inw salg b c (Expr.arbUn x body) d
  :=
    ⟨dBound, s⟩
  
  
  def insArbUnElim
    (s: Ins salg b c (Expr.arbUn x body) d)
  :
    ∃ dBound,
      Ins salg (b.update x dBound) (c.update x dBound) body d
  :=
    s
  
  def inwArbUnElim
    (s: Inw salg b c (Expr.arbUn x body) d)
  :
    ∃ dBound,
      Inw salg (b.update x dBound) (c.update x dBound) body d
  :=
    s
  
  
  def insArbIr
    {salg: Salgebra sig}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s:
      ∀ dBound,
        Ins salg (b.update x dBound) (c.update x dBound) body d)
  :
    Ins salg b c (Expr.arbIr x body) d
  :=
    fun d => s d
  
  def inwArbIr
    {salg: Salgebra sig}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s:
      ∀ dBound,
        Inw salg (b.update x dBound) (c.update x dBound) body d)
  :
    Inw salg b c (Expr.arbIr x body) d
  :=
    fun d => s d
  
  
  def insArbIrElim
    (s: Ins salg b c (Expr.arbIr x body) d)
    (dBound: salg.D)
  :
    Ins salg (b.update x dBound) (c.update x dBound) body d
  :=
    s dBound
  
  def inwArbIrElim
    (s: Inw salg b c (Expr.arbIr x body) d)
    (dBound: salg.D)
  :
    Inw salg (b.update x dBound) (c.update x dBound) body d
  :=
    s dBound
  
  
  def insCpl
    (c: Valuation salg.D)
    (w: ¬Inw salg b b expr d)
  :
    Ins salg b c (Expr.cpl expr) d
  :=
    w
  
  def inwCpl
    (c: Valuation salg.D)
    (s: ¬Ins salg b b expr d)
  :
    Inw salg b c (Expr.cpl expr) d
  :=
    s
  
  def insCplElim
    (s: Ins salg b c (Expr.cpl expr) d)
  :
    ¬Inw salg b b expr d
  :=
    s
  
  def inwCplElim
    (w: Inw salg b c (Expr.cpl expr) d)
  :
    ¬Ins salg b b expr d
  :=
    w
  
  
  def ninsCpl
    (c: Valuation salg.D)
    (w: Inw salg b b expr d)
  :
    ¬Ins salg b c (Expr.cpl expr) d
  :=
    fun ins => ins w
  
  def ninwCpl
    (c: Valuation salg.D)
    (s: Ins salg b b expr d)
  :
    ¬Inw salg b c (Expr.cpl expr) d
  :=
    fun inw => inw s
  
  
  
  def insBound:
    Ins salg b (Valuation.update c x dBound) (var x) dBound
  :=
    Valuation.update.inEq.defMem c x dBound
  
  def inwBound:
    Inw salg b (Valuation.update c x dBound) (var x) dBound
  :=
    Valuation.update.inEq.posMem c x dBound
  
  def insBoundElim
    (s: Ins salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inDef.eq s
  
  def inwBoundElim
    (w: Inw salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inPos.eq w
  
  def insFree
    {d: salg.D}
    (ins: Ins salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b (c.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.defMem c neq ins
  
  def inwFree
    {d: salg.D}
    (isPos: Inw salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b (Valuation.update c xB dBound) (var x) d
  :=
    Valuation.update.inNeq.posMem c neq isPos
  
  def insFreeElim
    (s: Ins salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b c (var x) d
  :=
    Valuation.update.inNeqElim.defMem s neq
  
  def inwFreeElim
    (w: Inw salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b c (var x) d
  :=
    Valuation.update.inNeqElim.posMem w neq
  
  
  def insAny: Ins salg b c anyExpr d := insArbUn _ insBound
  def inwAny: Inw salg b c anyExpr d := inwArbUn _ inwBound
  
  def ninsNone: ¬Ins salg b c noneExpr d := ninsCpl c inwAny
  def ninwNone: ¬Inw salg b c noneExpr d := ninwCpl c insAny
  
  
  def InsWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins2 salg (dl.wellFoundedModel salg) d
  
  def InwWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw2 salg (dl.wellFoundedModel salg) d
  
  
  def insWfmDefToIns
    (s: InsWfm salg dl (dl.getDef n) d)
  :
    InsWfm salg dl n d
  := by
    unfold InsWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ s
  
  def inwWfmDefToInw
    (w: InwWfm salg dl (dl.getDef n) d)
  :
    InwWfm salg dl n d
  := by
    unfold InwWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ w
  
  
  def insWfmToInsDef
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
  
  def inwWfmToInwDef
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
end Expr


def wfmAtEq
  (dl: DefList sig)
  (salg: Salgebra sig)
  (x: Nat)
:
  dl.wellFoundedModel salg x
    =
  dl.interpretation salg (dl.wellFoundedModel salg) (dl.wellFoundedModel salg) x
:=
  congr (DefList.wellFoundedModel.isModel salg dl) rfl
