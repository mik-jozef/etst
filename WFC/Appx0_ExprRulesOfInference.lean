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

import WFC.Ch4_Operators
import WFC.Ch5_PairSalgebra


namespace Expr
  -- `anyExpr` contains all elements, under any valuation.
  def anyExpr [x: Inhabited Var]: Expr Var sig :=
    Expr.arbUn x.default x.default
  
  -- `noneExpr` contains no elements, under any valuation.
  def noneExpr [Inhabited Var]: Expr Var sig := Expr.cpl anyExpr
  
  
  @[reducible] def Ins
    (salg: Salgebra sig)
    (b: Valuation Var salg.D)
    (c: Valuation Var salg.D)
    (expr: Expr Var sig)
    (d: salg.D)
  :
    Prop
  :=
    d ∈ (expr.interpretation salg b c).defMem
  
  def Inw
    (salg: Salgebra sig)
    (b: Valuation Var salg.D)
    (c: Valuation Var salg.D)
    (expr: Expr Var sig)
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
    (v: Valuation Var salg.D)
    (expr: Expr Var sig)
    (d: salg.D)
  :=
    Ins salg v v expr d
  
  def Inw2
    (salg: Salgebra sig)
    (v: Valuation Var salg.D)
    (expr: Expr Var sig)
    (d: salg.D)
  :=
    Inw salg v v expr d
  
  
  def insArbUn
    dBound
    {x: Var}
    (s: Ins salg (b.update x dBound) (c.update x dBound) body d)
  :
    Ins salg b c (Expr.arbUn x body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    dBound
    {x: Var}
    (s: Inw salg (b.update x dBound) (c.update x dBound) body d)
  :
    Inw salg b c (Expr.arbUn x body) d
  :=
    ⟨dBound, s⟩
  
  
  def insArbUnElim
    {x: Var}
    (s: Ins salg b c (Expr.arbUn x body) d)
  :
    ∃ dBound,
      Ins salg (b.update x dBound) (c.update x dBound) body d
  :=
    s
  
  def inwArbUnElim
    {x: Var}
    (s: Inw salg b c (Expr.arbUn x body) d)
  :
    ∃ dBound,
      Inw salg (b.update x dBound) (c.update x dBound) body d
  :=
    s
  
  
  def insArbIr
    {salg: Salgebra sig}
    {b c: Valuation Var salg.D}
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
    {b c: Valuation Var salg.D}
    {d: salg.D}
    (s:
      ∀ dBound,
        Inw salg (b.update x dBound) (c.update x dBound) body d)
  :
    Inw salg b c (Expr.arbIr x body) d
  :=
    fun d => s d
  
  
  def insArbIrElim
    {x: Var}
    (s: Ins salg b c (Expr.arbIr x body) d)
    (dBound: salg.D)
  :
    Ins salg (b.update x dBound) (c.update x dBound) body d
  :=
    s dBound
  
  def inwArbIrElim
    {x: Var}
    (s: Inw salg b c (Expr.arbIr x body) d)
    (dBound: salg.D)
  :
    Inw salg (b.update x dBound) (c.update x dBound) body d
  :=
    s dBound
  
  
  def insCpl
    (c: Valuation Var salg.D)
    (w: ¬Inw salg b b expr d)
  :
    Ins salg b c (Expr.cpl expr) d
  :=
    w
  
  def inwCpl
    (c: Valuation Var salg.D)
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
    (c: Valuation Var salg.D)
    (w: Inw salg b b expr d)
  :
    ¬Ins salg b c (Expr.cpl expr) d
  :=
    fun ins => ins w
  
  def ninwCpl
    (c: Valuation Var salg.D)
    (s: Ins salg b b expr d)
  :
    ¬Inw salg b c (Expr.cpl expr) d
  :=
    fun inw => inw s
  
  
  
  def insBound {x: Var}:
    Ins salg b (Valuation.update c x dBound) (var x) dBound
  :=
    Valuation.update.inEq.defMem c x dBound
  
  def inwBound {x: Var}:
    Inw salg b (Valuation.update c x dBound) (var x) dBound
  :=
    Valuation.update.inEq.posMem c x dBound
  
  def insBoundElim
    {x: Var}
    (s: Ins salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inDef.eq s
  
  def inwBoundElim
    {x: Var}
    (w: Inw salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.update.inPos.eq w
  
  def insFree
    {xB: Var}
    {d: salg.D}
    (ins: Ins salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b (c.update xB dBound) (var x) d
  :=
    Valuation.update.inNeq.defMem c neq ins
  
  def inwFree
    {xB: Var}
    {d: salg.D}
    (isPos: Inw salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b (Valuation.update c xB dBound) (var x) d
  :=
    Valuation.update.inNeq.posMem c neq isPos
  
  def insFreeElim
    {salg: Salgebra sig}
    {b c: Valuation Var salg.D}
    {d dBound: salg.D}
    (s: Ins salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b c (var x) d
  := show
    (c x).defMem d
  from
    Valuation.update.inNeqElim.defMem s neq
  
  def inwFreeElim
    {xB: Var}
    (w: Inw salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b c (var x) d
  := show
    (c x).posMem d
  from
    Valuation.update.inNeqElim.posMem w neq
  
  
  def insAny
    [Inhabited Var]
  :
    Ins salg b c (anyExpr (Var := Var)) d
  :=
    insArbUn _ insBound
  
  def inwAny
    [Inhabited Var]
  :
    Inw salg b c (anyExpr (Var := Var)) d
  :=
    inwArbUn _ inwBound
  
  def ninsNone
    [Inhabited Var]
  :
    ¬Ins salg b c (noneExpr (Var := Var)) d
  :=
    ninsCpl c inwAny
  
  def ninwNone
    [Inhabited Var]
  :
    ¬Inw salg b c (noneExpr (Var := Var)) d
  :=
    ninwCpl c insAny
  
  
  def InsWfm
    (salg: Salgebra sig)
    (dl: DefList Var sig)
    (expr: Expr Var sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins2 salg (dl.wellFoundedModel salg) d
  
  def InwWfm
    (salg: Salgebra sig)
    (dl: DefList Var sig)
    (expr: Expr Var sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw2 salg (dl.wellFoundedModel salg) d
  
  
  def insWfmDefToIns
    {x: Var}
    (s: InsWfm salg dl (dl.getDef x) d)
  :
    InsWfm salg dl x d
  := by
    unfold InsWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ s
  
  def inwWfmDefToInw
    {x: Var}
    (w: InwWfm salg dl (dl.getDef x) d)
  :
    InwWfm salg dl x d
  := by
    unfold InwWfm;
    exact (DefList.wellFoundedModel.isModel salg dl) ▸ w
  
  
  def insWfmToInsDef
    {x: Var}
    (s: InsWfm salg dl x d)
  :
    InsWfm salg dl (dl.getDef x) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v x = dl.interpretation salg v v x
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v x).defMem d from eqAtN ▸ s
  
  def inwWfmToInwDef
    {x: Var}
    (w: InwWfm salg dl x d)
  :
    InwWfm salg dl (dl.getDef x) d
  :=
    let v := dl.wellFoundedModel salg
    
    let eqAtN:
      v x = dl.interpretation salg v v x
    :=
      congr (DefList.wellFoundedModel.isModel salg dl) rfl
    
    show (dl.interpretation salg v v x).posMem d from eqAtN ▸ w
end Expr


def wfmAtEq
  (dl: DefList Var sig)
  (salg: Salgebra sig)
  (x: Var)
:
  dl.wellFoundedModel salg x
    =
  dl.interpretation salg (dl.wellFoundedModel salg) (dl.wellFoundedModel salg) x
:=
  congr (DefList.wellFoundedModel.isModel salg dl) rfl
