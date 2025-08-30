import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Valuation

namespace Etst


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
    Valuation.in_update_bound_defMem rfl
  
  def inwBound:
    Inw salg b (Valuation.update c x dBound) (var x) dBound
  :=
    Valuation.in_update_bound_posMem rfl
  
  def insBoundElim
    (s: Ins salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.eq_of_in_update_bound_defMem s
  
  def inwBoundElim
    (w: Inw salg b (Valuation.update c x dBound) (var x) d)
  :
    d = dBound
  :=
    Valuation.eq_of_in_update_bound_posMem w
  
  def insFree
    {d: salg.D}
    (ins: Ins salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b (c.update xB dBound) (var x) d
  :=
    Valuation.in_update_free_defMem neq ins
  
  def inwFree
    {d: salg.D}
    (inw: Inw salg b c (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b (Valuation.update c xB dBound) (var x) d
  :=
    Valuation.in_update_free_posMem neq inw
  
  def insFreeElim
    (s: Ins salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Ins salg b c (var x) d
  :=
    Valuation.in_orig_of_neq_defMem s neq
  
  def inwFreeElim
    (w: Inw salg b (Valuation.update c xB dBound) (var x) d)
    (neq: xB ≠ x)
  :
    Inw salg b c (var x) d
  :=
    Valuation.in_orig_of_neq_posMem w neq


  def insAny: Ins salg b c anyExpr d := insArbUn _ insBound
  def inwAny: Inw salg b c anyExpr d := inwArbUn _ inwBound
  
  def ninsNone: ¬Ins salg b c noneExpr d := ninsCpl c inwAny
  def ninwNone: ¬Inw salg b c noneExpr d := ninwCpl c insAny
  
  
  abbrev InsWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins2 salg (dl.wfm salg) d
  
  abbrev InwWfm
    (salg: Salgebra sig)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw2 salg (dl.wfm salg) d
  
  
  def InsWfm.of_ins_def
    (s: InsWfm salg dl (dl.getDef n) d)
  :
    InsWfm salg dl n d
  := by
    unfold InsWfm;
    exact (DefList.wfm_isModel salg dl) ▸ s
  
  def InwWfm.of_inw_def
    (w: InwWfm salg dl (dl.getDef n) d)
  :
    InwWfm salg dl n d
  := by
    unfold InwWfm;
    exact (DefList.wfm_isModel salg dl) ▸ w
  
  
  def InsWfm.ins_def_of_ins
    {n: Nat}
    (s: InsWfm salg dl n d)
  :
    InsWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wfm salg
    
    let eqAtN: v n = dl.interpretation salg v v n :=
      congr (DefList.wfm_isModel salg dl) rfl
    
    show (dl.interpretation salg v v n).defMem d from eqAtN ▸ s
  
  def InsWfm.inw_def_of_inw
    {n: Nat}
    (w: InwWfm salg dl n d)
  :
    InwWfm salg dl (dl.getDef n) d
  :=
    let v := dl.wfm salg
    
    let eqAtN:
      v n = dl.interpretation salg v v n
    :=
      congr (DefList.wfm_isModel salg dl) rfl

    show (dl.interpretation salg v v n).posMem d from eqAtN ▸ w
end Expr
