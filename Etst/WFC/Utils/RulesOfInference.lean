import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Valuation

namespace Etst


namespace Expr
  -- `any` contains all elements, under any valuation.
  def any: Expr sig := Expr.arbUn (.bvar 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr sig := Expr.cpl any


  abbrev Ins
    (salg: Salgebra sig)
    (bv: List salg.D)
    (b: Valuation salg.D)
    (c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    (expr.interpretation salg bv b c).defMem d
  
  abbrev Inw
    (salg: Salgebra sig)
    (bv: List salg.D)
    (b: Valuation salg.D)
    (c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    (expr.interpretation salg bv b c).posMem d
  
  def Ins.toInw (s: Ins salg bv b c expr d):
    Inw salg bv b c expr d
  :=
    s.toPos
  
  
  def Ins2
    (salg: Salgebra sig)
    (bv: List salg.D)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Ins salg bv v v expr d
  
  def Inw2
    (salg: Salgebra sig)
    (bv: List salg.D)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Inw salg bv v v expr d
  
  
  def insArbUn
    dBound
    (s: Ins salg (dBound :: bv) b c body d)
  :
    Ins salg bv b c (arbUn body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    dBound
    (s: Inw salg (dBound :: bv) b c body d)
  :
    Inw salg bv b c (arbUn body) d
  :=
    ⟨dBound, s⟩
  
  
  def insArbUnElim
    (s: Ins salg bv b c (arbUn body) d)
  :
    ∃ dBound, Ins salg (dBound :: bv) b c body d
  :=
    s
  
  def inwArbUnElim
    (s: Inw salg bv b c (arbUn body) d)
  :
    ∃ dBound, Inw salg (dBound :: bv) b c body d
  :=
    s
  
  
  def insArbIr
    {salg: Salgebra sig}
    {bv: List salg.D}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Ins salg (dBound :: bv) b c body d)
  :
    Ins salg bv b c (arbIr body) d
  :=
    fun d => s d
  
  def inwArbIr
    {salg: Salgebra sig}
    {bv: List salg.D}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Inw salg (dBound :: bv) b c body d)
  :
    Inw salg bv b c (arbIr body) d
  :=
    fun d => s d
  
  
  def insArbIrElim
    (s: Ins salg bv b c (arbIr body) d)
    (dBound: salg.D)
  :
    Ins salg (dBound :: bv) b c body d
  :=
    s dBound
  
  def inwArbIrElim
    (s: Inw salg bv b c (arbIr body) d)
    (dBound: salg.D)
  :
    Inw salg (dBound :: bv) b c body d
  :=
    s dBound
  
  
  def insCpl
    (c: Valuation salg.D)
    (w: ¬Inw salg bv b b expr d)
  :
    Ins salg bv b c (cpl expr) d
  :=
    w
  
  def inwCpl
    (c: Valuation salg.D)
    (s: ¬Ins salg bv b b expr d)
  :
    Inw salg bv b c (cpl expr) d
  :=
    s
  
  def insCplElim
    (s: Ins salg bv b c (cpl expr) d)
  :
    ¬Inw salg bv b b expr d
  :=
    s
  
  def inwCplElim
    (w: Inw salg bv b c (cpl expr) d)
  :
    ¬Ins salg bv b b expr d
  :=
    w
  
  
  def ninsCpl
    (c: Valuation salg.D)
    (w: Inw salg bv b b expr d)
  :
    ¬Ins salg bv b c (cpl expr) d
  :=
    fun ins => ins w
  
  def ninwCpl
    (c: Valuation salg.D)
    (s: Ins salg bv b b expr d)
  :
    ¬Inw salg bv b c (cpl expr) d
  :=
    fun inw => inw s
  
  
  
  def insBound
    {bv: List salg.D}
    {dBound: salg.D}
    (insBv: bv[x]? = some dBound)
  :
    Ins salg bv b c (bvar x) dBound
  := by
    rw [Ins, interpretation, insBv]
    rfl
  
  def inwBound
    {bv: List salg.D}
    {dBound: salg.D}
    (insBv: bv[x]? = some dBound)
  :
    Inw salg bv b c (bvar x) dBound
  := by
    rw [Inw, interpretation, insBv]
    rfl
  
  def insBoundElim
    (s: Ins salg bv b c (bvar x) d)
    (eqBound: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [Ins, interpretation, eqBound] at s
    exact s
  
  def inwBoundElim
    (w: Inw salg bv b c (bvar x) d)
    (eqBound: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [Inw, interpretation, eqBound] at w
    exact w
  

  def insAny: Ins salg bv b c any d := insArbUn d (insBound rfl)
  def inwAny: Inw salg bv b c any d := inwArbUn d (inwBound rfl)
  
  def ninsNone: ¬Ins salg bv b c none d := ninsCpl c inwAny
  def ninwNone: ¬Inw salg bv b c none d := ninwCpl c insAny
  
  
  abbrev InsWfm
    (salg: Salgebra sig)
    (bv: List salg.D)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins2 salg bv (dl.wfm salg) d
  
  abbrev InwWfm
    (salg: Salgebra sig)
    (bv: List salg.D)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw2 salg bv (dl.wfm salg) d
  
  
  def InsWfm.of_ins_def
    (s: InsWfm salg [] dl (dl.getDef x) d)
  :
    InsWfm salg [] dl (.var x) d
  := by
    unfold InsWfm;
    exact (DefList.wfm_isModel salg dl) ▸ s
  
  def InwWfm.of_inw_def
    (w: InwWfm salg [] dl (dl.getDef x) d)
  :
    InwWfm salg [] dl (.var x) d
  := by
    unfold InwWfm;
    exact (DefList.wfm_isModel salg dl) ▸ w
  
  
  def InsWfm.ins_def_of_ins
    (s: InsWfm salg [] dl (.var x) d)
  :
    InsWfm salg [] dl (dl.getDef x) d
  :=
    let v := dl.wfm salg
    
    let eqAtN: v x = dl.interpretation salg v v x :=
      congr (DefList.wfm_isModel salg dl) rfl
    
    show (dl.interpretation salg v v x).defMem d from eqAtN ▸ s
  
  def InsWfm.inw_def_of_inw
    (w: InwWfm salg [] dl (.var x) d)
  :
    InwWfm salg [] dl (dl.getDef x) d
  :=
    let v := dl.wfm salg
    
    let eqAtN:
      v x = dl.interpretation salg v v x
    :=
      congr (DefList.wfm_isModel salg dl) rfl

    show (dl.interpretation salg v v x).posMem d from eqAtN ▸ w
end Expr
