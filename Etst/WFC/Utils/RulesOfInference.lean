import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Valuation

namespace Etst


namespace Expr
  -- `any` contains all elements, under any valuation.
  def any: Expr sig := Expr.arbUn (.bvar 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr sig := Expr.cpl any


  abbrev Ins2
    (salg: Salgebra sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    (expr.interpretation salg bv b c).defMem d
  
  abbrev Inw2
    (salg: Salgebra sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    (expr.interpretation salg bv b c).posMem d

  def Ins2.toInw2 (s: Ins2 salg bv b c expr d):
    Inw2 salg bv b c expr d
  :=
    s.toPos
  
  
  def Ins
    (salg: Salgebra sig)
    (bv: List salg.D)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Ins2 salg bv v v expr d
  
  def Inw
    (salg: Salgebra sig)
    (bv: List salg.D)
    (v: Valuation salg.D)
    (expr: Expr sig)
    (d: salg.D)
  :=
    Inw2 salg bv v v expr d
  
  
  def insArbUn
    dBound
    (s: Ins2 salg (dBound :: bv) b c body d)
  :
    Ins2 salg bv b c (arbUn body) d
  :=
    ⟨dBound, s⟩
  
  def inwArbUn
    dBound
    (s: Inw2 salg (dBound :: bv) b c body d)
  :
    Inw2 salg bv b c (arbUn body) d
  :=
    ⟨dBound, s⟩
  
  
  def insArbUnElim
    (s: Ins2 salg bv b c (arbUn body) d)
  :
    ∃ dBound, Ins2 salg (dBound :: bv) b c body d
  :=
    s
  
  def inwArbUnElim
    (s: Inw2 salg bv b c (arbUn body) d)
  :
    ∃ dBound, Inw2 salg (dBound :: bv) b c body d
  :=
    s
  
  
  def insArbIr
    {salg: Salgebra sig}
    {bv: List salg.D}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Ins2 salg (dBound :: bv) b c body d)
  :
    Ins2 salg bv b c (arbIr body) d
  :=
    fun d => s d
  
  def inwArbIr
    {salg: Salgebra sig}
    {bv: List salg.D}
    {b c: Valuation salg.D}
    {d: salg.D}
    (s: ∀ dBound, Inw2 salg (dBound :: bv) b c body d)
  :
    Inw2 salg bv b c (arbIr body) d
  :=
    fun d => s d
  
  
  def insArbIrElim
    (s: Ins2 salg bv b c (arbIr body) d)
    (dBound: salg.D)
  :
    Ins2 salg (dBound :: bv) b c body d
  :=
    s dBound
  
  def inwArbIrElim
    (s: Inw2 salg bv b c (arbIr body) d)
    (dBound: salg.D)
  :
    Inw2 salg (dBound :: bv) b c body d
  :=
    s dBound
  
  
  def insCpl
    (c: Valuation salg.D)
    (w: ¬Inw2 salg bv b b expr d)
  :
    Ins2 salg bv b c (cpl expr) d
  :=
    w
  
  def inwCpl
    (c: Valuation salg.D)
    (s: ¬Ins2 salg bv b b expr d)
  :
    Inw2 salg bv b c (cpl expr) d
  :=
    s
  
  def insCplElim
    (s: Ins2 salg bv b c (cpl expr) d)
  :
    ¬Inw2 salg bv b b expr d
  :=
    s
  
  def inwCplElim
    (w: Inw2 salg bv b c (cpl expr) d)
  :
    ¬Ins2 salg bv b b expr d
  :=
    w
  
  
  -- Valuation c would be redundant since Lean would ignore it, and
  -- complain it cannot be synthetized.
  def ninsCpl
    (w: Inw2 salg bv b b expr d)
  :
    ¬Ins2 salg bv b b (cpl expr) d
  :=
    fun Ins2 => Ins2 w
  
  def ninwCpl
    (s: Ins2 salg bv b b expr d)
  :
    ¬Inw2 salg bv b b (cpl expr) d
  :=
    fun Inw2 => Inw2 s
  
  
  
  def insBound
    {bv: List salg.D}
    {dBound: salg.D}
    (insBv: bv[x]? = some dBound)
  :
    Ins2 salg bv b c (bvar x) dBound
  := by
    rw [Ins2, interpretation, insBv]
    rfl
  
  def inwBound
    {bv: List salg.D}
    {dBound: salg.D}
    (insBv: bv[x]? = some dBound)
  :
    Inw2 salg bv b c (bvar x) dBound
  := by
    rw [Inw2, interpretation, insBv]
    rfl
  
  def insBoundElim
    (s: Ins2 salg bv b c (bvar x) d)
    (eqBound: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [Ins2, interpretation, eqBound] at s
    exact s
  
  def inwBoundElim
    (w: Inw2 salg bv b c (bvar x) d)
    (eqBound: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [Inw2, interpretation, eqBound] at w
    exact w
  

  def insAny: Ins2 salg bv b c any d := insArbUn d (insBound rfl)
  def inwAny: Inw2 salg bv b c any d := inwArbUn d (inwBound rfl)
  
  def ninsNone: ¬Ins2 salg bv b b none d := ninsCpl inwAny
  def ninwNone: ¬Inw2 salg bv b b none d := ninwCpl insAny
  
  
  abbrev InsWfm
    (salg: Salgebra sig)
    (bv: List salg.D)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Ins salg bv (dl.wfm salg) d
  
  abbrev InwWfm
    (salg: Salgebra sig)
    (bv: List salg.D)
    (dl: DefList sig)
    (expr: Expr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.Inw salg bv (dl.wfm salg) d
  
  
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
