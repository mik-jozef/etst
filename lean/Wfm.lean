import PairExpr
import ExprRulesOfInference

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
