import Utils.PairExpr


inductive PExprKind
  | var
  | zero
  | pair
  | un
  | ir
  | condSome
  | condFull
  | cpl
  | arbUn
  | arbIr

abbrev ExtraInfo := PExprKind → Type

abbrev EmptyExtraInfo: ExtraInfo := fun _ => Unit

abbrev Paint := Nat → Bool
def Paint.clear: Paint := fun _ => false
def Paint.solid: Paint := fun _ => true

abbrev PaintedExtraInfo: ExtraInfo
  | .var => Paint
  | _ => Unit


inductive PExpr (E: ExtraInfo)
  | var (e: E .var) (x: Nat)
  | zero (e: E .zero)
  | pair (e: E .pair) (zth fst: PExpr E)
  | un (e: E .un) (l r: PExpr E)
  | ir (e: E .ir) (l r: PExpr E)
  | condSome (e: E .condSome) (cond: PExpr E)
  | condFull (e: E .condFull) (cond: PExpr E)
  | cpl (e: E .cpl) (expr: PExpr E)
  | arbUn (e: E .arbUn) (x: Nat) (body: PExpr E)
  | arbIr (e: E .arbIr) (x: Nat) (body: PExpr E)

def PExpr.toExpr: PExpr E → Expr pairSignature
  | var _ x => Expr.var x
  | zero _ => PairExpr.zeroExpr
  | pair _ l r => PairExpr.pairExpr l.toExpr r.toExpr
  | un _ l r => PairExpr.unExpr l.toExpr r.toExpr
  | ir _ l r => PairExpr.irExpr l.toExpr r.toExpr
  | condSome _ c => PairExpr.condSomeExpr c.toExpr
  | condFull _ c => PairExpr.condFullExpr c.toExpr
  | cpl _ expr => Expr.cpl expr.toExpr
  | arbUn _ x body => Expr.arbUn x body.toExpr
  | arbIr _ x body => Expr.arbIr x body.toExpr

def PExpr.toEmptyInfo: PExpr E → PExpr EmptyExtraInfo
  | var _ x => .var () x
  | zero _ => .zero ()
  | pair _ l r => .pair () l.toEmptyInfo r.toEmptyInfo
  | un _ l r => .un () l.toEmptyInfo r.toEmptyInfo
  | ir _ l r => .ir () l.toEmptyInfo r.toEmptyInfo
  | condSome _ c => .condSome () c.toEmptyInfo
  | condFull _ c => .condFull () c.toEmptyInfo
  | cpl _ expr => .cpl () expr.toEmptyInfo
  | arbUn _ x body => .arbUn () x body.toEmptyInfo
  | arbIr _ x body => .arbIr () x body.toEmptyInfo

structure UnpackedExtraInfo (E: ExtraInfo) where
  kind: PExprKind
  e: E kind

def PExpr.getExtraInfo: PExpr E → UnpackedExtraInfo E
  | var e _ => ⟨.var, e⟩
  | zero e => ⟨.zero, e⟩
  | pair e _ _ => ⟨.pair, e⟩
  | un e _ _ => ⟨.un, e⟩
  | ir e _ _ => ⟨.ir, e⟩
  | condSome e _ => ⟨.condSome, e⟩
  | condFull e _ => ⟨.condFull, e⟩
  | cpl e _ => ⟨.cpl, e⟩
  | arbUn e _ _ => ⟨.arbUn, e⟩
  | arbIr e _ _ => ⟨.arbIr, e⟩

def Expr.toPExpr
  (expr: Expr pairSignature)
  {E: ExtraInfo}
  (e: (kind: PExprKind) → E kind)
:
  PExpr E
:=
  match expr with
  | var x => .var (e .var) x
  | op pairSignature.Op.zero _ => .zero (e .zero)
  | op pairSignature.Op.pair args =>
    .pair (e .pair) ((args .zth).toPExpr e) ((args .fst).toPExpr e)
  | op pairSignature.Op.un args =>
    .un (e .un) ((args .zth).toPExpr e) ((args .fst).toPExpr e)
  | op pairSignature.Op.ir args =>
    .ir (e .ir) ((args .zth).toPExpr e) ((args .fst).toPExpr e)
  | op pairSignature.Op.condSome args =>
    .condSome (e .condSome) ((args .zth).toPExpr e)
  | op pairSignature.Op.condFull args =>
    .condFull (e .condFull) ((args .zth).toPExpr e)
  | cpl expr => .cpl (e .cpl) (expr.toPExpr e)
  | arbUn x body => .arbUn (e .arbUn) x (body.toPExpr e)
  | arbIr x body => .arbIr (e .arbIr) x (body.toPExpr e)


abbrev PaintedPExpr := PExpr PaintedExtraInfo

namespace PaintedPExpr
  def var (x: Nat) (paint: Paint): PaintedPExpr := PExpr.var paint x
  def zero: PaintedPExpr := PExpr.zero ()
  def pair (zth fst: PaintedPExpr): PaintedPExpr := PExpr.pair () zth fst
  def un (l r: PaintedPExpr): PaintedPExpr := PExpr.un () l r
  def ir (l r: PaintedPExpr): PaintedPExpr := PExpr.ir () l r
  def condSome (c: PaintedPExpr): PaintedPExpr := PExpr.condSome () c
  def condFull (c: PaintedPExpr): PaintedPExpr := PExpr.condFull () c
  def cpl (expr: PaintedPExpr): PaintedPExpr := PExpr.cpl () expr
  def arbUn (x: Nat) (body: PaintedPExpr): PaintedPExpr :=
    PExpr.arbUn () x body
  def arbIr (x: Nat) (body: PaintedPExpr): PaintedPExpr :=
    PExpr.arbIr () x body
  
  def clearVar (x: Nat): PaintedPExpr := var x .clear
  def solidVar (x: Nat): PaintedPExpr := var x .solid
  
  def anyExpr: PaintedPExpr := .arbUn 0 (.solidVar 0)
  def noneExpr: PaintedPExpr := .arbIr 0 (.solidVar 0)
  
end PaintedPExpr


def PExpr.intp
  (a: PExpr E)
  (v: Valuation Pair)
:
  Set3 Pair
:=
  a.toExpr.intp v

  def PExpr.intp2
    (a: PExpr E)
    (b c: Valuation Pair)
  :
    Set3 Pair
  :=
    a.toExpr.intp2 b c


def PExpr.mono_un_pos_left
  (a b: PExpr E)
  (e: E .un)
  (v: Valuation Pair)
:
  (a.toExpr.intp v).posMem
    ⊆
  ((PExpr.un e a b).toExpr.intp v).posMem
:=
  fun _ => Or.inl

def PExpr.mono_un_pos_rite
  (a b: PExpr E)
  (e: E .un)
  (v: Valuation Pair)
:
  (b.toExpr.intp v).posMem
    ⊆
  ((PExpr.un e a b).toExpr.intp v).posMem
:=
  fun _ => Or.inr
