import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

namespace Etst


/-
  Converts an expression to "negation normal form", pushing negations
  as far down as possible. Duals (eg. union) are still left repre-
  sented with complements.
-/
-- This version uses well-founded recursion, which makes the function
-- not reducible due to :/
-- https://github.com/leanprover/lean4/issues/5192
-- def Expr.toNnf {E}: Expr E → Expr E
-- | .const e x => .const e x
-- | .var x => .var x
-- | .null => .null
-- | .prod left rite => .prod left.toNnf rite.toNnf
-- | .ir left rite => .ir left.toNnf rite.toNnf
-- | .full body => .full body.toNnf
-- | .compl (.const e x) => .compl (.const e x)
-- | .compl (.var x) => .compl (.var x)
-- | .compl .null => .pair .any .any
-- | .compl (.prod left rite) =>
--   s3(null,
--     null | (!<[left.toNnf]>, <[any]>) | (<[any]>, !<[rite.toNnf]>))
-- | .compl (.ir left rite) =>
--   .compl (.ir (.compl left.compl.toNnf) (.compl rite.compl.toNnf))
-- | .compl (.full body) =>
--   .compl (.full (.compl body.compl.toNnf))
-- | .compl (.compl body) => body.toNnf
-- | .compl (.arbIr body) =>
--   .compl (.arbIr (.compl body.compl.toNnf))
-- | .arbIr body => .arbIr body.toNnf
def Expr.toNnfAux {E} : Expr E → Bool → Expr E
-- Positive context (isNegated = false)
| .const e x, false => .const e x
| .oracle e x, false => .oracle e x
| .var x,     false => .var x
| .null,      false => .null
| .prod l r,  false => .prod (l.toNnfAux false) (r.toNnfAux false)
| .ir l r,    false => .ir (l.toNnfAux false) (r.toNnfAux false)
| .full b,    false => .full (b.toNnfAux false)
| .arbIr b,   false => .arbIr (b.toNnfAux false)
| .compl b,   false => b.toNnfAux true -- Switch to negative context
-- Negative context (isNegated = true)
| .const e x, true  => .compl (.const e x)
| .oracle e x, true => .compl (.oracle e x)
| .var x,     true  => .compl (.var x)
| .null,      true  => .prod .any .any
| .prod l r,  true  => 
  .un
    .null
    (.un
      (.prod (l.toNnfAux true) .any)
      (.prod .any (r.toNnfAux true)))
| .ir l r,    true  => 
  .compl (.ir (.compl (l.toNnfAux true)) (.compl (r.toNnfAux true)))
| .full b,    true  => 
  .compl (.full (.compl (b.toNnfAux true)))
| .arbIr b,   true  => 
  .compl (.arbIr (.compl (b.toNnfAux true)))
| .compl b,   true  => 
  b.toNnfAux false -- Double negation eliminated,

def Expr.toNnf {E} (e : Expr E) : Expr E :=
  e.toNnfAux false

def Expr.toNnfCcElim {E}
  (expr: Expr E)
:
  expr.compl.compl.toNnf = expr.toNnf
:=
  rfl


def SingleLaneExpr.intp2_toNnfAux_eq
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c o: Valuation Pair)
:
  And
    (intp2 (expr.toNnfAux false) fv b c o = intp2 expr fv b c o)
    (intp2 (expr.toNnfAux true) fv b c o = intp2 (.compl expr) fv b c o)
:=
  match expr with
  | .const _ _ => ⟨rfl, rfl⟩
  | .oracle _ _ => ⟨rfl, rfl⟩
  | .var _ => ⟨rfl, rfl⟩
  | .null => ⟨
      funext fun _ => rfl,
      funext fun
      | .null => propext ⟨nofun, nofun⟩
      | .pair _ _ => propext ⟨nofun, fun _ => inProd inAny inAny⟩,
    ⟩
  | .prod left rite =>
    let ⟨ihL, ihCL⟩ := left.intp2_toNnfAux_eq fv b c o
    let ⟨ihR, ihCR⟩ := rite.intp2_toNnfAux_eq fv b c o
    ⟨
      eq_intp2_prod_of_eq ihL ihR,
      funext fun p =>
      propext ⟨
        fun inUnNullPairPair =>
          match p with
          | .null => inCompl fun inProdNull => inProdElimNope inProdNull
          | .pair _ _ =>
            inCompl fun inProdAB =>
              let ⟨inLeft, inRite⟩ := inProdElim inProdAB
              (inUnElim inUnNullPairPair).elim
                (fun inNull => inNullElimNope inNull)
                (fun inInner =>
                  (inUnElim inInner).elim
                    (fun inProdL =>
                      let ⟨inCplLeft, _⟩ := inProdElim inProdL
                      inComplElim (ihCL.symm ▸ inCplLeft) inLeft)
                    (fun inProdR =>
                      let ⟨_, inCplRite⟩ := inProdElim inProdR
                      inComplElim (ihCR.symm ▸ inCplRite) inRite)),
        fun inComplProd =>
          match p with
          | .null => inUnL inNull
          | .pair _ _ =>
            (ninProdElim inComplProd).elim
              (fun ninLeft =>
                inUnR
                  (inUnL
                    (inProd
                      (ihCL ▸ inCompl ninLeft)
                      inAny)))
              (fun ninRite =>
                inUnR
                  (inUnR
                    (inProd
                      inAny
                      (ihCR ▸ inCompl ninRite)))),
      ⟩,
    ⟩
  | .ir left rite =>
    let ⟨ihL, ihCL⟩ := left.intp2_toNnfAux_eq fv b c o
    let ⟨ihR, ihCR⟩ := rite.intp2_toNnfAux_eq fv b c o
    ⟨
      eq_intp2_ir_of_eq ihL ihR,
      eq_intp2_compl_of_eq
        (eq_intp2_ir_of_eq
          ((eq_intp2_compl_of_eq ihCL.symm).symm.trans
            ((intp2_compl_compl_eq left fv c b o)))
          ((eq_intp2_compl_of_eq ihCR.symm).symm.trans
            ((intp2_compl_compl_eq rite fv c b o)))),
    ⟩
  | .full body =>
    let ⟨ih, ihC⟩ := body.intp2_toNnfAux_eq fv b c o
    ⟨
      eq_intp2_full_of_eq ih,
      eq_intp2_compl_of_eq
        (eq_intp2_full_of_eq
          ((eq_intp2_compl_of_eq ihC.symm).symm.trans
            (intp2_compl_compl_eq body fv c b o))),
    ⟩
  | .compl body =>
    let ⟨ih, ihC⟩ := body.intp2_toNnfAux_eq fv b c o
    ⟨
      ihC,
      (ih.trans (intp2_compl_compl_eq body fv b c o).symm),
    ⟩
  | .arbIr body =>
    ⟨
      eq_intp2_arbIr_of_eq fun pB =>
        (body.intp2_toNnfAux_eq (pB :: fv) b c o).left,
      eq_intp2_compl_of_eq
        (eq_intp2_arbIr_of_eq fun pX =>
          let ⟨_, ihC⟩ := body.intp2_toNnfAux_eq (pX :: fv) b c o
          ((eq_intp2_compl_of_eq ihC.symm).symm.trans
            (intp2_compl_compl_eq body (pX :: fv) c b o))),
    ⟩

def SingleLaneExpr.intp2_toNnf_eq
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c o: Valuation Pair)
:
  intp2 expr.toNnf fv b c o = intp2 expr fv b c o
:=
  (expr.intp2_toNnfAux_eq fv b c o).left


-- A unary helper for termination when recursing on nnf expressions.
def complUnaryLt {E} [SizeOf E]
  (body: Expr E)
:
  sizeOf (Expr.compl body) < 1 + (1 + (sizeOf body))
:= by
  apply Nat.add_lt_add_left
  exact lt_add_of_pos_of_le zero_lt_one le_rfl

-- A left helper for termination when recursing on nnf expressions.
def complBinLtL {E} [SizeOf E]
  (left rite: Expr E)
:
  sizeOf (Expr.compl left) < 1 + (1 + sizeOf left + sizeOf rite)
:= by
  apply Nat.add_lt_add_left _ 1
  exact Nat.lt_add_right _ (Nat.lt_add_left_iff_pos.mpr zero_lt_one)

-- A rite helper for termination when recursing on nnf expressions.
def complBinLtR {E} [SizeOf E]
  (left rite: Expr E)
:
  sizeOf (Expr.compl rite) < 1 + (1 + sizeOf left + sizeOf rite)
:= by
  apply Nat.add_lt_add_left _ 1
  rw [Nat.add_assoc]
  apply lt_add_of_pos_of_le zero_lt_one
  apply Nat.le_add_left


inductive Expr.IsNnf {E}: Expr E → Prop
| const {e x}: IsNnf (.const e x)
| complConst {e x}: IsNnf (.compl (.const e x))
| oracle {e x}: IsNnf (.oracle e x)
| complOracle {e x}: IsNnf (.compl (.oracle e x))
| var {x}: IsNnf (.var x)
| complVar {x}: IsNnf (.compl (.var x))
| null: IsNnf .null
| prod {left rite}: IsNnf left → IsNnf rite → IsNnf (prod left rite)
| ir {left rite}: IsNnf left → IsNnf rite → IsNnf (.ir left rite)
| un {left rite}: IsNnf left → IsNnf rite → IsNnf (.un left rite)
| full {body}: IsNnf body → IsNnf (.full body)
| some {body}: IsNnf body → IsNnf (.some body)
| arbIr {body}: IsNnf body → IsNnf (.arbIr body)
| arbUn {body}: IsNnf body → IsNnf (.arbUn body)


def Expr.IsNnf.any {E}: IsNnf (any (E := E)) := .arbUn .var

def Expr.isNnfAux {E}:
  (expr: Expr E) →
  (isNegated: Bool) →
  IsNnf (expr.toNnfAux isNegated)
|
  .const _ _, false => .const
| .const _ _, true => .complConst
| .oracle _ _, false => .oracle
| .oracle _ _, true => .complOracle
| .var _, false => .var
| .var _, true => .complVar
| .null, false => .null
| .null, true => .prod .any .any
| .prod l r, false =>
  .prod (isNnfAux l false) (isNnfAux r false)
| .prod l r, true =>
  .un .null
    (.un
      (.prod (isNnfAux l true) .any)
      (.prod .any (isNnfAux r true)))
| .ir l r, false =>
  .ir (isNnfAux l false) (isNnfAux r false)
| .ir l r, true =>
  .un (isNnfAux l true) (isNnfAux r true)
| .full b, false => .full (isNnfAux b false)
| .full b, true => .some (isNnfAux b true)
| .compl b, false => isNnfAux b true
| .compl b, true => isNnfAux b false
| .arbIr b, false => .arbIr (isNnfAux b false)
| .arbIr b, true => .arbUn (isNnfAux b true)

def Expr.toNnf_isNnf {E} (expr: Expr E): expr.toNnf.IsNnf :=
  isNnfAux expr false


def Expr.IsNnf.toNnf_id {E} {expr: Expr E}:
  expr.IsNnf →
  expr.toNnf = expr
|
  .const => rfl
| .complConst => rfl
| .oracle => rfl
| .complOracle => rfl
| .var => rfl
| .complVar => rfl
| .null => rfl
| .prod l r =>
  show Expr.prod _ _ = _ from
  congr (congr rfl l.toNnf_id) r.toNnf_id
| .ir l r =>
  show Expr.ir _ _ = _ from
  congr (congr rfl l.toNnf_id) r.toNnf_id
| .un l r =>
  show Expr.un _ _ = _ from
  congr (congr rfl l.toNnf_id) r.toNnf_id
| .full b =>
  show Expr.full _ = _ from
  congr rfl b.toNnf_id
| .some b =>
  show Expr.some _ = _ from
  congr rfl b.toNnf_id
| .arbIr b =>
  show Expr.arbIr _ = _ from
  congr rfl b.toNnf_id
| .arbUn b =>
  show Expr.arbUn _ = _ from
  congr rfl b.toNnf_id

def Expr.toNnf_idem {E}
  (expr: Expr E)
:
  expr.toNnf.toNnf = expr.toNnf
:=
  expr.toNnf_isNnf.toNnf_id 


def BasicExpr.toNnfAux_toLane_comm
  (expr: BasicExpr)
  (isNegated: Bool)
  (lane: Set3.Lane)
:
  let otherLane := if isNegated then lane.toggle else lane
  Eq
    (BasicExpr.toLane (expr.toNnfAux isNegated) lane)
    ((expr.toLane otherLane).toNnfAux isNegated)
:=
  match expr, isNegated with
  | .const x, false => rfl
  | .const x, true => rfl
  | .oracle x, false => rfl
  | .oracle x, true => rfl
  | .var x, false => rfl
  | .var x, true => rfl
  | .null, false => rfl
  | .null, true => rfl
  | .prod left rite, false =>
    let ihL := toNnfAux_toLane_comm left false lane
    let ihR := toNnfAux_toLane_comm rite false lane
    show Expr.prod _ _ = Expr.prod _ _ from
    congr (congr rfl ihL) ihR
  | .prod left rite, true =>
    let ihL := toNnfAux_toLane_comm left true lane
    let ihR := toNnfAux_toLane_comm rite true lane
    show .un _ (.un _ _) = Expr.un _ (.un _ _) from
    let teq := Set3.Lane.toggle_toggle_eq lane
    let teq2: lane = lane.toggle.toggle.toggle.toggle := by
      conv => lhs; rw [←teq, ←teq]
    congr
      (congr rfl rfl)
      (congr (congr rfl (teq2 ▸ ihL ▸ rfl)) (teq2 ▸ ihR ▸ rfl))
  | .ir left rite, false =>
    let ihL := toNnfAux_toLane_comm left false lane
    let ihR := toNnfAux_toLane_comm rite false lane
    show Expr.ir _ _ = Expr.ir _ _ from
    congr (congr rfl ihL) ihR
  | .ir left rite, true =>
    let ihL := toNnfAux_toLane_comm left true lane
    let ihR := toNnfAux_toLane_comm rite true lane
    show Expr.un _ _ = Expr.un _ _ from
    let teq := Set3.Lane.toggle_toggle_eq lane
    congr (congr rfl (teq.symm ▸ ihL)) (teq.symm ▸ ihR)
  | .full body, false =>
    let ih := toNnfAux_toLane_comm body false lane
    show Expr.full _ = Expr.full _ from
    congr rfl ih
  | .full body, true =>
    let ih := toNnfAux_toLane_comm body true lane
    let teq := Set3.Lane.toggle_toggle_eq lane
    show Expr.some _ = Expr.some _ from
    congr rfl (teq.symm ▸ ih)
  | .compl body, false =>
    toNnfAux_toLane_comm body true lane
  | .compl body, true =>
    let ih: _ = _ := toNnfAux_toLane_comm body false lane
    let teq := Set3.Lane.toggle_toggle_eq lane
    show _ = (body.toLane lane.toggle.toggle).toNnfAux false from
    teq.symm ▸ ih
  | .arbIr body, false =>
    let ih := toNnfAux_toLane_comm body false lane
    show Expr.arbIr _ = Expr.arbIr _ from
    congr rfl ih
  | .arbIr body, true =>
    let ih := toNnfAux_toLane_comm body true lane
    let teq := Set3.Lane.toggle_toggle_eq lane
    show Expr.arbUn _ = Expr.arbUn _ from
    congr rfl (teq.symm ▸ ih)

def BasicExpr.toNnf_toLane_comm
  (expr: BasicExpr)
  (lane: Set3.Lane)
:
  BasicExpr.toLane expr.toNnf lane =  (expr.toLane lane).toNnf
:=
  expr.toNnfAux_toLane_comm false lane


def BasicExpr.triIntp2_toNnf_eq
  (expr: BasicExpr)
  (fv: List Pair)
  (b c o: Valuation Pair)
:
  BasicExpr.triIntp2 expr.toNnf fv b c o = expr.triIntp2 fv b c o
:=
  open SingleLaneExpr in
  Set3.eq
    (show intp2 _ _ _ _ _ = _ from
      toNnf_toLane_comm _ _ ▸
      intp2_toNnf_eq _ _ _ _ _)
    (show intp2 _ _ _ _ _ = _ from
      toNnf_toLane_comm _ _ ▸
      intp2_toNnf_eq _ _ _ _ _)

def BasicExpr.triIntp_toNnf_eq
  (expr: BasicExpr)
  (fv: List Pair)
  (v: Valuation Pair)
:
  BasicExpr.triIntp expr.toNnf fv v = expr.triIntp fv v
:=
  funext fun o => expr.triIntp2_toNnf_eq fv v v o
