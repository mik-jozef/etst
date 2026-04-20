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
-- | .pair left rite => .pair left.toNnf rite.toNnf
-- | .ir left rite => .ir left.toNnf rite.toNnf
-- | .full body => .full body.toNnf
-- | .compl (.const e x) => .compl (.const e x)
-- | .compl (.var x) => .compl (.var x)
-- | .compl .null => .pair .any .any
-- | .compl (.pair left rite) =>
--   s3(null, null | (![left.toNnf], [any]) | ([any], ![rite.toNnf]))
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
| .var x,     false => .var x
| .null,      false => .null
| .pair l r,  false => .pair (l.toNnfAux false) (r.toNnfAux false)
| .ir l r,    false => .ir (l.toNnfAux false) (r.toNnfAux false)
| .full b,    false => .full (b.toNnfAux false)
| .arbIr b,   false => .arbIr (b.toNnfAux false)
| .compl b,   false => b.toNnfAux true -- Switch to negative context
-- Negative context (isNegated = true)
| .const e x, true  => .compl (.const e x)
| .var x,     true  => .compl (.var x)
| .null,      true  => .pair .any .any
| .pair l r,  true  => 
  .un
    .null
    (.un
      (.pair (l.toNnfAux true) .any)
      (.pair .any (r.toNnfAux true)))
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


def SingleLaneExpr.intp2_toNnfAux
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  And
    (intp2 expr fv b c = intp2 (expr.toNnfAux false) fv b c)
    (intp2 (.compl expr) fv b c = intp2 (expr.toNnfAux true) fv b c)
:=
  match expr with
  | .const _ _ => ⟨rfl, rfl⟩
  | .var _ => ⟨rfl, rfl⟩
  | .null => ⟨
      funext fun _ => rfl,
      funext fun
      | .null => propext ⟨nofun, nofun⟩
      | .pair _ _ => propext ⟨fun _ => inPair inAny inAny, nofun⟩,
    ⟩
  | .pair left rite =>
    let ⟨ihL, ihCL⟩ := intp2_toNnfAux left fv b c
    let ⟨ihR, ihCR⟩ := intp2_toNnfAux rite fv b c
    ⟨
      eq_intp2_pair_of_eq ihL ihR,
      funext fun d =>
      propext ⟨
        fun inComplPair =>
          match d with
          | .null => inUnL inNull
          | .pair _ _ =>
            (ninPairElim inComplPair).elim
              (fun ninLeft =>
                inUnR
                  (inUnL
                    (inPair
                      (ihCL ▸ inCompl ninLeft)
                      inAny)))
              (fun ninRite =>
                inUnR
                  (inUnR
                    (inPair
                      inAny
                      (ihCR ▸ inCompl ninRite)))),
        fun inUnNullPairPair =>
          match d with
          | .null => inCompl fun inPair => inPairElimNope inPair
          | .pair _ _ =>
            inCompl fun inPairAB =>
              let ⟨inLeft, inRite⟩ := inPairElim inPairAB
              (inUnElim inUnNullPairPair).elim
                (fun inNull => inNullElimNope inNull)
                (fun inInner =>
                  (inUnElim inInner).elim
                    (fun inPairL =>
                      let ⟨inCplLeft, _⟩ := inPairElim inPairL
                      inComplElim (ihCL.symm ▸ inCplLeft) inLeft)
                    (fun inPairR =>
                      let ⟨_, inCplRite⟩ := inPairElim inPairR
                      inComplElim (ihCR.symm ▸ inCplRite) inRite)),
      ⟩,
    ⟩
  | .ir left rite =>
    let ⟨ihL, ihCL⟩ := intp2_toNnfAux left fv b c
    let ⟨ihR, ihCR⟩ := intp2_toNnfAux rite fv b c
    ⟨
      eq_intp2_ir_of_eq ihL ihR,
      eq_intp2_compl_of_eq
        (eq_intp2_ir_of_eq
          ((intp2_compl_compl_eq left fv c b).symm.trans
            (eq_intp2_compl_of_eq ihCL))
          ((intp2_compl_compl_eq rite fv c b).symm.trans
            (eq_intp2_compl_of_eq ihCR))),
    ⟩
  | .full body =>
    let ⟨ih, ihC⟩ := intp2_toNnfAux body fv b c
    ⟨
      eq_intp2_full_of_eq ih,
      eq_intp2_compl_of_eq
        (eq_intp2_full_of_eq
          ((intp2_compl_compl_eq body fv c b).symm.trans
            (eq_intp2_compl_of_eq ihC))),
    ⟩
  | .compl body =>
    let ⟨ih, ihC⟩ := intp2_toNnfAux body fv b c
    ⟨
      ihC,
      (intp2_compl_compl_eq body fv b c).trans ih,
    ⟩
  | .arbIr body =>
    ⟨
      eq_intp2_arbIr_of_eq fun dB =>
        (intp2_toNnfAux body (dB :: fv) b c).left,
      eq_intp2_compl_of_eq
        (eq_intp2_arbIr_of_eq fun dX =>
          ((intp2_compl_compl_eq body (dX :: fv) c b).symm.trans
            (eq_intp2_compl_of_eq
              (intp2_toNnfAux body (dX :: fv) b c).right))),
    ⟩

def SingleLaneExpr.intp2_toNnf
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  intp2 expr fv b c = intp2 expr.toNnf fv b c
:=
  (intp2_toNnfAux expr fv b c).left

def SingleLaneExpr.intp2_toNnf_p
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c: Valuation Pair)
  (p: Pair)
:
  intp2 expr fv b c p = intp2 expr.toNnf fv b c p
:=
  congr (intp2_toNnf expr fv b c) rfl


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
