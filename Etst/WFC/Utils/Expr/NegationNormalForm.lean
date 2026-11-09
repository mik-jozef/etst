module
public import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst


/-
  Converts an expression to "negation normal form", pushing negations
  as far down as possible. Duals (eg. union) are still left repre-
  sented with complements.
-/
-- This version uses well-founded recursion, which makes the function
-- not reducible due to :/
-- https://github.com/leanprover/lean4/issues/5192
-- def Expr.toNnf {E}: Expr kind → Expr kind
-- | .const tag x => .const tag x
-- | .var x => .var x
-- | .null => .null
-- | .prod left rite => .prod left.toNnf rite.toNnf
-- | .ir left rite => .ir left.toNnf rite.toNnf
-- | .full body => .full body.toNnf
-- | .compl (.const tag x) => .compl (.const tag x)
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
exposed def Expr.toNnfAux {kind}: Expr kind → Bool → Expr kind
-- Positive context (isNegated = false)
| .const tag x, false => .const tag x
| .var x,     false => .var x
| .null,      false => .null
| .prod l r,  false => .prod (l.toNnfAux false) (r.toNnfAux false)
| .ir l r,    false => .ir (l.toNnfAux false) (r.toNnfAux false)
| .full b,    false => .full (b.toNnfAux false)
| .arbIr b,   false => .arbIr (b.toNnfAux false)
| .compl b,   false => b.toNnfAux true -- Switch to negative context
-- Negative context (isNegated = true)
| .const tag x, true  => .compl (.const tag x)
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

exposed def Expr.toNnf {kind} (e: Expr kind): Expr kind :=
  e.toNnfAux false

theorem Expr.toNnfCcElim {kind}
  (expr: Expr kind)
:
  expr.compl.compl.toNnf = expr.toNnf
:=
  rfl


theorem Expr.intp_toNnfAux_eq {kind}
  (expr: Expr kind)
  (lane: kind.Lane)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  And
    (Eq
      ((expr.toNnfAux false).intp lane b c fv)
      (expr.intp lane b c fv))
    (Eq
      ((expr.toNnfAux true).intp lane b c fv)
      (expr.compl.intp lane b c fv))
:=
  match expr with
  | .const _ _ => ⟨rfl, rfl⟩
  | .var _ => ⟨rfl, rfl⟩
  | .null => ⟨
      Set.ext fun _ => Iff.rfl,
      Set.ext fun
      | .null => ⟨nofun, nofun⟩
      | .pair _ _ => ⟨nofun, fun _ => inProd inAny inAny⟩,
    ⟩
  | .prod left rite =>
    let ⟨ihL, ihCL⟩ := left.intp_toNnfAux_eq lane b c fv
    let ⟨ihR, ihCR⟩ := rite.intp_toNnfAux_eq lane b c fv
    ⟨
      eq_intp_prod_of_eq ihL ihR,
      Set.ext fun p =>
      ⟨
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
    let ⟨ihL, ihCL⟩ := left.intp_toNnfAux_eq lane b c fv
    let ⟨ihR, ihCR⟩ := rite.intp_toNnfAux_eq lane b c fv
    ⟨
      eq_intp_ir_of_eq ihL ihR,
      eq_intp_compl_of_eq <|
      eq_intp_ir_of_eq
        (eq_intp_of_eq_compl <|
          (left.toNnfAux true).intp_compl_compl_eq lane b c fv ▸
          ihCL)
        (eq_intp_of_eq_compl <|
          (rite.toNnfAux true).intp_compl_compl_eq lane b c fv ▸
          ihCR)
    ⟩
  | .full body =>
    let ⟨ih, ihC⟩ := body.intp_toNnfAux_eq lane b c fv
    ⟨
      eq_intp_full_of_eq ih,
      eq_intp_compl_of_eq <|
      eq_intp_full_of_eq <|
      eq_intp_of_eq_compl <|
      (body.toNnfAux true).intp_compl_compl_eq lane b c fv ▸
      ihC
    ⟩
  | .compl body =>
    let ⟨ih, ihC⟩ := body.intp_toNnfAux_eq lane b c fv
    ⟨
      ihC,
      (ih.trans (body.intp_compl_compl_eq lane b c fv).symm),
    ⟩
  | .arbIr body =>
    ⟨
      eq_intp_arbIr_of_eq fun pB =>
        (body.intp_toNnfAux_eq lane b c (pB :: fv)).left,
      eq_intp_compl_of_eq <|
      eq_intp_arbIr_of_eq fun pX =>
      let ⟨_, ihC⟩ := body.intp_toNnfAux_eq lane b c (pX :: fv)
      eq_intp_of_eq_compl <|
      (body.toNnfAux true).intp_compl_compl_eq lane b c (pX :: fv) ▸
      ihC
    ⟩

theorem Expr.intp_toNnf_eq {kind}
  (expr: Expr kind)
  (lane: kind.Lane)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  expr.toNnf.intp lane b c fv = expr.intp lane b c fv
:=
  (expr.intp_toNnfAux_eq lane b c fv).left


-- A unary helper for termination when recursing on nnf expressions.
theorem complUnaryLt {kind}
  (body: Expr kind)
:
  sizeOf body.compl < 1 + (1 + (sizeOf body))
:= by
  apply Nat.add_lt_add_left
  exact lt_add_of_pos_of_le zero_lt_one le_rfl

-- A left helper for termination when recursing on nnf expressions.
theorem complBinLtL {kind}
  (left rite: Expr kind)
:
  sizeOf (Expr.compl left) < 1 + (1 + sizeOf left + sizeOf rite)
:= by
  apply Nat.add_lt_add_left _ 1
  exact Nat.lt_add_right _ (Nat.lt_add_left_iff_pos.mpr zero_lt_one)

-- A rite helper for termination when recursing on nnf expressions.
theorem complBinLtR {kind}
  (left rite: Expr kind)
:
  sizeOf (Expr.compl rite) < 1 + (1 + sizeOf left + sizeOf rite)
:= by
  apply Nat.add_lt_add_left _ 1
  rw [Nat.add_assoc]
  apply lt_add_of_pos_of_le zero_lt_one
  apply Nat.le_add_left


inductive Expr.IsNnf {kind}: Expr kind → Prop
| const {tag x}: IsNnf (.const tag x)
| complConst {tag x}: IsNnf (.compl (.const tag x))
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


theorem Expr.IsNnf.any {kind}: IsNnf (any (kind := kind)) := .arbUn .var

theorem Expr.isNnfAux {kind}:
  (expr: Expr kind) →
  (isNegated: Bool) →
  IsNnf (expr.toNnfAux isNegated)
|
  .const _ _, false => .const
| .const _ _, true => .complConst
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

theorem Expr.toNnf_isNnf {kind} (expr: Expr kind): expr.toNnf.IsNnf :=
  isNnfAux expr false


theorem Expr.IsNnf.toNnf_id {kind} {expr: Expr kind}:
  expr.IsNnf →
  expr.toNnf = expr
|
  .const => rfl
| .complConst => rfl
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

theorem Expr.toNnf_idem {kind}
  (expr: Expr kind)
:
  expr.toNnf.toNnf = expr.toNnf
:=
  expr.toNnf_isNnf.toNnf_id 


theorem Expr.triIntp_toNnf_eq
  (expr: Expr .basic)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  expr.toNnf.triIntp b c fv = expr.triIntp b c fv
:=
  Set3.eq
    (expr.intp_toNnf_eq .defLane b c fv)
    (expr.intp_toNnf_eq .posLane b c fv)
