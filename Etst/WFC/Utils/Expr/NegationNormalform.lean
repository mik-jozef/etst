import Etst.WFC.Syntax.FiniteDefList
import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

namespace Etst


/-
  Converts an expression to "negation normal form", pushing negations
  as far down as possible. Duals (eg. union) are still left repre-
  sented with complements.
-/
def Expr.toNnf {E}: Expr E → Expr E
| .const e x => .const e x
| .var x => .var x
| .null => .null
| .pair left rite => .pair left.toNnf rite.toNnf
| .ir left rite => .ir left.toNnf rite.toNnf
| .full body => .full body.toNnf
| .compl (.const e x) => .compl (.const e x)
| .compl (.var x) => .compl (.var x)
| .compl .null => .compl .null
| .compl (.pair left rite) =>
  s3(null, null | (![left.toNnf], [any]) | ([any], ![rite.toNnf]))
| .compl (.ir left rite) =>
  .compl (.ir (.compl left.compl.toNnf) (.compl rite.compl.toNnf))
| .compl (.full body) =>
  .compl (.full (.compl body.compl.toNnf))
| .compl (.compl body) => body.toNnf
| .compl (.arbIr body) =>
  .compl (.arbIr (.compl body.compl.toNnf))
| .arbIr body => .arbIr body.toNnf


def SingleLaneExpr.intp2_toNnf
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  intp2 expr fv b c = intp2 expr.toNnf fv b c
:= by
  unfold Expr.toNnf
  exact
  match expr with
  | .const _ _ => rfl
  | .var _ => rfl
  | .null => funext fun _ => rfl
  | .pair left rite =>
    eq_intp2_pair_of_eq
      (intp2_toNnf left fv b c)
      (intp2_toNnf rite fv b c)
  | .ir left rite =>
    eq_intp2_ir_of_eq
      (intp2_toNnf left fv b c)
      (intp2_toNnf rite fv b c)
  | .full body =>
    eq_intp2_full_of_eq
      (intp2_toNnf body fv b c)
  | .compl (.const _ _) => rfl
  | .compl (.var _) => rfl
  | .compl .null => rfl
  | .compl (.pair left rite) =>
    let ihL := intp2_toNnf left fv c b
    let ihR := intp2_toNnf rite fv c b
    funext fun d =>
    propext ⟨
      fun inCompl =>
        match d with
        | .null => inUnL inNull
        | .pair pA pB =>
          (ninPairElim inCompl).elim
            (fun ninLeft =>
              inUnR
                (inUnL
                  (inPair
                    (fun inNnf => ninLeft (ihL ▸ inNnf))
                    inAny)))
            (fun ninRite =>
              inUnR
                (inUnR
                  (inPair
                    inAny
                    (fun inNnf => ninRite (ihR ▸ inNnf))))),
      fun inUnNullPairPair =>
        match d with
        | .null => inCompl fun inPair => inPairElimNope inPair
        | .pair pA pB =>
          inCompl fun inPairAB =>
            let ⟨inLeft, inRite⟩ := inPairElim inPairAB
            (inUnElim inUnNullPairPair).elim
              (fun inNull => inNullElimNope inNull)
              (fun inInner =>
                (inUnElim inInner).elim
                  (fun inPairL =>
                    let ⟨inCplLeft, _⟩ := inPairElim inPairL
                    inComplElim inCplLeft (ihL.symm ▸ inLeft))
                  (fun inPairR =>
                    let ⟨_, inCplRite⟩ := inPairElim inPairR
                    inComplElim inCplRite (ihR.symm ▸ inRite)))
    ⟩
  | .compl (.ir left rite) =>
    have: sizeOf left.compl < 1 + (1 + sizeOf left + sizeOf rite) := by
      apply Nat.add_lt_add_left _ 1
      exact Nat.lt_add_right _ (Nat.lt_add_left_iff_pos.mpr zero_lt_one)
    have: sizeOf rite.compl < 1 + (1 + sizeOf left + sizeOf rite) := by
      show 1 + sizeOf rite < 1 + (1 + sizeOf left + sizeOf rite)
      apply Nat.add_lt_add_left _ 1
      rw [Nat.add_assoc]
      apply lt_add_of_pos_of_le zero_lt_one
      apply Nat.le_add_left
    eq_intp2_compl_of_eq
      (eq_intp2_ir_of_eq
        ((intp2_compl_compl_eq left fv c b).symm.trans
          (eq_intp2_compl_of_eq (intp2_toNnf (.compl left) fv b c)))
        ((intp2_compl_compl_eq rite fv c b).symm.trans
          (eq_intp2_compl_of_eq (intp2_toNnf (.compl rite) fv b c))))
  | .compl (.full body) =>
    have: sizeOf body.compl < 1 + (1 + sizeOf body) :=
      Nat.lt_add_left_iff_pos.mpr zero_lt_one
    eq_intp2_compl_of_eq
      (eq_intp2_full_of_eq
        ((intp2_compl_compl_eq body fv c b).symm.trans
          (eq_intp2_compl_of_eq
            (intp2_toNnf (.compl body) fv b c))))
  | .compl (.compl body) =>
    (intp2_compl_compl_eq body fv b c).trans
      (intp2_toNnf body fv b c)
  | .compl (.arbIr body) =>
    have: sizeOf body.compl < 1 + (1 + (sizeOf body)) :=
      Nat.lt_add_left_iff_pos.mpr zero_lt_one
    eq_intp2_compl_of_eq
      (eq_intp2_arbIr_of_eq fun dX => by
        let ih := intp2_toNnf body.compl (dX :: fv) b c
        show _ = Set.compl (intp2 (body.compl).toNnf (dX :: fv) b c)
        rw [←ih]
        show _ = (body.intp2 (dX :: fv) c b)ᶜᶜ
        rw [compl_compl])
  | .arbIr body =>
    eq_intp2_arbIr_of_eq fun dB =>
      intp2_toNnf body (dB :: fv) b c


def SingleLaneExpr.intp2_toNnf_p
  (expr: SingleLaneExpr)
  (fv: List Pair)
  (b c: Valuation Pair)
  (p: Pair)
:
  intp2 expr fv b c p = intp2 expr.toNnf fv b c p
:=
  congr (intp2_toNnf expr fv b c) rfl
