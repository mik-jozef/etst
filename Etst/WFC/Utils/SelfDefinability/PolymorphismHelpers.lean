-- TODO it would be nice to refactor this file by using the extra
-- encodings from `Etst/WFC/Utils/SelfDefinability/UniSetMapExt.lean`.
module
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
public import Etst.WFC.Utils.RulesOfInference
public import Etst.WFC.Utils.NamedDefList.NamedPairExpr
import Etst.WFC.Ch6_SelfDefinability
import Etst.WFC.Utils.Expr.FreeVars

public section
namespace Etst
open Expr


exposed pairDefList opFixHelpersDl extends uniSetMapDl
  -- See `Pair.callEnc` below.
  p3 callEnc :=
    Ex aEnc bEnc,
      × aEnc × bEnc
      × 11 × 6 × (9 × 6 × aEnc × 5 × bEnc × 2 × 0) × 2 × 0
  
  -- See `Pair.indexCall` below.
  p3 indexCallUsm :=
    Ex usmEnc fn arg,
      × usmEnc × fn × arg
      × usmEnc
      × (fn × arg × null)
      × callEnc (callEnc (0 × 1) (2 × 2)) (2 × 2)
  
  -- Named χ on the wiki's article on the Diagonal lemma.
  p3 magicUsm :=
    Ex usmEnc iFn iArg,
      × usmEnc × iFn × iArg
      × uniSetMap iFn (indexCallUsm usmEnc iArg iArg)
  
  p3 composeOp :=
    Ex iOp iArg, iOp × iArg × uniSetMap (uniSetMap iOp iArg)
  
pairDefList.

exposed def opFixDl.ofhDlEnc :=
  opFixHelpersDl.dl.prefixEncoding opFixHelpersDl.dl.size

namespace Pair
  -- Represents the encoding of `Expr.call`, see `callEnc_eq` below.
  -- The arguments are assumed to be already encoded.
  exposed def callEnc
    (fn arg: Pair)
  :
    Pair
  :=
    let enc n p := pair (.nat n) p
    let bin n l r := pair (.nat n) (.pair l r)
    let var0 := enc 2 (.nat 0)
    enc 11 (bin 6 (enc 9 (bin 6 fn (bin 5 arg var0))) var0)
  
  exposed def indexCallExpr: Expr .basic :=
    .call
      (.call
        (uniSetMapDl.cstExpr "uniSetMap")
        (.var 2)) -- Lifted twice because inside two `call`s.
      (.var 2) -- Lifted once because inside one `call`.
  
  -- Returns an index representing `uniSetMap fn arg`. `usmDlEnc` is
  -- expected to be the encoding of `uniSetMapDl` (or its extension).
  exposed def indexCall
    (fn arg: Pair)
  :
    Pair
  :=
    pair opFixDl.ofhDlEnc <|
    pair (listEncoding [fn, arg]) <|
    indexCallExpr.encoding
  
end Pair

/-
  The encoding of an application is the `callEnc` of the encodings
  of its components.
-/
theorem Expr.encoding_call_eq
  (fn arg: Expr .basic)
:
  (fn.call arg).encoding = fn.encoding.callEnc arg.encoding
:=
  rfl

/-
  A constant denotes its value; neither the background valuation,
  nor the free variables, nor the lane matter.
  TODO
-/
theorem Expr.intp_const
  {kind: ExprKind} {b c: Valuation Pair} {lane fv}
  {tag: kind.ConstTag} {x: Nat}
:
  Eq
    ((Expr.const tag x).intp lane b c fv)
    ((c x).getLane (tag.getLane lane))
:=
  rfl

open opFixDl in
exposed pairDefList opFixDl extends opFixHelpersDl
  p3 ofhDlEnc := <[ofhDlEnc.toWfNamedExpr]>
  
  p3 indexCall := indexCallUsm ofhDlEnc
  
  p3 magicIndex :=
    × ofhDlEnc
    × (ofhDlEnc × null)
    × callEnc
        (0 × <[.nat (opFixHelpersDl.const "magicUsm")]>)
        (2 × 1)
  
  p3 composeOpIndex :=
    × ofhDlEnc
    × null
    × 0 × <[.nat (opFixHelpersDl.const "composeOp")]>
  
  p3 trisetFix :=
    Ex iOp, × iOp × magicUsm ofhDlEnc iOp (indexCall magicIndex iOp)
  
  p3 indexFix :=
    Ex iOp, × iOp × trisetFix (indexCall composeOpIndex iOp)
pairDefList.

namespace opFixDl
  exposed noncomputable def magic (fn arg: Pair): Set3 Pair :=
    (((opFixDl.val "magicUsm").call ofhDlEnc).call fn).call arg
  
  /-
    An index representing `magic`, ie. `magicUsm` applied to `ofhDlEnc`.
    The latter is passed as the single free variable (which `call`
    shifts by one), so that the encoding is not duplicated.
  -/
  exposed def magicIndex: Pair :=
    .pair ofhDlEnc <|
    .pair (.pair ofhDlEnc .null) <|
    .callEnc
      (.pair (.nat 0) (.nat (opFixHelpersDl.const "magicUsm")))
      (.pair (.nat 2) (.nat 1))
  
  -- An index representing `opFixHelpersDl.composeOp`.
  exposed def composeOpIndex: Pair :=
    .pair ofhDlEnc <|
    .pair .null <|
    .pair (.nat 0) (.nat (opFixHelpersDl.const "composeOp"))
  
  exposed def composeIndex (iOp: Pair): Pair :=
    composeOpIndex.indexCall iOp
  
  
  /-
    The `uniSetMap` constant of `uniSetMapDl` denotes `uniSetMap`,
    provided the valuation does.
  -/
  theorem mem_uniSetMap_const_iff {c lane fv p}
    (cUsm: c (uniSetMapDl.const "uniSetMap") = uniSetMap)
  :
    Iff
      (p ∈ (uniSetMapDl.cstExpr "uniSetMap").intp lane c c fv)
      (p ∈ uniSetMap.getLane lane)
  :=
    Iff.of_eq (congrArg (fun s => p ∈ s.getLane lane) cUsm)
  
  theorem callEnc_ins {kind tag lane}
    (fn arg: Pair)
  :
    Set.Mem
      (opFixDl.dl.intp
          (const (kind := kind) tag (opFixDl.const "callEnc"))
          lane
          [])
      (.pair fn (.pair arg (fn.callEnc arg)))
  :=
    let inVar0 := inProd (inNat 2) (inNat 0)
    let inBin5 := inProd (inNat 5) (inProd (inVar rfl) inVar0)
    let inBin6 := inProd (inNat 6) (inProd (inVar rfl) inBin5)
    let inEnc9 := inProd (inNat 9) inBin6
    let inEncBody := inProd (inNat 6) (inProd inEnc9 inVar0)
    let inEnc11 := inProd (inNat 11) inEncBody
    let inBody := inProd (inVar rfl) (inProd (inVar rfl) inEnc11)
    DefList.in_def_no_fv (inArbUn fn (inArbUn arg inBody))
  
  theorem callEnc_elim {kind tag lane fn arg enc}
    (ins:
      Set.Mem
        (opFixDl.dl.intp
          (const (kind := kind) tag (opFixDl.const "callEnc"))
          lane
          [])
        (.pair fn (.pair arg enc))
    )
  :
    fn.callEnc arg = enc
  :=
    let ins := DefList.in_def_body_no_fv ins
    let ⟨fnWit, ins⟩ := inArbUnElim ins
    let ⟨argWit, ins⟩ := inArbUnElim ins
    let ⟨inFn, ins⟩ := inProdElim ins
    let fnEq := inVarElim inFn rfl
    let ⟨inArg, inEnc⟩ := inProdElim ins
    let argEq := inVarElim inArg rfl
    match enc with
    | .null => inProdElimNope inEnc
    | .pair tag11 encBody =>
    let ⟨inTag11, inEncBody⟩ := inProdElim inEnc
    let tag11Eq := inNatElim (n := 11) inTag11
    match encBody with
    | .null => inProdElimNope inEncBody
    | .pair tag6 encArgs =>
    let ⟨inTag6, inEncArgs⟩ := inProdElim inEncBody
    let tag6Eq := inNatElim (n := 6) inTag6
    match encArgs with
    | .null => inProdElimNope inEncArgs
    | .pair enc9 var0R =>
    let ⟨inEnc9, inVar0R⟩ := inProdElim inEncArgs
    match enc9 with
    | .null => inProdElimNope inEnc9
    | .pair tag9 bin6 =>
    let ⟨inTag9, inBin6⟩ := inProdElim inEnc9
    let tag9Eq := inNatElim (n := 9) inTag9
    match bin6 with
    | .null => inProdElimNope inBin6
    | .pair tag6L bin5Wrap =>
    let ⟨inTag6L, inBin5Wrap⟩ := inProdElim inBin6
    let tag6LEq := inNatElim (n := 6) inTag6L
    match bin5Wrap with
    | .null => inProdElimNope inBin5Wrap
    | .pair fnVar bin5 =>
    let ⟨inFnVar, inBin5⟩ := inProdElim inBin5Wrap
    let fnWitEq := inVarElim inFnVar rfl
    match bin5 with
    | .null => inProdElimNope inBin5
    | .pair tag5 bin5Args =>
    let ⟨inTag5, inBin5Args⟩ := inProdElim inBin5
    let tag5Eq := inNatElim (n := 5) inTag5
    match bin5Args with
    | .null => inProdElimNope inBin5Args
    | .pair argVar var0L =>
    let ⟨inArgVar, inVar0L⟩ := inProdElim inBin5Args
    let argWitEq := inVarElim inArgVar rfl
    match var0L, var0R with
    | .null, _ => inProdElimNope inVar0L
    | _, .null => inProdElimNope inVar0R
    | .pair tag2L tag0L, .pair tag2R tag0R =>
    let ⟨inTag2L, inTag0L⟩ := inProdElim inVar0L
    let tag2LEq := inNatElim (n := 2) inTag2L
    let tag0LEq := inNatElim (n := 0) inTag0L
    let ⟨inTag2R, inTag0R⟩ := inProdElim inVar0R
    let tag2REq := inNatElim (n := 2) inTag2R
    let tag0REq := inNatElim (n := 0) inTag0R
    let encEq:
      fnWit.callEnc argWit
        =
      tag11.pair
        (tag6.pair
          ((tag9.pair
              (tag6L.pair
                (fnVar.pair
                  (tag5.pair
                    (argVar.pair
                      (tag2L.pair tag0L)))))).pair
            (tag2R.pair tag0R)))
    := by
      rw [tag11Eq, tag6Eq, tag9Eq, tag6LEq, ←fnWitEq, tag5Eq]
      rw [←argWitEq, tag2LEq, tag0LEq, tag2REq, tag0REq]
      rfl
    fnEq ▸ argEq ▸ encEq
  
  -- TODO can it be made nicer / shorter?
  theorem intpCallEnc_singleton {lane} {left rite: Expr .basic} {pL pR: Pair}
    (inLeft: ∀ {fv}, left.intp lane opFixDl.dl.wfm opFixDl.dl.wfm fv = {pL})
    (inRite: ∀ {fv}, rite.intp lane opFixDl.dl.wfm opFixDl.dl.wfm fv = {pR})
  :
    ∀ {fv},
      (((Expr.const () (opFixDl.const "callEnc")).call left).call rite).intp
        lane opFixDl.dl.wfm opFixDl.dl.wfm fv
        =
      {pL.callEnc pR}
  :=
    fun {fv} =>
    Set.ext fun p =>
      Iff.intro
        (fun ins =>
          let inLeftArg := inCallElimSingle ins (inRite (fv := p :: fv))
          (callEnc_elim <|
            inCallElimSingle inLeftArg
              (inLeft (fv := .pair pR p :: p :: fv))).symm)
        (fun pEq =>
          pEq.symm ▸
          inCall
            (inCall
              (callEnc_ins pL pR)
              (inLeft
                (fv := .pair pR (pL.callEnc pR) :: pL.callEnc pR :: fv)
                ▸ rfl))
            (inRite (fv := pL.callEnc pR :: fv) ▸ rfl))
  
  
  /-
    The `ofhDlEnc` constant of this definition list denotes the
    encoding of the base definitions.
  -/
  theorem ofhDlEnc_ins {lane}:
    opFixDl.ofhDlEnc ∈ (opFixDl.val "ofhDlEnc").getLane lane
  :=
    DefList.in_def_no_fv (inToNamedExpr (p := opFixDl.ofhDlEnc))
  
  theorem ofhDlEnc_elim {lane p}
    (ins: p ∈ (opFixDl.val "ofhDlEnc").getLane lane)
  :
    p = opFixDl.ofhDlEnc
  :=
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    (inToNamedExprElim (p := opFixDl.ofhDlEnc) ins).symm
  
  theorem ofhDlEnc_singleton {lane fv}:
    Eq
      ((opFixDl.dl.intp (opFixDl.constExpr .basic "ofhDlEnc") lane fv))
      {opFixDl.ofhDlEnc}
  :=
    Set.ext fun _ => Iff.intro ofhDlEnc_elim (· ▸ ofhDlEnc_ins)
  
  
  /-
    The value of `indexCallUsm` on `ofhDlEnc` (introduction rule).
  -/
  theorem indexCallUsm_ins {lane} (fn arg: Pair)
  :
    Set.Mem
      ((opFixDl.val "indexCallUsm").getLane lane)
      (.pair opFixDl.ofhDlEnc (.pair fn (.pair arg (fn.indexCall arg))))
  :=
    let e1Pair: Pair := .pair (.nat 0) (.nat 1)
    let e2Pair: Pair := .pair (.nat 2) (.nat 2)
    let inEncArgs := inProd (inNat 2) (inNat 2)
    -- `callEnc (0 × 1)`
    let inInner :=
      inCall
        (callEnc_ins e1Pair e2Pair)
        (inProd (inNat 0) (inNat 1))
    -- `callEnc (0 × 1) (2 × 2)`
    let inInner := inCall inInner inEncArgs
    -- `callEnc (callEnc (0 × 1) (2 × 2))`
    let inOuter :=
      inCall (callEnc_ins (e1Pair.callEnc e2Pair) e2Pair) inInner
    -- `callEnc (callEnc (0 × 1) (2 × 2)) (2 × 2)`
    let inEncExpr := inCall inOuter inEncArgs
    DefList.in_def_no_fv
    (inArbUn opFixDl.ofhDlEnc
    (inArbUn fn
    (inArbUn arg
    (inProd (inVar rfl)
    (inProd (inVar rfl)
    (inProd (inVar rfl)
    (inProd (inVar rfl)
    (inProd
      (inProd (inVar rfl) (inProd (inVar rfl) inNull))
      inEncExpr))))))))
  
  theorem indexCall_ins {kind tag lane}
    (fn arg: Pair)
  :
    Set.Mem
      (opFixDl.dl.intp
        (const (kind := kind) tag (opFixDl.const "indexCall"))
        lane
        [])
      (.pair fn (.pair arg (fn.indexCall arg)))
  :=
    DefList.in_def_no_fv
      (inCall (indexCallUsm_ins fn arg) ofhDlEnc_ins)
  
  /-
    Members of `indexCall` are members of `indexCallUsm` applied to
    `ofhDlEnc`.
  -/
  theorem indexCall_sub_indexCallUsm {lane fn arg enc}
    (ins:
      Set.Mem
        ((opFixDl.val "indexCall").getLane lane)
        (.pair fn (.pair arg enc)))
  :
    Set.Mem
      ((opFixDl.val "indexCallUsm").getLane lane)
      (.pair opFixDl.ofhDlEnc (.pair fn (.pair arg enc)))
  :=
    let ins := DefList.in_def_body_no_fv ins
    let ⟨usmAlias, ⟨inIndexCallUsm, inOfhDl⟩⟩ := inCallElim ins
    let usmAliasEq: usmAlias = opFixDl.ofhDlEnc := ofhDlEnc_elim inOfhDl
    usmAliasEq ▸ inIndexCallUsm
  
  /-
    The value of `indexCallUsm` on `ofhDlEnc`.
  -/
  theorem indexCallUsm_elim {lane fn arg enc}
    (ins:
      Set.Mem
        ((opFixDl.val "indexCallUsm").getLane lane)
        (.pair opFixDl.ofhDlEnc (.pair fn (.pair arg enc))))
  :
    fn.indexCall arg = enc
  :=
    let ins := DefList.in_def_body_no_fv ins
    let ⟨usmBound, ins⟩ := inArbUnElim ins
    let ⟨fnBound, ins⟩ := inArbUnElim ins
    let ⟨argBound, ins⟩ := inArbUnElim ins
    let ⟨inUsm, ins⟩ := inProdElim ins
    let usmBoundEq: usmBound = opFixDl.ofhDlEnc :=
      (inVarElim inUsm rfl).symm
    let ⟨inFn, ins⟩ := inProdElim ins
    let fnBoundEq: fnBound = fn := (inVarElim inFn rfl).symm
    let ⟨inArg, ins⟩ := inProdElim ins
    let argBoundEq: argBound = arg := (inVarElim inArg rfl).symm
    match enc with
    | .null => inProdElimNope ins
    | .pair encUsm encRest =>
    let ⟨inEncUsm, inEncRest⟩ := inProdElim ins
    let encUsmEq: opFixDl.ofhDlEnc = encUsm :=
      ((inVarElim inEncUsm rfl).trans usmBoundEq).symm
    match encRest with
    | .null => inProdElimNope inEncRest
    | .pair encFv encExpr =>
    let ⟨inEncFv, inEncExpr⟩ := inProdElim inEncRest
    match encFv with
    | .null => inProdElimNope inEncFv
    | .pair fvFn fvRest =>
    let ⟨inFvFn, inFvRest⟩ := inProdElim inEncFv
    let fvFnEq: fn = fvFn :=
      ((inVarElim inFvFn rfl).trans fnBoundEq).symm
    match fvRest with
    | .null => inProdElimNope inFvRest
    | .pair fvArg fvNull =>
    let ⟨inFvArg, inFvNull⟩ := inProdElim inFvRest
    let fvArgEq: arg = fvArg :=
      ((inVarElim inFvArg rfl).trans argBoundEq).symm
    let fvNullEq: Pair.null = fvNull := (inNullElim inFvNull).symm
    -- The encoded expression is the encoding of `uniSetMap fn arg`.
    let e1Pair: Pair := Pair.pair (Pair.nat 0) (Pair.nat 1)
    let e2Pair: Pair := Pair.pair (Pair.nat 2) (Pair.nat 2)
    let ⟨exprFn1, ⟨inExprFn1, inE2Mem1⟩⟩ := inCallElim inEncExpr
    let exprFn1Eq: e2Pair = exprFn1 :=
      inToExprElim (pExpr := e2Pair) inE2Mem1
    let inExprFn1 := exprFn1Eq.symm ▸ inExprFn1
    let ⟨exprFn2, ⟨inCallEncOuter, inD3Mem⟩⟩ := inCallElim inExprFn1
    let callEqOuter: exprFn2.callEnc e2Pair = encExpr :=
      callEnc_elim inCallEncOuter
    let ⟨exprFn3, ⟨inExprFn3, inE2Mem3⟩⟩ := inCallElim inD3Mem
    let exprFn3Eq: e2Pair = exprFn3 :=
      inToExprElim (pExpr := e2Pair) inE2Mem3
    let inExprFn3 := exprFn3Eq.symm ▸ inExprFn3
    let ⟨exprFn4, ⟨inCallEncInner, inE1Mem⟩⟩ := inCallElim inExprFn3
    let callEqInner: exprFn4.callEnc e2Pair = exprFn2 :=
      callEnc_elim inCallEncInner
    let exprFn4Eq: e1Pair = exprFn4 :=
      inToExprElim (pExpr := e1Pair) inE1Mem
    let callEqInner := exprFn4Eq.symm ▸ callEqInner
    let callEqOuter := callEqInner.symm ▸ callEqOuter
    let exprEq:
      Expr.encoding
        (.call
          (.call (uniSetMapDl.cstExpr "uniSetMap") (.var 2))
          (.var 2))
        =
      encExpr
    :=
      (Expr.encoding_call_eq
        (.call (uniSetMapDl.cstExpr "uniSetMap") (.var 2))
        (.var 2)).trans <|
      (congrArg
        (fun enc => enc.callEnc (Expr.encoding (.var 2)))
        (Expr.encoding_call_eq
          (uniSetMapDl.cstExpr "uniSetMap")
          (.var 2))).trans
      callEqOuter
    let fvEq:
      Pair.pair fn (.pair arg .null)
        =
      Pair.pair fvFn (.pair fvArg fvNull)
    :=
      Pair.eq fvFnEq (Pair.eq fvArgEq fvNullEq)
    Pair.eq encUsmEq (Pair.eq fvEq exprEq)
  
  theorem indexCall_elim {lane fn arg enc}
    (ins:
      Set.Mem
        ((opFixDl.val "indexCall").getLane lane)
        (.pair fn (.pair arg enc)))
  :
    fn.indexCall arg = enc
  :=
    indexCallUsm_elim (indexCall_sub_indexCallUsm ins)
  
  /-
    The expression `Pair.indexCall` encodes satisfies
    `uniSetMap fn arg`, as long as the valuation interprets the
    `uniSetMap` constant correctly.
  -/
  theorem indexCallExpr_iff {c lane iFn iArg}
    (cUsm: c (uniSetMapDl.const "uniSetMap") = uniSetMap)
    (p: Pair)
  :
    Iff
      (p ∈ Pair.indexCallExpr.intp lane c c [iFn, iArg])
      (p ∈ ((uniSetMap.call iFn).call iArg).getLane lane)
  :=
    Iff.intro
      (fun ins =>
        let ⟨pA, ⟨inInner, inArgMem⟩⟩ := inCallElim ins
        let pAEq: pA = iArg := inVarElim inArgMem rfl
        let inInner := pAEq ▸ inInner
        let ⟨pB, ⟨inUsm, inFnMem⟩⟩ := inCallElim inInner
        let pBEq: pB = iFn := inVarElim inFnMem rfl
        let inUsm := pBEq ▸ inUsm
        (mem_uniSetMap_const_iff cUsm).mp inUsm)
      (fun ins =>
        let inUsm := (mem_uniSetMap_const_iff cUsm).mpr ins
        inCall (inCall inUsm (inVar rfl)) (inVar rfl))
  
  theorem indexCall_correct
    (fn arg: Pair)
  :
    uniSetMap.call (fn.indexCall arg) = (uniSetMap.call fn).call arg
  :=
    let expr: Expr .basic :=
      (uniSetMapDl.cstExpr "uniSetMap").call (.var 2) |>.call (.var 2)
    let cUsm:
      opFixHelpersDl.dl.wfm (uniSetMapDl.const "uniSetMap") = uniSetMap
    :=
      opFixHelpersDl.extend_wfm_eq uniSetMapDl "uniSetMap"
    (opFixHelpersDl.dl.uniSetMapAt_eq [fn, arg] expr).trans <|
    Set3.eq
      (Set.ext fun p => indexCallExpr_iff cUsm p)
      (Set.ext fun p => indexCallExpr_iff cUsm p)
  
  def indexCall_call {kind}
    (tag: kind.ConstTag)
    (fn arg: Expr kind)
  :
    Expr kind
  :=
    ((const tag (opFixDl.const "indexCall")).call fn).call arg
  
  theorem indexCall_singleton {kind lane fv iFn iArg}
    {fn arg: Expr kind}
    {tag: kind.ConstTag}
    (inFn:
      ∀ pRes,
        opFixDl.dl.intp fn lane (.pair iArg pRes :: pRes :: fv) = {iFn})
    (inArg:
      ∀ pRes,
      opFixDl.dl.intp arg lane (pRes :: fv) = {iArg})
  :
    Eq
      (opFixDl.dl.intp (indexCall_call tag fn arg)
        lane
        fv)
      {iFn.indexCall iArg}
  := by
    unfold DefList.intp at inFn inArg
    exact Set.ext fun p => Iff.intro
      (fun inIndexCall =>
        let inInnerCall := inCallElimSingle inIndexCall (inArg p)
        let inConstIndexCall :=
          inCallElimSingle inInnerCall (inFn p)
        (indexCall_elim inConstIndexCall).symm)
      (fun pEq =>
        pEq ▸
        inCall
          (inCall
            (indexCall_ins iFn iArg)
            ((inFn (iFn.indexCall iArg)) ▸ rfl))
          ((inArg (iFn.indexCall iArg)) ▸ rfl))
  
  
  exposed def magicUsmBodyExpr: Expr .basic :=
    p3(usmEnc, fn, arg; uniSetMap fn (indexCallUsm usmEnc arg arg))
    |>.compile opFixDl.consts
  
  -- `magicUsm`'s body denotes `uniSetMap iFn (iArg.indexCall iArg)`.
  theorem magicUsmBodyExpr_iff {lane} (iFn iArg p: Pair):
    Iff
      (Set.Mem
        (magicUsmBodyExpr.intp lane
          opFixDl.dl.wfm opFixDl.dl.wfm
          [iArg, iFn, opFixDl.ofhDlEnc])
        p)
      (p ∈ ((uniSetMap.call iFn).call (iArg.indexCall iArg)).getLane lane)
  :=
    let usmEq := opFixDl.extend_wfm_eq uniSetMapDl "uniSetMap"
    Iff.intro
      (fun insBody =>
        let ⟨res, ⟨inFnApp, inArgApp⟩⟩ := inCallElim insBody
        let ⟨argEnd, ⟨inA1, inArgEndMem⟩⟩ := inCallElim inArgApp
        let argEndEq: argEnd = iArg := inVarElim inArgEndMem rfl
        let inA1 := argEndEq ▸ inA1
        let ⟨argMid, ⟨inA2, inArgMidMem⟩⟩ := inCallElim inA1
        let argMidEq: argMid = iArg := inVarElim inArgMidMem rfl
        let inA2 := argMidEq ▸ inA2
        let ⟨usmArg, ⟨inVal, inUsmArgMem⟩⟩ := inCallElim inA2
        let usmArgEq: usmArg = opFixDl.ofhDlEnc := inVarElim inUsmArgMem rfl
        let inVal := usmArgEq ▸ inVal
        let resEq: res = iArg.indexCall iArg :=
          (indexCallUsm_elim inVal).symm
        let inFnApp := resEq ▸ inFnApp
        let ⟨fnArg, ⟨inUsmMem, inFnArgMem⟩⟩ := inCallElim inFnApp
        let fnArgEq: fnArg = iFn := inVarElim inFnArgMem rfl
        let inUsmMem := fnArgEq ▸ inUsmMem
        (mem_uniSetMap_const_iff usmEq).mp inUsmMem)
      (fun ins =>
        let inUsmT := (mem_uniSetMap_const_iff usmEq).mpr ins
        let inFnApp := inCall inUsmT (inVar rfl)
        let inArgApp :=
          inCall
            (inCall
              (inCall
                (fn := .const .basic (opFixDl.const "indexCallUsm"))
                (indexCallUsm_ins (lane := lane) iArg iArg)
                (inVar rfl))
              (inVar rfl))
            (inVar rfl)
        inCall inFnApp inArgApp)
  
  theorem magic_ins {lane p iFn iArg}
    (ins: p ∈ ((uniSetMap.call iFn).call (iArg.indexCall iArg)).getLane lane)
  :
    p ∈ (magic iFn iArg).getLane lane
  :=
    let inBody:
      p ∈ magicUsmBodyExpr.intp lane
        opFixDl.dl.wfm opFixDl.dl.wfm
        [iArg, iFn, opFixDl.ofhDlEnc]
    :=
      (magicUsmBodyExpr_iff iFn iArg p).mpr ins
    DefList.in_def_no_fv <|
    inArbUn opFixDl.ofhDlEnc <|
    inArbUn iFn <|
    inArbUn iArg <|
    inProd (inVar rfl) <|
    inProd (inVar rfl) <|
    inProd (inVar rfl) inBody
  
  theorem magic_elim {lane p iFn iArg}
    (ins: p ∈ (magic iFn iArg).getLane lane)
  :
    p ∈ ((uniSetMap.call iFn).call (iArg.indexCall iArg)).getLane lane
  :=
    let ins := DefList.in_def_body_no_fv ins
    let ⟨usmBound, ins⟩ := inArbUnElim ins
    let ⟨fnBound, ins⟩ := inArbUnElim ins
    let ⟨argBound, ins⟩ := inArbUnElim ins
    let ⟨inUsm, ins⟩ := inProdElim ins
    let usmBoundEq: usmBound = opFixDl.ofhDlEnc :=
      (inVarElim inUsm rfl).symm
    let ⟨inFn, ins⟩ := inProdElim ins
    let fnBoundEq: fnBound = iFn := (inVarElim inFn rfl).symm
    let ⟨inArg, ins⟩ := inProdElim ins
    let argBoundEq: argBound = iArg := (inVarElim inArg rfl).symm
    let ins: p ∈ magicUsmBodyExpr.intp lane
        opFixDl.dl.wfm opFixDl.dl.wfm
        [iArg, iFn, opFixDl.ofhDlEnc]
    :=
      argBoundEq ▸ fnBoundEq ▸ usmBoundEq ▸ ins
    (magicUsmBodyExpr_iff iFn iArg p).mp ins
  
  theorem magic_call_eq
    (iFn iArg: Pair)
  :
    magic iFn iArg = (uniSetMap.call iFn).call (iArg.indexCall iArg)
  :=
    Set3.eq4
      (fun _ => magic_elim (lane := .defLane))
      (fun _ => magic_ins (lane := .defLane))
      (fun _ => magic_elim (lane := .posLane))
      (fun _ => magic_ins (lane := .posLane))
  
  theorem magicIndex_val:
    uniSetMap.call magicIndex = (opFixDl.val "magicUsm").call ofhDlEnc
  :=
    let x := opFixHelpersDl.const "magicUsm"
    let constCallEqMem {lane c} (p r: Pair):
      Iff
        (r ∈ (Expr.call (.const .basic x) (.var 1)).intp lane c c [p])
        (.pair p r ∈ (c x).getLane lane)
    :=
      Iff.intro
        (fun h =>
          let ⟨a, ⟨inFn, inArg⟩⟩ := inCallElim h
          let aEq: a = p := inVarElim inArg rfl
          aEq ▸ inFn)
        (fun h => inCall h (inVar rfl))
    let constCallEq {c} (p):
      Eq
        (((const () x).call (.var 1)).triIntp c c [p])
        ((c x).call p)
    :=
      Set3.eq
        (Set.ext fun r => constCallEqMem p r)
        (Set.ext fun r => constCallEqMem p r)
    let expr: Expr .basic := .call (.const () x) (.var 1)
    let eqIndexAt :=
      congrArg (fun i => uniSetMap.call i) rfl
    let eqAt :=
      opFixHelpersDl.dl.uniSetMapAt_eq [opFixDl.ofhDlEnc] expr
    (eqIndexAt.trans eqAt).trans <|
    (constCallEq opFixDl.ofhDlEnc).trans <|
    congrArg
      (fun s => s.call ofhDlEnc)
      (opFixHelpersDl.extend_wfm_eq opFixDl "magicUsm")
  
  theorem magicIndexBody_singleton {lane}:
    Eq
      (opFixDl.dl.intp (opFixDl.getDef "magicIndex") lane [])
      {opFixDl.magicIndex}
  :=
    prod_singleton
      ofhDlEnc_singleton
      (prod_singleton
        (prod_singleton
          ofhDlEnc_singleton
          null_singleton)
        (intpCallEnc_singleton
          (prod_singleton
            null_singleton
            (nat_singleton 4))
          (prod_singleton
            (nat_singleton 2)
            (nat_singleton 1))))
  
  
  theorem composeOp_ins {iOp iArg lane p}
    (ins:
      Set.Mem
        ((uniSetMap.flatCall ((uniSetMap.call iOp).call iArg)).getLane
          lane)
        p)
  :
    p ∈ (((opFixDl.val "composeOp").call iOp).call iArg).getLane lane
  :=
    let ⟨q, inQ, inUsm⟩ := Set3.inFlatCallElim ins
    let eqUni := uniSetMapDl.extend_wfm_eq opFixDl "uniSetMap"
    let insInner:
      ((opFixDl.dl.wfm (opFixDl.const "uniSetMap")).getLane lane).Mem
        (.pair iOp (.pair iArg q))
    :=
      eqUni.symm ▸ inQ
    let insOuter:
      Set.Mem
        ((opFixDl.dl.wfm (opFixDl.const "uniSetMap")).getLane lane)
        (.pair q p)
    :=
      eqUni.symm ▸ inUsm
    let inComposeCall :=
      inCall
        insOuter
        (inCall
          (inCall
            insInner
            (inVar rfl))
          (inVar rfl))
    DefList.in_def_no_fv <|
    inArbUn iOp <|
    inArbUn iArg <|
    inProd
      (inVar rfl)
      (inProd (inVar rfl) inComposeCall)
  
  theorem composeOp_elim {iOp iArg lane p}
    (ins:
      p ∈ (((opFixDl.val "composeOp").call iOp).call iArg).getLane lane)
  :
    Set.Mem
      (Set3.getLane
        (uniSetMap.flatCall ((uniSetMap.call iOp).call iArg))
        lane)
      p
  :=
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    let ⟨opAlias, ins⟩ := inArbUnElim ins
    let ⟨argAlias, ins⟩ := inArbUnElim ins
    let ⟨inVarOp, ins⟩ := inProdElim ins
    let ⟨inVarArg, ins⟩ := inProdElim ins
    let opEq := inVarElim inVarOp rfl
    let argEq := inVarElim inVarArg rfl
    let ⟨qAlias, ⟨inOuterFn, inInnerCall⟩⟩ := inCallElim ins
    let ⟨argAlias2, ⟨inMidFn, inArgVar⟩⟩ := inCallElim inInnerCall
    let argAlias2Eq := inVarElim inArgVar rfl
    let ⟨opAlias2, ⟨inUsmConst, inOpVar⟩⟩ := inCallElim inMidFn
    let opAlias2Eq := inVarElim inOpVar rfl
    let eqUni := uniSetMapDl.extend_wfm_eq opFixDl "uniSetMap"
    let inUsmConst:
      ((uniSetMapDl.dl.wfm (opFixDl.const "uniSetMap")).getLane lane).Mem
        (.pair opAlias2 (.pair argAlias2 qAlias))
    :=
      eqUni ▸ inUsmConst
    let inOuterFn:
      Set.Mem
        ((uniSetMapDl.dl.wfm (opFixDl.const "uniSetMap")).getLane lane)
        (.pair qAlias p)
    :=
      eqUni ▸ inOuterFn
    let inQ: qAlias ∈ ((uniSetMap.call iOp).call iArg).getLane lane :=
      opEq ▸ argEq ▸ opAlias2Eq ▸ argAlias2Eq ▸ inUsmConst
    Set3.inFlatCall inQ inOuterFn
  
  theorem composeOp_call_eq
    (iOp iArg: Pair)
  :
    Eq
      (((opFixDl.val "composeOp").call iOp).call iArg)
      (uniSetMap.flatCall ((uniSetMap.call iOp).call iArg))
  :=
    Set3.eq4
      (fun _ => composeOp_elim (lane := .defLane))
      (fun _ => composeOp_ins (lane := .defLane))
      (fun _ => composeOp_elim (lane := .posLane))
      (fun _ => composeOp_ins (lane := .posLane))
  
  theorem composeIndex_call
    (iOp iArg: Pair)
  :
    Eq
      ((uniSetMap.call (composeIndex iOp)).call iArg)
      (uniSetMap.flatCall ((uniSetMap.call iOp).call iArg))
  :=
    let eqCall := indexCall_correct composeOpIndex iOp
    let eqComposeOpParent :=
      opFixHelpersDl.dl.uniSetMapAt_eq
        []
        (.const () (opFixDl.const "composeOp"))
    let eqComposeOpChild :=
      opFixHelpersDl.extend_wfm_eq opFixDl "composeOp"
    let eqHead:
      uniSetMap.call composeOpIndex = (opFixDl.val "composeOp")
    :=
      eqComposeOpParent.trans eqComposeOpChild
    (congrArg (fun s => Set3.call s iArg) eqCall).trans
      ((congrArg (fun s => (Set3.call s iOp).call iArg) eqHead).trans
        (composeOp_call_eq iOp iArg))
  
  theorem composeOpIndex_singleton {lane fv}:
    Eq
      (opFixDl.dl.intp
        (opFixDl.constExpr .basic "composeOpIndex")
        lane
        fv)
      {opFixDl.composeOpIndex}
  :=
    const_singleton <|
    prod_singleton
      ofhDlEnc_singleton
      (prod_singleton
        null_singleton
        (prod_singleton
          null_singleton
          (nat_singleton 5)))
  
  
  exposed def trisetFixIndex (iFn: Pair): Pair :=
    (magicIndex.indexCall iFn).indexCall (magicIndex.indexCall iFn)
  
  theorem trisetFixIndex_eq
    (iFn: Pair)
  :
    Eq
      (uniSetMap.call (trisetFixIndex iFn))
      (magic iFn (magicIndex.indexCall iFn))
  :=
    let iCall := magicIndex.indexCall iFn
    (indexCall_correct iCall iCall).trans <|
    (congrArg
      (fun s => s.call iCall)
      (indexCall_correct magicIndex iFn)).trans <|
    congrArg
      (fun s => (s.call iFn).call iCall)
      magicIndex_val
  
  /-
    The `indexCall magicIndex iOp` argument of `trisetFix`, where `iOp`
    is `var 2` under the two enclosing `call` binders.
  -/
  theorem indexCallMagicIndex_eq {lane iFn p}
  :
    Eq
      (Expr.intp
        (indexCall_call .basic
          (opFixDl.constExpr () "magicIndex")
          (.var 2))
        lane
        opFixDl.dl.wfm
        opFixDl.dl.wfm
        (p :: [iFn]))
      {opFixDl.magicIndex.indexCall iFn}
  :=
    indexCall_singleton
      (fun _ => const_singleton magicIndexBody_singleton)
      (fun _ => var_singleton rfl)
  
  theorem trisetFix_ins {lane p iFn}
    (ins: p ∈ (magic iFn (magicIndex.indexCall iFn)).getLane lane)
  :
    p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane
  :=
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl) <|
    inCall
      (inCall (inCall ins ofhDlEnc_ins) (inVar rfl))
      (indexCallMagicIndex_eq ▸ rfl)
  
  theorem trisetFix_elim {lane p iFn}
    (ins: p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane)
  :
    p ∈ (magic iFn (magicIndex.indexCall iFn)).getLane lane
  :=
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    let ⟨iOp, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    let ins :=
      inCallElimSingle ins
        (indexCallMagicIndex_eq (lane := lane) (iFn := iOp) (p := p))
    let ins := inCallElimSingle ins (var_singleton rfl)
    let ins := inCallElimSingle ins ofhDlEnc_singleton
    iEq ▸ ins
  
  theorem trisetFix_call_eq
    (iFn: Pair)
  :
    Eq
      ((opFixDl.val "trisetFix").call iFn)
      (uniSetMap.call (trisetFixIndex iFn))
  :=
    Set3.eq4
      (fun _ ins =>
        trisetFixIndex_eq iFn ▸ trisetFix_elim (lane := .defLane) ins)
      (fun _ ins =>
        trisetFix_ins (lane := .defLane) (trisetFixIndex_eq iFn ▸ ins))
      (fun _ ins =>
        trisetFixIndex_eq iFn ▸ trisetFix_elim (lane := .posLane) ins)
      (fun _ ins =>
        trisetFix_ins (lane := .posLane) (trisetFixIndex_eq iFn ▸ ins))
  
  
  /-
    The `indexCall composeOpIndex iOp` argument of `indexFix`, where
    `iOp` is `var 2` under the two enclosing `call` binders.
  -/
  theorem indexCallComposeOpIndex_eq {lane iOp p}
  :
    Eq
      (Expr.intp
        (indexCall_call .basic
          (opFixDl.constExpr () "composeOpIndex")
          (.var 2))
        lane
        opFixDl.dl.wfm
        opFixDl.dl.wfm
        (p :: [iOp]))
      {opFixDl.composeOpIndex.indexCall iOp}
  :=
    indexCall_singleton
      (fun _ => composeOpIndex_singleton)
      (fun _ => var_singleton rfl)
  
  theorem indexFix_ins {iOp lane p}
    (ins:
      Set.Mem
        (Set3.getLane
          ((opFixDl.val "trisetFix").call (composeIndex iOp))
          lane)
        p)
  :
    p ∈ ((opFixDl.val "indexFix").call iOp).getLane lane
  :=
    DefList.in_def_no_fv <|
    inArbUn iOp <|
    inProd (inVar rfl) <|
    inCall ins (indexCallComposeOpIndex_eq ▸ rfl)
  
  theorem indexFix_elim {iOp lane p}
    (ins: p ∈ ((opFixDl.val "indexFix").call iOp).getLane lane)
  :
    p ∈ ((opFixDl.val "trisetFix").call (composeIndex iOp)).getLane lane
  :=
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    let ⟨_, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    iEq ▸ inCallElimSingle ins indexCallComposeOpIndex_eq

  
  theorem indexFix_call_eq
    (iOp: Pair)
  :
    Eq
      ((opFixDl.val "indexFix").call iOp)
      ((opFixDl.val "trisetFix").call (composeIndex iOp))
  :=
    Set3.eq4
      (fun _ => indexFix_elim)
      (fun _ => indexFix_ins)
      (fun _ => indexFix_elim)
      (fun _ => indexFix_ins)
  
end opFixDl
