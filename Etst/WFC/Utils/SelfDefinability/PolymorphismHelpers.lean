-- TODO eventually, rewrite this file with the extra encoding cases
-- to reduce the huge size of opFixDl.
-- See `Etst/WFC/Utils/SelfDefinability/UniSetMapExt.lean`
module
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
public import Etst.WFC.Utils.RulesOfInference
public import Etst.WFC.Utils.NamedDefList.NamedPairExpr
import Etst.WFC.Ch6_SelfDefinability
import Etst.WFC.Utils.Expr.FreeVars

public section
namespace Etst


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
  
  -- Returns an index representing `uniSetMap fn arg`.
  exposed def indexCall
    (fn arg: Pair)
  :
    Pair
  :=
    uniSetMapIndex
      uniSetMapDl.dl.toDefList
      uniSetMapDl.dl.size
      []
      (((uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr).call arg.toExpr)
  
end Pair

theorem Expr.callEnc_eq
  (fn arg: Expr .basic)
:
  fn.encoding.callEnc arg.encoding = (fn.call arg).encoding
:=
  rfl

theorem Expr.prod_call_expr_call_eq {kind}
  (fn: Expr kind)
  (fnIsClean: fn.IsClean)
  (arg: Pair)
  (lane: kind.Lane)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  Eq
    ((fn.call arg.toExpr).intp lane b c fv)
    (Pair.setCall (fn.intp lane b c fv) arg)
:=
  Set.Subset.antisymm
    (fun _ inCall =>
      fnIsClean.intp_eq ▸
      inCallElimSingle inCall (intp_toExpr_eq_singleton arg))
    (fun _ inFn =>
      inCall (fnIsClean.intp_eq ▸ inFn) (inToExpr arg))

theorem Expr.prod_call_expr_call_eq3
  (fn: Expr .basic)
  (fnIsClean: fn.IsClean)
  (arg: Pair)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  Eq
    ((fn.call arg.toExpr).triIntp b c fv)
    ((fn.triIntp b c fv).call arg)
:=
  Set3.eq
    (fn.prod_call_expr_call_eq fnIsClean arg .defLane b c fv)
    (fn.prod_call_expr_call_eq fnIsClean arg .posLane b c fv)


exposed def uniSetMapDlEncoding :=
  uniSetMapDl.dl.prefixEncoding uniSetMapDl.dl.size

open uniSetMapDl in
exposed pairDefList opFixHelpersDl extends uniSetMapDl
  -- Converts a pair to an encoding of an expression that evaluates to it.
  p3 encodeAsExpr :=
  | null × 4 × null
  | Ex l r, (l × r) × 5 × encodeAsExpr l × encodeAsExpr r
  
  p3 callEnc :=
    Ex aEnc bEnc,
      × aEnc × bEnc
      × 11 × 6 × (9 × 6 × aEnc × 5 × bEnc × 2 × 0) × 2 × 0
  
  p3 indexCall :=
    Ex fn arg,
      × fn × arg
      × <[uniSetMapDlEncoding.toNamedExpr]>
      × null
      × callEnc
          (callEnc
            <[((cstExpr "uniSetMap").encoding.toNamedExpr)]>
            (encodeAsExpr fn))
          (encodeAsExpr arg)
  
  -- Named χ on the wiki's article on the Diagonal lemma:
  p3 magic :=
    Ex iFn iArg, iFn × iArg × uniSetMap iFn (indexCall iArg iArg)
  
  p3 composeOp :=
    Ex iOp iArg, iOp × iArg × uniSetMap (uniSetMap iOp iArg)
pairDefList.

-- An index representing `opFixHelpersDl.magic`.
exposed def opFixDl.magicIndex: Pair :=
  (uniSetMapIndex
    opFixHelpersDl.dl.toDefList
    opFixHelpersDl.dl.size
    []
    (.const () (opFixHelpersDl.const "magic")))

exposed def opFixDl.composeOpIndex: Pair :=
  uniSetMapIndex
    opFixHelpersDl.dl.toDefList
    opFixHelpersDl.dl.size
    []
    (.const () (opFixHelpersDl.const "composeOp"))

exposed def opFixDl.composeIndex (iOp: Pair): Pair :=
  composeOpIndex.indexCall iOp


open opFixDl in
exposed pairDefList opFixDl extends opFixHelpersDl
  p3 trisetFix :=
    Ex iOp,
      × iOp
      × magic iOp (indexCall <[magicIndex.toNamedExpr]> iOp)
  
  p3 indexFix :=
    Ex iOp,
      × iOp
      × trisetFix (indexCall <[composeOpIndex.toNamedExpr]> iOp)
pairDefList.

def Pair.size: Pair → Nat
| .null => 1
| .pair a b => a.size + b.size + 1

def Expr.size {kind}: Expr kind → Nat
| .const _ _ => 1
| .var _ => 1
| .null => 1
| .prod a b => a.size + b.size + 1
| .ir a b => a.size + b.size + 1
| .full a => a.size + 1
| .compl a => a.size + 1
| .arbIr a => a.size + 1

-- #eval "indexCall size: " ++ (opFixHelpersDl.getDef "indexCall").size.repr
-- #eval "magicIndex size: " ++ opFixDl.magicIndex.size.repr
-- #eval "composeOpIndex size: " ++ opFixDl.composeOpIndex.size.repr


namespace opFixDl
  open Expr
  
  -- TODO should I cover both basic and lane expressions?
  theorem encodeAsExpr_ins (p: Pair) {kind tag lane}:
    Set.Mem
      (opFixDl.dl.intp
        (const (kind := kind) tag (opFixDl.const "encodeAsExpr"))
        lane
        [])
      (.pair p p.toExpr.encoding)
  :=
    DefList.in_def_no_fv
    (match p with
    | .null => inUnL (inProd inNull (inProd (inNat 4) inNull))
    | .pair l r =>
      let ihL := inCall (encodeAsExpr_ins l) (inVar rfl)
      let ihR := inCall (encodeAsExpr_ins r) (inVar rfl)
      let inRet := inProd (inNat 5) (inProd ihL ihR)
      inUnR (inArbUn l (inArbUn r (inProd (inProd rfl rfl) inRet))))
  
  theorem encodeAsExpr_elim {kind tag lane p enc}
    (ins:
      Set.Mem
        (opFixDl.dl.intp
          (const (kind := kind) tag (opFixDl.const "encodeAsExpr"))
          lane
          [])
        (.pair p enc))
  :
    p.toExpr.encoding = enc
  :=
    match p with
    | .null =>
      let ins := DefList.in_def_body_no_fv ins
      (inUnElim ins).elim
        (fun ins =>
          let ⟨_, inEnc⟩ := inProdElim ins
          match enc with
          | .pair _ _ =>
          let ⟨inTag, inNullEnc⟩ := inProdElim inEnc
          let tagEq := inNatElim (n := 4) inTag
          let argEq := inNullElim inNullEnc
          tagEq ▸ argEq.symm ▸ rfl)
        (fun ins =>
          let ⟨_, ins⟩ := inArbUnElim ins
          let ⟨_, ins⟩ := inArbUnElim ins
          let ⟨inProdP, _⟩ := inProdElim ins
          inProdElimNope inProdP)
    | .pair l r =>
      let ins := DefList.in_def_body_no_fv ins
      (inUnElim ins).elim
        (fun ins =>
          let ⟨inProdP, _⟩ := inProdElim ins
          inNullElimNope inProdP)
        (fun ins =>
          let ⟨lWit, ins⟩ := inArbUnElim ins
          let ⟨rWit, ins⟩ := inArbUnElim ins
          let ⟨inProdP, inEnc⟩ := inProdElim ins
          let ⟨_, _, pEq, inLeft, inRite⟩ := inProdElimEx inProdP
          let ⟨lEq, rEq⟩ := Pair.noConfusion pEq And.intro
          match enc with
          | .pair _ (.pair _ _) =>
          let ⟨inTag, inArg⟩ := inProdElim inEnc
          let tagEq := inNatElim (n := 5) inTag
          let ⟨inLeftEnc, inRiteEnc⟩ := inProdElim inArg
          let pLEq := inVarElim inLeft rfl
          let pREq := inVarElim inRite rfl
          let insLeft := inCallElimSingle inLeftEnc rfl
          let insRite := inCallElimSingle inRiteEnc rfl
          let ihL := encodeAsExpr_elim insLeft
          let ihR := encodeAsExpr_elim insRite
          let lWitEq: lWit = l := pLEq.symm.trans lEq.symm
          let rWitEq: rWit = r := pREq.symm.trans rEq.symm
          lWitEq ▸ rWitEq ▸ tagEq ▸ ihL ▸ ihR ▸ rfl)
  
  
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
    | .pair tag11 encBody =>
    let ⟨inTag11, inEncBody⟩ := inProdElim inEnc
    let tag11Eq := inNatElim (n := 11) inTag11
    match encBody with
    | .pair tag6 encArgs =>
    let ⟨inTag6, inEncArgs⟩ := inProdElim inEncBody
    let tag6Eq := inNatElim (n := 6) inTag6
    match encArgs with
    | .pair enc9 var0R =>
    let ⟨inEnc9, inVar0R⟩ := inProdElim inEncArgs
    match enc9 with
    | .pair tag9 bin6 =>
    let ⟨inTag9, inBin6⟩ := inProdElim inEnc9
    let tag9Eq := inNatElim (n := 9) inTag9
    match bin6 with
    | .pair tag6L bin5Wrap =>
    let ⟨inTag6L, inBin5Wrap⟩ := inProdElim inBin6
    let tag6LEq := inNatElim (n := 6) inTag6L
    match bin5Wrap with
    | .pair fnVar bin5 =>
    let ⟨inFnVar, inBin5⟩ := inProdElim inBin5Wrap
    let fnWitEq := inVarElim inFnVar rfl
    match bin5 with
    | .pair tag5 bin5Args =>
    let ⟨inTag5, inBin5Args⟩ := inProdElim inBin5
    let tag5Eq := inNatElim (n := 5) inTag5
    match bin5Args with
    | .pair argVar var0L =>
    let ⟨inArgVar, inVar0L⟩ := inProdElim inBin5Args
    let argWitEq := inVarElim inArgVar rfl
    match var0L, var0R with
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
    let inUsmConstEnc :=
      inToExpr (uniSetMapDl.cstExpr "uniSetMap").encoding
    let inFnEnc := inCall (encodeAsExpr_ins fn) (inVar rfl)
    let inArgEnc := inCall (encodeAsExpr_ins arg) (inVar rfl)
    let inInnerCall :=
      inCall
        (inCall
          (callEnc_ins
            (uniSetMapDl.cstExpr "uniSetMap").encoding
            fn.toExpr.encoding)
          inUsmConstEnc)
        inFnEnc
    let inExprEnc :=
      inCall
        (inCall
          (callEnc_ins
            ((uniSetMapDl.cstExpr "uniSetMap").encoding.callEnc
              fn.toExpr.encoding)
            arg.toExpr.encoding)
          inInnerCall)
        inArgEnc
    DefList.in_def_no_fv
    (inArbUn fn
    (inArbUn arg
    (inProd (inVar rfl)
    (inProd (inVar rfl)
    (inProd (inToNamedExpr uniSetMapDlEncoding)
    (inProd inNull inExprEnc))))))
  
  -- TODO perhaps generalize to arbitrary lanes?
  theorem indexCall_elim {fn arg enc}
    (ins: .pair fn (.pair arg enc) ∈ (opFixDl.val "indexCall").posMem)
  :
    fn.indexCall arg = enc
  :=
    let ins := DefList.in_def_body_no_fv (lane := .posLane) ins
    let ⟨fnWit, ins⟩ := inArbUnElim ins
    let ⟨argWit, ins⟩ := inArbUnElim ins
    let ⟨inFn, ins⟩ := inProdElim ins
    let fnEq := inVarElim inFn rfl
    let ⟨inArg, inEnc⟩ := inProdElim ins
    let argEq := inVarElim inArg rfl
    match enc with
    | .pair dlEnc encTail =>
    let ⟨inDlEnc, inEncTail⟩ := inProdElim inEnc
    let dlEq := inToExprElim inDlEnc
    match encTail with
    | .null => inProdElimNope inEncTail
    | .pair fvEnc exprEnc =>
    let ⟨inFvEnc, inExprEnc⟩ := inProdElim inEncTail
    let fvEq := inNullElim inFvEnc

    let ⟨argEncAlias, ⟨inOuterFn, inArgExpr⟩⟩ := inCallElim inExprEnc
    let ⟨argAlias, ⟨inConstEncodeAsExprArg, inArgVar⟩⟩ :=
      inCallElim inArgExpr
    let argAliasEq := inVarElim inArgVar rfl
    let argEncEq := encodeAsExpr_elim inConstEncodeAsExprArg

    let ⟨fnIndexCallAlias, ⟨inOuterConstCallEnc, inFnExpr⟩⟩ :=
      inCallElim inOuterFn
    let outerCallEq := callEnc_elim inOuterConstCallEnc

    let ⟨fnEncAlias, ⟨inInnerFn, inFnEncExpr⟩⟩ := inCallElim inFnExpr
    let ⟨fnAlias, ⟨inConstEncodeAsExprFn, inFnVar⟩⟩ :=
      inCallElim inFnEncExpr
    let fnAliasEq := inVarElim inFnVar rfl
    let fnEncEq := encodeAsExpr_elim inConstEncodeAsExprFn

    let ⟨usmConstEncAlias, ⟨inInnerConstCallEnc, inUsmConstEnc⟩⟩ :=
      inCallElim inInnerFn
    let innerCallEq := callEnc_elim inInnerConstCallEnc
    let usmConstEncEq := inToNamedExprElim inUsmConstEnc
    let argAliasFinalEq: argAlias = arg := argAliasEq.trans argEq.symm
    let fnAliasFinalEq: fnAlias = fn := fnAliasEq.trans fnEq.symm

    let exprEncEq :=
      let nestedEncEq:
        ((uniSetMapDl.cstExpr "uniSetMap").encoding.callEnc fn.toExpr.encoding).callEnc arg.toExpr.encoding
          =
        exprEnc
      := by
        rw [argAliasFinalEq] at argEncEq
        rw [fnAliasFinalEq] at fnEncEq
        rw [←usmConstEncEq] at innerCallEq
        rw [←fnEncEq] at innerCallEq
        rw [←argEncEq] at outerCallEq
        rw [←innerCallEq] at outerCallEq
        exact outerCallEq
      let eqStep0 :=
        congrArg
          (fun enc => enc.callEnc arg.toExpr.encoding)
          (Expr.callEnc_eq
            (uniSetMapDl.cstExpr "uniSetMap")
            fn.toExpr)
      let eqStep1 :=
        (Expr.callEnc_eq
          ((uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr))
          arg.toExpr
      eqStep0.trans (eqStep1.trans nestedEncEq)

    Pair.eq dlEq (Pair.eq fvEq.symm exprEncEq)
  
  theorem indexCall_correct
    (fn arg: Pair)
  :
    uniSetMap.call (fn.indexCall arg) = (uniSetMap.call fn).call arg
  :=
    let fnCallExpr :=
      (uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr
    let fullExpr := fnCallExpr.call arg.toExpr
    let fnCallExprClean: fnCallExpr.IsClean :=
      fun x
        (usesX: ((Expr.const () 1).call fn.toExpr).UsesFreeVar x)
      =>
        usesX.elim
          (fun 
          | Or.inr (Or.inl fnUses) =>
            fn.toExpr_IsClean (x + 1) fnUses)
          nofun
    let eqAt := uniSetMapDl.dl.uniSetMapAt_eq [] fullExpr
    let eqCall :=
      Expr.prod_call_expr_call_eq3
        fnCallExpr
        fnCallExprClean
        arg
        uniSetMapDl.dl.wfm
        uniSetMapDl.dl.wfm
        []
    let eqFn :=
      Expr.prod_call_expr_call_eq3
        (uniSetMapDl.cstExpr "uniSetMap")
        (by decide)
        fn
        uniSetMapDl.dl.wfm
        uniSetMapDl.dl.wfm
        []
    eqAt.trans (eqCall.trans (congrArg (fun s => s.call arg) eqFn))
  
  def indexCall_call {kind}
    (fn arg: Expr kind)
    (tag: kind.ConstTag)
  :
    Expr kind
  :=
    ((const tag (opFixDl.const "indexCall")).call fn).call arg
  
  theorem indexCall_eq_singleton {kind lane fv iFn iArg}
    {fn arg: Expr kind}
    {tag: kind.ConstTag}
    (inFn:
      ∀ pRes,
        let fvFn := .pair iArg pRes :: pRes :: fv
        fn.intp lane opFixDl.dl.wfm opFixDl.dl.wfm fvFn = {iFn})
    (inArg:
      ∀ pRes,
      arg.intp lane opFixDl.dl.wfm opFixDl.dl.wfm (pRes :: fv) = {iArg})
  :
    Eq
      ((indexCall_call fn arg tag).intp lane opFixDl.dl.wfm opFixDl.dl.wfm fv)
      {iFn.indexCall iArg}
  :=
    Set.ext fun p => Iff.intro
      (fun inIndexCall =>
        let inInnerCall := inCallElimSingle inIndexCall (inArg p)
        let inConstIndexCall :=
          inCallElimSingle inInnerCall (inFn p)
        (indexCall_elim (Set3.getLane_toPos inConstIndexCall)).symm)
      (fun pEq =>
        pEq ▸
        inCall
          (inCall
            (indexCall_ins iFn iArg)
            ((inFn (iFn.indexCall iArg)) ▸ rfl))
          ((inArg (iFn.indexCall iArg)) ▸ rfl))
  
  
  theorem magic_ins {iFn iArg lane p}
    (ins:
      p ∈ ((uniSetMap.call iFn).call (iArg.indexCall iArg)).getLane lane)
  :
    p ∈ (((opFixDl.val "magic").call iFn).call iArg).getLane lane
  :=
    let eqUni := uniSetMapDl.extend_wfm_eq opFixDl "uniSetMap"
    let ins:
      ((opFixDl.dl.wfm (uniSetMapDl.const "uniSetMap")).getLane lane).Mem
        (.pair iFn (.pair (iArg.indexCall iArg) p))
    :=
      eqUni.symm ▸ (Set3.inCallElim (Set3.inCallElim ins))
    let insIndexCall:
      _ ∈ (Expr.const .basic 4).intp lane _ _ _
    :=
      indexCall_ins iArg iArg
    let inMagicCall :=
      inCall
        (inCall ins (inVar rfl))
        (inCall
          (inCall
            insIndexCall
            (inVar rfl))
          (inVar rfl))
    Set3.inCall <|
    Set3.inCall <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inArbUn iArg <|
    inProd
      (inVar rfl)
      (inProd (inVar rfl) inMagicCall)
  
  theorem magic_elim {iFn iArg lane p}
    (ins: p ∈ (((opFixDl.val "magic").call iFn).call iArg).getLane lane)
  :
    p ∈ ((uniSetMap.call iFn).call (iArg.indexCall iArg)).getLane lane
  :=
    let ins := Set3.inCallElim (Set3.inCallElim ins)
    let ins := DefList.in_def_body_no_fv ins
    let ⟨fnAlias, ins⟩ := inArbUnElim ins
    let ⟨argAlias, ins⟩ := inArbUnElim ins
    let ⟨inVarFn, ins⟩ := inProdElim ins
    let ⟨inVarArg, ins⟩ := inProdElim ins
    let fnEq := inVarElim inVarFn rfl
    let argEq := inVarElim inVarArg rfl
    
    let indexCallEq := indexCall_eq_singleton (fun _ => rfl) (fun _ => rfl)
    let ins := inCallElimSingle ins indexCallEq
    let ins := inCallElimSingle ins rfl
    let eqUni := uniSetMapDl.extend_wfm_eq opFixDl "uniSetMap"
    let ins:
      Set.Mem
        (Set3.getLane
          (uniSetMapDl.dl.wfm (uniSetMapDl.const "uniSetMap"))
          lane)
        (.pair fnAlias (.pair (argAlias.indexCall argAlias) p))
    :=
       eqUni ▸ ins
    Set3.inCall (Set3.inCall (fnEq ▸ argEq ▸ ins))
  
  theorem magic_call_eq
    (iFn iArg: Pair)
  :
    Eq
      (((opFixDl.val "magic").call iFn).call iArg)
      ((uniSetMap.call iFn).call (iArg.indexCall iArg))
  :=
    Set3.eq4
      (fun _ => magic_elim (lane := .defLane))
      (fun _ => magic_ins (lane := .defLane))
      (fun _ => magic_elim (lane := .posLane))
      (fun _ => magic_ins (lane := .posLane))
  
  exposed def trisetFixIndex (iFn: Pair): Pair :=
    (magicIndex.indexCall iFn).indexCall (magicIndex.indexCall iFn)
  
  theorem trisetFixIndex_eq
    (iFn: Pair)
  :
    Eq
      (uniSetMap.call (trisetFixIndex iFn))
      (((opFixDl.val "magic").call iFn).call (magicIndex.indexCall iFn))
  :=
    let iCall := magicIndex.indexCall iFn
    let eqOuter := indexCall_correct iCall iCall
    let eqInnerCall := indexCall_correct magicIndex iFn
    let eqMagicParent :=
      (opFixHelpersDl.dl.uniSetMapAt_eq
        []
        (.const () (opFixHelpersDl.const "magic")))
    let eqMagicChild := opFixHelpersDl.extend_wfm_eq opFixDl "magic"
    eqOuter ▸
    eqInnerCall ▸
    congrArg
      (fun s => s.call iCall)
      (congrArg (fun s => s.call iFn) (eqMagicParent.trans eqMagicChild))
  
  
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
      eqUni.symm ▸ (Set3.inCallElim (Set3.inCallElim inQ))
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
    Set3.inCall <|
    Set3.inCall <|
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
    let ins := Set3.inCallElim (Set3.inCallElim ins)
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
      opEq ▸ argEq ▸ opAlias2Eq ▸ argAlias2Eq ▸
        Set3.inCall (Set3.inCall inUsmConst)
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
  
  
  theorem trisetFix_ins {iFn lane p}
    (ins:
      Set.Mem
        (Set3.getLane
          (((opFixDl.val "magic").call iFn).call (magicIndex.indexCall iFn))
          lane)
        p)
  :
    p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane
  :=
    let indexCallEq :=
      indexCall_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton magicIndex)
        (fun _ => intp_var_eq_singleton rfl)
    Set3.inCall <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inProd
      (inVar rfl)
      (inCall
        (inCall
          (Set3.inCallElim (Set3.inCallElim ins))
          rfl)
        (indexCallEq ▸ rfl))

  theorem trisetFix_elim {iFn lane p}
    (ins: p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane)
  :
    Set.Mem
      (Set3.getLane
        (((opFixDl.val "magic").call iFn).call (magicIndex.indexCall iFn))
        lane)
      p
  :=
    let ins := Set3.inCallElim ins
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    let ⟨_unused, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    let indexCallEq :=
      indexCall_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton magicIndex)
        (fun _ => intp_var_eq_singleton rfl)
    let ins := inCallElimSingle ins indexCallEq
    let ins := inCallElimSingle ins (intp_var_eq_singleton rfl)
    Set3.inCall (Set3.inCall (iEq ▸ ins))

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
    The `indexFix` symbol of `opFixDl` is defined as
    `Ex iOp, (iOp, trisetFix (indexCall [composeOpIndex.toExpr] iOp))`,
    so calling it with `iOp` semantically reduces to evaluating
    `trisetFix` at the composed-op index `composeIndex iOp`.
  -/
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
    let indexCallEq :=
      indexCall_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton composeOpIndex)
        (fun _ => intp_var_eq_singleton rfl)
    Set3.inCall <|
    DefList.in_def_no_fv <|
    inArbUn iOp <|
    inProd
      (inVar rfl)
      (inCall
        (Set3.inCallElim ins)
        (indexCallEq ▸ rfl))
  
  theorem indexFix_elim {iOp lane p}
    (ins: p ∈ ((opFixDl.val "indexFix").call iOp).getLane lane)
  :
    p ∈ ((opFixDl.val "trisetFix").call (composeIndex iOp)).getLane lane
  :=
    let ins := Set3.inCallElim ins
    let ins := DefList.in_def_body_no_fv (lane := lane) ins
    let ⟨_unused, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    let indexCallEq :=
      indexCall_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton composeOpIndex)
        (fun _ => intp_var_eq_singleton rfl)
    let ins := inCallElimSingle ins indexCallEq
    Set3.inCall (iEq ▸ ins)
  
  theorem indexFix_call_eq
    (iOp: Pair)
  :
    Eq
      ((opFixDl.val "indexFix").call iOp)
      ((opFixDl.val "trisetFix").call (composeIndex iOp))
  :=
    Set3.eq4
      (fun _ => indexFix_elim (lane := .defLane))
      (fun _ => indexFix_ins (lane := .defLane))
      (fun _ => indexFix_elim (lane := .posLane))
      (fun _ => indexFix_ins (lane := .posLane))
  
end opFixDl
