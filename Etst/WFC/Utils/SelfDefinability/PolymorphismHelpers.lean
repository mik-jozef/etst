-- TODO rewrite this file with the extra encoding cases to reduce
-- the huge size of opFixDl
module
-- The `meta` import is required because
-- `pairDefList opFixHelpersDl extends uniSetMapDl` below evaluates
-- `uniSetMapDl.constNames` at elaboration time. See the docstring
-- of `pair_def_list` in `FiniteDefList.lean`.
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
public import Etst.WFC.Utils.RulesOfInference
public import Etst.WFC.Utils.NamedDefList.NamedPairExpr
import Etst.WFC.Ch6_SelfDefinability
import Etst.WFC.Utils.Expr.FreeVars

public section
namespace Etst


namespace Pair
  -- Represents the encoding of `Expr.call`, see `encodeCall_eq` below.
  -- The arguments are assumed to be already encoded.
  exposed def encodeCall
    (fn arg: Pair)
  :
    Pair
  :=
    let enc n p := pair (.nat n) p
    let bin n l r := pair (.nat n) (.pair l r)
    let var0 := enc 2 (.nat 0)
    enc 11 (bin 6 (enc 9 (bin 6 fn (bin 5 arg var0))) var0)
  
  -- Returns an index representing `uniSetMap fn arg`.
  exposed def callEnc
    (fn arg: Pair)
  :
    Pair
  :=
    uniSetMapIndex
      uniSetMapDl.dl.toDefList
      uniSetMapDl.dl.size
      []
      (((uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr).call arg.toExpr)
  
  theorem toExpr_IsClean: (p: Pair) → p.toExpr.IsClean
  | .null => fun _ => id
  | .pair left rite =>
    fun x usesX =>
      usesX.elim (toExpr_IsClean left x) (toExpr_IsClean rite x)
  
end Pair

theorem Expr.encodeCall_eq
  (fn arg: BasicExpr)
:
  Eq
    (fn.encoding.encodeCall arg.encoding)
    (BasicExpr.encoding (fn.call arg))
:=
  rfl

theorem BasicExpr.prod_call_expr_call_eq
  (fn: BasicExpr)
  (fnIsClean: fn.IsClean)
  (arg: Pair)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  Eq
    (BasicExpr.triIntp (fn.call arg.toExpr) b c fv)
    ((fn.triIntp b c fv).call arg)
:=
  open SingleLaneExpr in
  Set3.eq4
    (fun _ inCall =>
      show _ ∈ (fn.toLane .defLane).intp b c fv from
      (fnIsClean.toLane .defLane).intp_eq ▸
      inCallElimSingle inCall (intp_toExpr_eq_singleton arg))
    (fun _ inFn =>
      let inFnShifted := (fnIsClean.toLane .defLane).intp_eq ▸ inFn
      inCall inFnShifted (inToExpr arg))
    (fun _ inCall =>
      show _ ∈ (fn.toLane .posLane).intp b c fv from
      (fnIsClean.toLane .posLane).intp_eq ▸
      inCallElimSingle inCall (intp_toExpr_eq_singleton arg))
    (fun _ inFn =>
      let inFnShifted: _ ∈ (fn.toLane .posLane).intp _ _ _ :=
        (fnIsClean.toLane .posLane).intp_eq ▸ inFn
      inCall inFnShifted (inToExpr arg))


exposed def uniSetMapDlEncoding :=
  uniSetMapDl.dl.prefixEncoding uniSetMapDl.dl.size

open uniSetMapDl in
exposed pairDefList opFixHelpersDl extends uniSetMapDl
  -- Converts a pair to an encoding of an expression that evaluates to it.
  p3 encodeAsExpr :=
  | null × 4 × null
  | (Ex l r, (l × r) × 5 × encodeAsExpr l × encodeAsExpr r)
  
  p3 encodeCall :=
    Ex aEnc bEnc,
      × aEnc × bEnc
      × 11 × 6 × (9 × 6 × aEnc × 5 × bEnc × 2 × 0) × 2 × 0
  
  p3 callEnc :=
    Ex fn arg,
      × fn × arg
      × <[uniSetMapDlEncoding.toNamedExpr]>
      × null
      × encodeCall
          (encodeCall
            <[((cstExpr "uniSetMap").encoding.toNamedExpr)]>
            (encodeAsExpr fn))
          (encodeAsExpr arg)
  
  -- Named χ on the wiki's article on the Diagonal lemma:
  p3 magic :=
    Ex iFn iArg, iFn × iArg × uniSetMap iFn (callEnc iArg iArg)
  
  p3 composeOp :=
    Ex iOp iArg, iOp × iArg × uniSetMap (uniSetMap iOp iArg)
pairDefList.

-- An index representing `opFixHelpersDl.magic`.
exposed def opFixDl.magicIndex: Pair :=
  (uniSetMapIndex
    opFixHelpersDl.dl.toDefList
    opFixHelpersDl.dl.size
    []
    (.const (opFixHelpersDl.const "magic")))

exposed def composeOpIndex: Pair :=
  uniSetMapIndex
    opFixHelpersDl.dl.toDefList
    opFixHelpersDl.dl.size
    []
    (.const (opFixHelpersDl.const "composeOp"))

exposed def composeIndex (iOp: Pair): Pair :=
  composeOpIndex.callEnc iOp

exposed pairDefList opFixDl extends opFixHelpersDl
  p3 trisetFix :=
    Ex iOp,
      × iOp
      × magic iOp (callEnc <[opFixDl.magicIndex.toNamedExpr]> iOp)
  
  p3 indexFix :=
    Ex iOp,
      × iOp
      × trisetFix (callEnc <[composeOpIndex.toNamedExpr]> iOp)
pairDefList.


namespace opFixDl
  open SingleLaneExpr
  
  theorem encodeAsExpr_ins (p: Pair):
    opFixDl.dl.InWfm []
      (.const .defLane (opFixDl.const "encodeAsExpr"))
      (.pair p p.toExpr.encoding)
  :=
    DefList.InWfm.of_in_def_no_fv
    (match p with
    | .null => inUnL (inProd inNull (inProd (inNat 4) inNull))
    | .pair l r =>
      let ihL := inCall (encodeAsExpr_ins l) (inVar rfl)
      let ihR := inCall (encodeAsExpr_ins r) (inVar rfl)
      let inRet := inProd (inNat 5) (inProd ihL ihR)
      inUnR (inArbUn l (inArbUn r (inProd (inProd rfl rfl) inRet))))
  
  theorem encodeAsExpr_elim {p enc}
    (ins:
      opFixDl.dl.InWfm []
        (.const .posLane (opFixDl.const "encodeAsExpr"))
        (.pair p enc)
    )
  :
    p.toExpr.encoding = enc
  :=
    match p with
    | .null =>
      let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
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
      let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
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
  
  
  theorem encodeCall_ins
    (fn arg: Pair)
  :
    opFixDl.dl.InWfm []
      (.const .defLane (opFixDl.const "encodeCall"))
      (.pair fn (.pair arg (fn.encodeCall arg)))
  :=
    let inVar0 := inProd (inNat 2) (inNat 0)
    let inBin5 := inProd (inNat 5) (inProd (inVar rfl) inVar0)
    let inBin6 := inProd (inNat 6) (inProd (inVar rfl) inBin5)
    let inEnc9 := inProd (inNat 9) inBin6
    let inEncBody := inProd (inNat 6) (inProd inEnc9 inVar0)
    let inEnc11 := inProd (inNat 11) inEncBody
    let inBody := inProd (inVar rfl) (inProd (inVar rfl) inEnc11)
    DefList.InWfm.of_in_def_no_fv (inArbUn fn (inArbUn arg inBody))
  
  theorem encodeCall_elim {fn arg enc}
    (ins:
      opFixDl.dl.InWfm []
        (.const .posLane (opFixDl.const "encodeCall"))
        (.pair fn (.pair arg enc))
    )
  :
    fn.encodeCall arg = enc
  :=
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
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
      fnWit.encodeCall argWit
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
  
  
  theorem callEnc_ins
    (fn arg: Pair)
  :
      opFixDl.dl.InWfm []
      (.const .defLane (opFixDl.const "callEnc"))
      (.pair fn (.pair arg (fn.callEnc arg)))
  :=
    let inUsmConstEnc :=
      inToExpr (uniSetMapDl.cstExpr "uniSetMap").encoding
    let inFnEnc := inCall (encodeAsExpr_ins fn) (inVar rfl)
    let inArgEnc := inCall (encodeAsExpr_ins arg) (inVar rfl)
    let inInnerCall :=
      inCall
        (inCall
          (encodeCall_ins
            (uniSetMapDl.cstExpr "uniSetMap").encoding
            fn.toExpr.encoding)
          inUsmConstEnc)
        inFnEnc
    let inExprEnc :=
      inCall
        (inCall
          (encodeCall_ins
            ((uniSetMapDl.cstExpr "uniSetMap").encoding.encodeCall
              fn.toExpr.encoding)
            arg.toExpr.encoding)
          inInnerCall)
        inArgEnc
    DefList.InWfm.of_in_def_no_fv
    (inArbUn fn
    (inArbUn arg
    (inProd (inVar rfl)
    (inProd (inVar rfl)
    (inProd (inToNamedExpr uniSetMapDlEncoding)
    (inProd inNull inExprEnc))))))
  
  theorem callEnc_elim {fn arg enc}
    (ins: .pair fn (.pair arg enc) ∈ (opFixDl.val "callEnc").posMem)
  :
    fn.callEnc arg = enc
  :=
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
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

    let ⟨fnCallEncAlias, ⟨inOuterConstEncodeCall, inFnExpr⟩⟩ :=
      inCallElim inOuterFn
    let outerCallEq := encodeCall_elim inOuterConstEncodeCall

    let ⟨fnEncAlias, ⟨inInnerFn, inFnEncExpr⟩⟩ := inCallElim inFnExpr
    let ⟨fnAlias, ⟨inConstEncodeAsExprFn, inFnVar⟩⟩ :=
      inCallElim inFnEncExpr
    let fnAliasEq := inVarElim inFnVar rfl
    let fnEncEq := encodeAsExpr_elim inConstEncodeAsExprFn

    let ⟨usmConstEncAlias, ⟨inInnerConstEncodeCall, inUsmConstEnc⟩⟩ :=
      inCallElim inInnerFn
    let innerCallEq := encodeCall_elim inInnerConstEncodeCall
    let usmConstEncEq := inToNamedExprElim inUsmConstEnc
    let argAliasFinalEq: argAlias = arg := argAliasEq.trans argEq.symm
    let fnAliasFinalEq: fnAlias = fn := fnAliasEq.trans fnEq.symm

    let exprEncEq :=
      let nestedEncEq:
        ((uniSetMapDl.cstExpr "uniSetMap").encoding.encodeCall fn.toExpr.encoding).encodeCall arg.toExpr.encoding
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
          (fun enc => enc.encodeCall arg.toExpr.encoding)
          (Expr.encodeCall_eq
            (uniSetMapDl.cstExpr "uniSetMap")
            fn.toExpr)
      let eqStep1 :=
        (Expr.encodeCall_eq
          ((uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr))
          arg.toExpr
      eqStep0.trans (eqStep1.trans nestedEncEq)

    Pair.eq dlEq (Pair.eq fvEq.symm exprEncEq)
  
  theorem callEnc_correct
    (fn arg: Pair)
  :
    uniSetMap.call (fn.callEnc arg) = (uniSetMap.call fn).call arg
  :=
    let fnCallExpr :=
      (uniSetMapDl.cstExpr "uniSetMap").call fn.toExpr
    let fullExpr := fnCallExpr.call arg.toExpr
    let fnCallExprClean: fnCallExpr.IsClean :=
      fun x
        (usesX: ((BasicExpr.const 1).call fn.toExpr).UsesFreeVar x)
      =>
        usesX.elim
          (fun 
          | Or.inr (Or.inl fnUses) =>
            fn.toExpr_IsClean (x + 1) fnUses)
          nofun
    let eqAt := uniSetMapDl.dl.uniSetMapAt_eq [] fullExpr
    let eqCall :=
      BasicExpr.prod_call_expr_call_eq
        fnCallExpr
        fnCallExprClean
        arg
        []
        uniSetMapDl.dl.wfm
        uniSetMapDl.dl.wfm
    let eqFn :=
      BasicExpr.prod_call_expr_call_eq
        (uniSetMapDl.cstExpr "uniSetMap")
        (by decide)
        fn
        []
        uniSetMapDl.dl.wfm
        uniSetMapDl.dl.wfm
    eqAt.trans (eqCall.trans (congrArg (fun s => s.call arg) eqFn))
  
  def callEnc_call
    (fn arg: SingleLaneExpr)
    (lane: Set3.Lane)
  :
    SingleLaneExpr
  :=
    ((const lane (opFixDl.const "callEnc")).call fn).call arg
  
  theorem callEnc_eq_singleton {fv iFn iArg lane}
    {fn arg: SingleLaneExpr}
    (inFn:
      ∀ pRes,
        let fvFn := .pair iArg pRes :: pRes :: fv
        fn.intp fvFn opFixDl.dl.wfm opFixDl.dl.wfm = {iFn})
    (inArg:
      ∀ pRes,
      arg.intp (pRes :: fv) opFixDl.dl.wfm opFixDl.dl.wfm = {iArg})
  :
    Eq
      ((callEnc_call fn arg lane).intp fv opFixDl.dl.wfm opFixDl.dl.wfm)
      {iFn.callEnc iArg}
  :=
    Set.ext fun p => Iff.intro
      (fun inCallEnc =>
        let inInnerCall := inCallElimSingle inCallEnc (inArg p)
        let inConstCallEnc :=
          inCallElimSingle inInnerCall (inFn p)
        (callEnc_elim (Set3.getLane_toPos inConstCallEnc)).symm)
      (fun pEq =>
        pEq ▸
        inCall
          (inCall
            (Set3.defMem_getLane (callEnc_ins iFn iArg))
            ((inFn (iFn.callEnc iArg)) ▸ rfl))
          ((inArg (iFn.callEnc iArg)) ▸ rfl))
  
  
  theorem magic_ins {iFn iArg lane p}
    (ins:
      p ∈ ((uniSetMap.call iFn).call (iArg.callEnc iArg)).getLane lane)
  :
    p ∈ (((opFixDl.val "magic").call iFn).call iArg).getLane lane
  :=
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt _ (by decide)
    let eqH :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
    let eqUni := eqU.trans eqH
    let ins:
      ((opFixDl.dl.wfm (uniSetMapDl.const "uniSetMap")).getLane lane).Mem
        (.pair iFn (.pair (iArg.callEnc iArg) p))
    :=
      eqUni.symm ▸ (Set3.inCallElim (Set3.inCallElim ins))
    let insCallEnc:
      _ ∈ ((BasicExpr.const 4).toLane lane).intp _ _ _
    :=
      Set3.defMem_getLane (callEnc_ins iArg iArg)
    let inMagicCall :=
      inCall
        (inCall (inToggle2 4 ins) (inVar rfl))
        (inCall
          (inCall
            (inToggle2 6 insCallEnc)
            (inVar rfl))
          (inVar rfl))
    Set3.inCall <|
    Set3.inCall <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inArbUn iArg <|
    inProd
      (inVar rfl)
      (inProd (inVar rfl) (inToggle2 2 inMagicCall))
  
  theorem magic_elim {iFn iArg lane p}
    (ins: p ∈ (((opFixDl.val "magic").call iFn).call iArg).getLane lane)
  :
    p ∈ ((uniSetMap.call iFn).call (iArg.callEnc iArg)).getLane lane
  :=
    let ins := Set3.inCallElim (Set3.inCallElim ins)
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨fnAlias, ins⟩ := inArbUnElim ins
    let ⟨argAlias, ins⟩ := inArbUnElim ins
    let ⟨inVarFn, ins⟩ := inProdElim ins
    let ⟨inVarArg, ins⟩ := inProdElim ins
    let fnEq := inVarElim inVarFn rfl
    let argEq := inVarElim inVarArg rfl
    
    let callEncEq := callEnc_eq_singleton (fun _ => rfl) (fun _ => rfl)
    let ins := inCallElimSingle ins callEncEq
    let ins := inCallElimSingle ins rfl
    let ins := inToggle2Elim 6 ins
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt _ (by decide)
    let eqH :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
    let eqUni := eqU.trans eqH
    let ins:
      Set.Mem
        (Set3.getLane
          (uniSetMapDl.dl.wfm (uniSetMapDl.const "uniSetMap"))
          lane)
        (.pair fnAlias (.pair (argAlias.callEnc argAlias) p))
    :=
       eqUni ▸ ins
    Set3.inCall (Set3.inCall (fnEq ▸ argEq ▸ ins))
  
  theorem magic_call_eq
    (iFn iArg: Pair)
  :
    Eq
      (((opFixDl.val "magic").call iFn).call iArg)
      ((uniSetMap.call iFn).call (iArg.callEnc iArg))
  :=
    Set3.eq4
      (fun _ => magic_elim (lane := .defLane))
      (fun _ => magic_ins (lane := .defLane))
      (fun _ => magic_elim (lane := .posLane))
      (fun _ => magic_ins (lane := .posLane))
  
  exposed def trisetFixIndex (iFn: Pair): Pair :=
    (magicIndex.callEnc iFn).callEnc (magicIndex.callEnc iFn)
  
  theorem trisetFixIndex_eq
    (iFn: Pair)
  :
    Eq
      (uniSetMap.call (trisetFixIndex iFn))
      (((opFixDl.val "magic").call iFn).call (magicIndex.callEnc iFn))
  :=
    let iCall := magicIndex.callEnc iFn
    let eqOuter := callEnc_correct iCall iCall
    let eqInnerCall := callEnc_correct magicIndex iFn
    let eqMagicParent :=
      (opFixHelpersDl.dl.uniSetMapAt_eq
        []
        (.const (opFixHelpersDl.const "magic")))
    let eqMagicChild :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
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
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt _ (by decide)
    let eqH :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
    let eqUni := eqU.trans eqH
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
        (inToggle2 2 insOuter)
        (inCall
          (inCall
            (inToggle2 6 insInner)
            (inVar rfl))
          (inVar rfl))
    Set3.inCall <|
    Set3.inCall <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iOp <|
    inArbUn iArg <|
    inProd
      (inVar rfl)
      (inProd (inVar rfl) (inToggle2 2 inComposeCall))
  
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
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨opAlias, ins⟩ := inArbUnElim ins
    let ⟨argAlias, ins⟩ := inArbUnElim ins
    let ⟨inVarOp, ins⟩ := inProdElim ins
    let ⟨inVarArg, ins⟩ := inProdElim ins
    let opEq := inVarElim inVarOp rfl
    let argEq := inVarElim inVarArg rfl
    let ins := inToggle2Elim 2 ins
    let ⟨qAlias, ⟨inOuterFn, inInnerCall⟩⟩ := inCallElim ins
    let ⟨argAlias2, ⟨inMidFn, inArgVar⟩⟩ := inCallElim inInnerCall
    let argAlias2Eq := inVarElim inArgVar rfl
    let ⟨opAlias2, ⟨inUsmConst, inOpVar⟩⟩ := inCallElim inMidFn
    let opAlias2Eq := inVarElim inOpVar rfl
    let inUsmConst := inToggle2Elim 6 inUsmConst
    let inOuterFn := inToggle2Elim 2 inOuterFn
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt _ (by decide)
    let eqH :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
    let eqUni := eqU.trans eqH
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
    let eqCall := callEnc_correct composeOpIndex iOp
    let eqComposeOpParent :=
      opFixHelpersDl.dl.uniSetMapAt_eq
        []
        (.const (opFixDl.const "composeOp"))
    let eqComposeOpChild :=
      opFixHelpersDl.extend_wfm_eq_of_lt _ (by decide)
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
          (((opFixDl.val "magic").call iFn).call (magicIndex.callEnc iFn))
          lane)
        p)
  :
    p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane
  :=
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton magicIndex)
        (fun _ => intp_var_eq_singleton rfl)
    Set3.inCall <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inProd
      (inVar rfl)
      (inCall
        (inCall
          (inToggle2 5 (Set3.inCallElim (Set3.inCallElim ins)))
          rfl)
        (callEncEq ▸ rfl))

  theorem trisetFix_elim {iFn lane p}
    (ins: p ∈ ((opFixDl.val "trisetFix").call iFn).getLane lane)
  :
    Set.Mem
      (Set3.getLane
        (((opFixDl.val "magic").call iFn).call (magicIndex.callEnc iFn))
        lane)
      p
  :=
    let ins := Set3.inCallElim ins
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨_unused, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    let ins := inToggle2Elim' 1 ins rfl
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton magicIndex)
        (fun _ => intp_var_eq_singleton rfl)
    let ins := inCallElimSingle ins callEncEq
    let ins := inCallElimSingle ins (intp_var_eq_singleton rfl)
    Set3.inCall (Set3.inCall (iEq ▸ (inToggle2Elim 4 ins)))

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
    `Ex iOp, (iOp, trisetFix (callEnc [composeOpIndex.toExpr] iOp))`,
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
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton composeOpIndex)
        (fun _ => intp_var_eq_singleton rfl)
    Set3.inCall <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iOp <|
    inProd
      (inVar rfl)
      (inCall
        (inToggle2 3 (Set3.inCallElim ins))
        (callEncEq ▸ rfl))
  
  theorem indexFix_elim {iOp lane p}
    (ins: p ∈ ((opFixDl.val "indexFix").call iOp).getLane lane)
  :
    p ∈ ((opFixDl.val "trisetFix").call (composeIndex iOp)).getLane lane
  :=
    let ins := Set3.inCallElim ins
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨_unused, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inProdElim ins
    let iEq := inVarElim inVarI rfl
    let ins := inToggle2Elim' 1 ins rfl
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp_toNamedExpr_eq_singleton composeOpIndex)
        (fun _ => intp_var_eq_singleton rfl)
    let ins := inCallElimSingle ins callEncEq
    Set3.inCall (iEq ▸ inToggle2Elim 2 ins)
  
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
