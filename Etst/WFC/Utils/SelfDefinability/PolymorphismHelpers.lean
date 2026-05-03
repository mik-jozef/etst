import Etst.WFC.Ch6_SelfDefinability
import Etst.WFC.Utils.Expr.FreeVars

namespace Etst


namespace Pair
  -- Represents the encoding of `Expr.call`, see `encodeCall_eq` below.
  -- The arguments are assumed to be already encoded.
  def encodeCall
    (fn arg: Pair)
  :
    Pair
  :=
    let enc n p := pair (.nat n) p
    let bin n l r := pair (.nat n) (.pair l r)
    let var0 := enc 2 (.nat 0)
    enc 11 (bin 6 (enc 9 (bin 6 fn (bin 5 arg var0))) var0)
  
  -- Returns an index representing `uniSetMap fn arg`.
  def callEnc
    (fn arg: Pair)
  :
    Pair
  :=
    uniSetMapIndex
      uniSetMapDl.toDefList
      (uniSetMapDl.consts.uniSetMap + 1)
      []
      ((uniSetMapDl.uniSetMapConst.call fn.toExpr).call arg.toExpr)
  
  def toExpr_IsClean: (p: Pair) → p.toExpr.IsClean
  | .null => fun _ => id
  | .pair left rite =>
    fun x usesX =>
      usesX.elim (toExpr_IsClean left x) (toExpr_IsClean rite x)
  
end Pair

def Expr.encodeCall_eq
  (fn arg: BasicExpr)
:
  Eq
    (fn.encoding.encodeCall arg.encoding)
    (BasicExpr.encoding (fn.call arg))
:=
  rfl

def BasicExpr.pair_call_expr_call_eq
  (fn: BasicExpr)
  (fnIsClean: fn.IsClean)
  (arg: Pair)
  (fv: List Pair)
  (b c: Valuation Pair)
:
  Eq
    (BasicExpr.triIntp2 (fn.call arg.toExpr) fv b c)
    ((fn.triIntp2 fv b c).call arg)
:=
  open SingleLaneExpr in
  Set3.eq4
    (fun _ inCall =>
      show (fn.toLane .defLane).intp2 fv b c _ from
      (fnIsClean.toLane .defLane).intp2_eq ▸
      inCallElimSingle inCall (intp2_toExpr_eq_singleton arg))
    (fun _ inFn =>
      let inFnShifted := (fnIsClean.toLane .defLane).intp2_eq ▸ inFn
      inCall inFnShifted (inToExpr arg))
    (fun _ inCall =>
      show (fn.toLane .posLane).intp2 fv b c _ from
      (fnIsClean.toLane .posLane).intp2_eq ▸
      inCallElimSingle inCall (intp2_toExpr_eq_singleton arg))
    (fun _ inFn =>
      let inFnShifted: (fn.toLane .posLane).intp2 _ _ _ _ :=
        (fnIsClean.toLane .posLane).intp2_eq ▸ inFn
      inCall inFnShifted (inToExpr arg))


def uniSetMapDlEncoding :=
  uniSetMapDl.prefixEncoding (uniSetMapDl.consts.uniSetMap + 1)

open uniSetMapDl in
pairDefList callFixHelpersDl extends uniSetMapDl
  -- Converts a pair to an encoding of an expression that evaluates to it.
  s3 encodeAsExpr :=
  | (null, (4, null))
  | (Ex l r, ((l, r), (5, (encodeAsExpr l, encodeAsExpr r))))
  
  s3 encodeCall :=
    Ex aEnc bEnc, (
      aEnc, (bEnc,
      (11, (6, ((9, (6, (aEnc, (5, (bEnc, (2, 0)))))), (2, 0))))
    ))
  
  s3 callEnc :=
    Ex fn arg, (
      fn, (arg,
      (
        [uniSetMapDlEncoding.toExpr],
        (
          null,
          encodeCall
            (encodeCall
              [((BasicExpr.const consts.uniSetMap).encoding.toExpr)]
              (encodeAsExpr fn))
            (encodeAsExpr arg)
        )
      )
    ))
  
  -- Named χ on the wiki's article on the Diagonal lemma:
  s3 magic :=
    Ex iFn iArg, (iFn, (iArg, uniSetMap iFn (callEnc iArg iArg)))
pairDefList.

-- An index representing `callFixHelpersDl.magic`.
def callFixDl.magicIndex: Pair :=
  (uniSetMapIndex
    callFixHelpersDl.toDefList
    (callFixHelpersDl.consts.magic + 1)
    []
    (.const callFixHelpersDl.consts.magic))

pairDefList callFixDl extends callFixHelpersDl
  s3 callFix :=
    Ex i, (
      i,
      magic i (callEnc [callFixDl.magicIndex.toExpr] i)
    )
pairDefList.


namespace callFixDl
  open callFixHelpersDl
  open SingleLaneExpr
  
  def encodeAsExpr_ins (p: Pair):
    callFixDl.InWfm []
      (.const .defLane consts.encodeAsExpr)
      (.pair p p.toExpr.encoding)
  :=
    DefList.InWfm.of_in_def_no_fv
    (match p with
    | .null => inUnL (inPair inNull (inPair (inNat 4) inNull))
    | .pair l r =>
      let ihL := inCall (encodeAsExpr_ins l) (inVar rfl)
      let ihR := inCall (encodeAsExpr_ins r) (inVar rfl)
      let inRet := inPair (inNat 5) (inPair ihL ihR)
      inUnR (inArbUn l (inArbUn r (inPair (inPair rfl rfl) inRet))))
  
  def encodeAsExpr_elim {p enc}
    (ins:
      callFixDl.InWfm []
        (.const .posLane consts.encodeAsExpr)
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
          let ⟨_, inEnc⟩ := inPairElim ins
          match enc with
          | .pair _ _ =>
          let ⟨inTag, inNullEnc⟩ := inPairElim inEnc
          let tagEq := inNatElim (n := 4) inTag
          let argEq := inNullElim inNullEnc
          tagEq ▸ argEq.symm ▸ rfl)
        (fun ins =>
          let ⟨_, ins⟩ := inArbUnElim ins
          let ⟨_, ins⟩ := inArbUnElim ins
          let ⟨inPairP, _⟩ := inPairElim ins
          inPairElimNope inPairP)
    | .pair l r =>
      let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
      (inUnElim ins).elim
        (fun ins =>
          let ⟨inPairP, _⟩ := inPairElim ins
          inNullElimNope inPairP)
        (fun ins =>
          let ⟨lWit, ins⟩ := inArbUnElim ins
          let ⟨rWit, ins⟩ := inArbUnElim ins
          let ⟨inPairP, inEnc⟩ := inPairElim ins
          let ⟨_, _, pEq, inLeft, inRite⟩ := inPairElimEx inPairP
          let ⟨lEq, rEq⟩ := Pair.noConfusion pEq And.intro
          match enc with
          | .pair _ (.pair _ _) =>
          let ⟨inTag, inArg⟩ := inPairElim inEnc
          let tagEq := inNatElim (n := 5) inTag
          let ⟨inLeftEnc, inRiteEnc⟩ := inPairElim inArg
          let pLEq := inVarElim inLeft rfl
          let pREq := inVarElim inRite rfl
          let insLeft := inCallElimSingle inLeftEnc rfl
          let insRite := inCallElimSingle inRiteEnc rfl
          let ihL := encodeAsExpr_elim insLeft
          let ihR := encodeAsExpr_elim insRite
          let lWitEq: lWit = l := pLEq.symm.trans lEq.symm
          let rWitEq: rWit = r := pREq.symm.trans rEq.symm
          lWitEq ▸ rWitEq ▸ tagEq ▸ ihL ▸ ihR ▸ rfl)
  
  
  def encodeCall_ins
    (fn arg: Pair)
  :
    callFixDl.InWfm []
      (.const .defLane consts.encodeCall)
      (.pair fn (.pair arg (fn.encodeCall arg)))
  :=
    let inVar0 := inPair (inNat 2) (inNat 0)
    let inBin5 := inPair (inNat 5) (inPair (inVar rfl) inVar0)
    let inBin6 := inPair (inNat 6) (inPair (inVar rfl) inBin5)
    let inEnc9 := inPair (inNat 9) inBin6
    let inEncBody := inPair (inNat 6) (inPair inEnc9 inVar0)
    let inEnc11 := inPair (inNat 11) inEncBody
    let inBody := inPair (inVar rfl) (inPair (inVar rfl) inEnc11)
    DefList.InWfm.of_in_def_no_fv (inArbUn fn (inArbUn arg inBody))
  
  def encodeCall_elim {fn arg enc}
    (ins:
      callFixDl.InWfm []
        (.const .posLane consts.encodeCall)
        (.pair fn (.pair arg enc))
    )
  :
    fn.encodeCall arg = enc
  :=
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
    let ⟨fnWit, ins⟩ := inArbUnElim ins
    let ⟨argWit, ins⟩ := inArbUnElim ins
    let ⟨inFn, ins⟩ := inPairElim ins
    let fnEq := inVarElim inFn rfl
    let ⟨inArg, inEnc⟩ := inPairElim ins
    let argEq := inVarElim inArg rfl
    match enc with
    | .pair tag11 encBody =>
    let ⟨inTag11, inEncBody⟩ := inPairElim inEnc
    let tag11Eq := inNatElim (n := 11) inTag11
    match encBody with
    | .pair tag6 encArgs =>
    let ⟨inTag6, inEncArgs⟩ := inPairElim inEncBody
    let tag6Eq := inNatElim (n := 6) inTag6
    match encArgs with
    | .pair enc9 var0R =>
    let ⟨inEnc9, inVar0R⟩ := inPairElim inEncArgs
    match enc9 with
    | .pair tag9 bin6 =>
    let ⟨inTag9, inBin6⟩ := inPairElim inEnc9
    let tag9Eq := inNatElim (n := 9) inTag9
    match bin6 with
    | .pair tag6L bin5Wrap =>
    let ⟨inTag6L, inBin5Wrap⟩ := inPairElim inBin6
    let tag6LEq := inNatElim (n := 6) inTag6L
    match bin5Wrap with
    | .pair fnVar bin5 =>
    let ⟨inFnVar, inBin5⟩ := inPairElim inBin5Wrap
    let fnWitEq := inVarElim inFnVar rfl
    match bin5 with
    | .pair tag5 bin5Args =>
    let ⟨inTag5, inBin5Args⟩ := inPairElim inBin5
    let tag5Eq := inNatElim (n := 5) inTag5
    match bin5Args with
    | .pair argVar var0L =>
    let ⟨inArgVar, inVar0L⟩ := inPairElim inBin5Args
    let argWitEq := inVarElim inArgVar rfl
    match var0L, var0R with
    | .pair tag2L tag0L, .pair tag2R tag0R =>
    let ⟨inTag2L, inTag0L⟩ := inPairElim inVar0L
    let tag2LEq := inNatElim (n := 2) inTag2L
    let tag0LEq := inNatElim (n := 0) inTag0L
    let ⟨inTag2R, inTag0R⟩ := inPairElim inVar0R
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
  
  
  def callEnc_ins
    (fn arg: Pair)
  :
    callFixDl.InWfm []
      (.const .defLane consts.callEnc)
      (.pair fn (.pair arg (fn.callEnc arg)))
  :=
    let inUsmConstEnc :=
      inToExpr uniSetMapDl.uniSetMapConst.encoding
    let inFnEnc := inCall (encodeAsExpr_ins fn) (inVar rfl)
    let inArgEnc := inCall (encodeAsExpr_ins arg) (inVar rfl)
    let inInnerCall :=
      inCall
        (inCall
          (encodeCall_ins
            uniSetMapDl.uniSetMapConst.encoding
            fn.toExpr.encoding)
          inUsmConstEnc)
        inFnEnc
    let inExprEnc :=
      inCall
        (inCall
          (encodeCall_ins
            (uniSetMapDl.uniSetMapConst.encoding.encodeCall
              fn.toExpr.encoding)
            arg.toExpr.encoding)
          inInnerCall)
        inArgEnc
    let inResult :=
      inPair
        (inToExpr uniSetMapDlEncoding)
        (inPair inNull inExprEnc)
    let inCallEnc := inPair (inVar rfl) (inPair (inVar rfl) inResult)
    DefList.InWfm.of_in_def_no_fv (inArbUn fn (inArbUn arg inCallEnc))
  
  def callEnc_elim {fn arg enc}
    (ins: (vals.callEnc.posMem (.pair fn (.pair arg enc))))
  :
    fn.callEnc arg = enc
  :=
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
    let ⟨fnWit, ins⟩ := inArbUnElim ins
    let ⟨argWit, ins⟩ := inArbUnElim ins
    let ⟨inFn, ins⟩ := inPairElim ins
    let fnEq := inVarElim inFn rfl
    let ⟨inArg, inEnc⟩ := inPairElim ins
    let argEq := inVarElim inArg rfl
    match enc with
    | .pair dlEnc encTail =>
    let ⟨inDlEnc, inEncTail⟩ := inPairElim inEnc
    let dlEq := inToExprElim inDlEnc
    match encTail with
    | .null => inPairElimNope inEncTail
    | .pair fvEnc exprEnc =>
    let ⟨inFvEnc, inExprEnc⟩ := inPairElim inEncTail
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
    let usmConstEncEq := inToExprElim inUsmConstEnc
    let argAliasFinalEq: argAlias = arg := argAliasEq.trans argEq.symm
    let fnAliasFinalEq: fnAlias = fn := fnAliasEq.trans fnEq.symm

    let exprEncEq :=
      let nestedEncEq:
        (uniSetMapDl.uniSetMapConst.encoding.encodeCall fn.toExpr.encoding).encodeCall arg.toExpr.encoding
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
            (BasicExpr.const uniSetMapDl.consts.uniSetMap)
            fn.toExpr)
      let eqStep1 :=
        (Expr.encodeCall_eq
          ((BasicExpr.const uniSetMapDl.consts.uniSetMap).call fn.toExpr))
          arg.toExpr
      eqStep0.trans (eqStep1.trans nestedEncEq)

    Pair.eq dlEq (Pair.eq fvEq.symm exprEncEq)
  
  def callEnc_correct
    (fn arg: Pair)
  :
    uniSetMap.call (fn.callEnc arg) = (uniSetMap.call fn).call arg
  :=
    let fnCallExpr :=
      (BasicExpr.const uniSetMapDl.consts.uniSetMap).call fn.toExpr
    let fullExpr := fnCallExpr.call arg.toExpr
    let fnCallExprClean: fnCallExpr.IsClean :=
      fun x usesX =>
        usesX.elim
          (fun 
          | Or.inr (Or.inl fnUses) => fn.toExpr_IsClean (x + 1) fnUses)
          nofun
    let eqAt := FiniteDefList.uniSetMapAt_eq uniSetMapDl [] fullExpr
    let eqCall :=
      BasicExpr.pair_call_expr_call_eq
        fnCallExpr
        fnCallExprClean
        arg
        []
        uniSetMapDl.wfm
        uniSetMapDl.wfm
    let eqFn :=
      BasicExpr.pair_call_expr_call_eq
        (BasicExpr.const uniSetMapDl.consts.uniSetMap)
        (by decide)
        fn
        []
        uniSetMapDl.wfm
        uniSetMapDl.wfm
    eqAt.trans (eqCall.trans (congrArg (fun s => s.call arg) eqFn))
  
  def callEnc_call
    (fn arg: SingleLaneExpr)
    (lane: Set3.Lane)
  :
    SingleLaneExpr
  :=
    ((const lane callFixDl.consts.callEnc).call fn).call arg
  
  def callEnc_eq_singleton {fv iFn iArg lane}
    {fn arg: SingleLaneExpr}
    (inFn:
      ∀ pRes,
      Eq
        (fn.intp2
          (.pair iArg pRes :: pRes :: fv)
          callFixDl.wfm
          callFixDl.wfm)
        {iFn}
    )
    (inArg:
      ∀ pRes,
      Eq
        (arg.intp2 (pRes :: fv) callFixDl.wfm callFixDl.wfm)
        {iArg}
    )
  :
    Eq
      ((callEnc_call fn arg lane).intp2
        fv
        callFixDl.wfm
        callFixDl.wfm)
      {iFn.callEnc iArg}
  :=
    Set.ext fun p => Iff.intro
      (fun inCallEnc =>
        let inInnerCall := inCallElimSingle inCallEnc (inArg p)
        let inConstCallEnc :=
          inCallElimSingle inInnerCall (inFn p)
        (callEnc_elim inConstCallEnc.toPos).symm)
      (fun pEq =>
        pEq ▸
        inCall
          (inCall
            (callEnc_ins iFn iArg).toLane
            ((inFn (iFn.callEnc iArg)) ▸ rfl))
          ((inArg (iFn.callEnc iArg)) ▸ rfl))
  
  
  def magic_ins {iFn iArg lane p}
    (ins: ((uniSetMap.call iFn).call (iArg.callEnc iArg)).getLane lane p)
  :
    ((vals.magic.call iFn).call iArg).getLane lane p
  :=
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt callFixHelpersDl rfl rfl (by decide)
    let eqH :=
      callFixHelpersDl.extend_wfm_eq_of_lt callFixDl rfl rfl (by decide)
    let eqUni := eqU.trans eqH
    let ins:
      (callFixDl.wfm consts.uniSetMap).getLane lane
        (.pair iFn (.pair (iArg.callEnc iArg) p))
    :=
      eqUni.symm ▸ (Set3.inCallElim (Set3.inCallElim ins))
    let insCallEnc: ((BasicExpr.const 4).toLane lane).intp2 _ _ _ _ :=
      (callEnc_ins iArg iArg).toLane
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
    inPair
      (inVar rfl)
      (inPair (inVar rfl) (inToggle2 2 inMagicCall))
  
  def magic_elim {iFn iArg lane p}
    (ins: ((vals.magic.call iFn).call iArg).getLane lane p)
  :
    ((uniSetMap.call iFn).call (iArg.callEnc iArg)).getLane lane p
  :=
    let ins := Set3.inCallElim (Set3.inCallElim ins)
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨fnAlias, ins⟩ := inArbUnElim ins
    let ⟨argAlias, ins⟩ := inArbUnElim ins
    let ⟨inVarFn, ins⟩ := inPairElim ins
    let ⟨inVarArg, ins⟩ := inPairElim ins
    let fnEq := inVarElim inVarFn rfl
    let argEq := inVarElim inVarArg rfl
    
    let callEncEq := callEnc_eq_singleton (fun _ => rfl) (fun _ => rfl)
    let ins := inCallElimSingle ins callEncEq
    let ins := inCallElimSingle ins rfl
    let ins := inToggle2Elim 6 ins
    let eqU :=
      uniSetMapDl.extend_wfm_eq_of_lt callFixHelpersDl rfl rfl (by decide)
    let eqH :=
      callFixHelpersDl.extend_wfm_eq_of_lt callFixDl rfl rfl (by decide)
    let eqUni := eqU.trans eqH
    let ins:
      (uniSetMapDl.wfm consts.uniSetMap).getLane lane
        (.pair fnAlias (.pair (argAlias.callEnc argAlias) p))
    :=
       eqUni ▸ ins
    Set3.inCall (Set3.inCall (fnEq ▸ argEq ▸ ins))
  
  def magic_call_eq
    (iFn iArg: Pair)
  :
    Eq
      ((vals.magic.call iFn).call iArg)
      ((uniSetMap.call iFn).call (iArg.callEnc iArg))
  :=
    Set3.eq4
      (fun _ => magic_elim (lane := .defLane))
      (fun _ => magic_ins (lane := .defLane))
      (fun _ => magic_elim (lane := .posLane))
      (fun _ => magic_ins (lane := .posLane))
  
  def magicCallIndex (iFn: Pair): Pair :=
    (magicIndex.callEnc iFn).callEnc (magicIndex.callEnc iFn)
  
  def magicCallIndex_eq
    (iFn: Pair)
  :
    Eq
      (uniSetMap.call (magicCallIndex iFn))
      ((vals.magic.call iFn).call (magicIndex.callEnc iFn))
  :=
    let iCall := magicIndex.callEnc iFn
    let eqOuter := callEnc_correct iCall iCall
    let eqInnerCall := callEnc_correct magicIndex iFn
    let eqMagicParent :=
      (callFixHelpersDl.uniSetMapAt_eq
        []
        (.const callFixHelpersDl.consts.magic))
    let eqMagicChild :=
      callFixHelpersDl.extend_wfm_eq_of_lt
        callFixDl
        rfl
        rfl
        (by decide)
    eqOuter ▸
    eqInnerCall ▸
    congrArg
      (fun s => s.call iCall)
      (congrArg (fun s => s.call iFn) (eqMagicParent.trans eqMagicChild))
  
  
  def callFix_ins {iFn lane p}
    (ins:
      Set3.getLane
        ((vals.magic.call iFn).call (magicIndex.callEnc iFn))
        lane
        p)
  :
    (vals.callFix.call iFn).getLane lane p
  :=
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp2_toExpr_eq_singleton magicIndex)
        (fun _ => intp2_var_eq_singleton rfl)
    Set3.inCall <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inPair
      (inVar rfl)
      (inCall
        (inCall
          (inToggle2 5 (Set3.inCallElim (Set3.inCallElim ins)))
          rfl)
        (callEncEq ▸ rfl))

  def callFix_elim {iFn lane p}
    (ins: (vals.callFix.call iFn).getLane lane p)
  :
    ((vals.magic.call iFn).call (magicIndex.callEnc iFn)).getLane lane p
  :=
    let ins := Set3.inCallElim ins
    let ins := DefList.InWfm.in_def_no_fv (lane := lane) ins
    let ⟨_, ins⟩ := inArbUnElim ins
    let ⟨inVarI, ins⟩ := inPairElim ins
    let iEq := inVarElim inVarI rfl
    let ins := inToggle2Elim 1 ins
    let callEncEq :=
      callEnc_eq_singleton
        (fun _ => intp2_toExpr_eq_singleton magicIndex)
        (fun _ => intp2_var_eq_singleton rfl)
    let ins := inCallElimSingle ins callEncEq
    let ins := inCallElimSingle ins (intp2_var_eq_singleton rfl)
    Set3.inCall (Set3.inCall (iEq ▸ (inToggle2Elim 4 ins)))

  def callFix_call_eq
    (iFn: Pair)
  :
    Eq
      (vals.callFix.call iFn)
      (uniSetMap.call (magicCallIndex iFn))
  :=
    Set3.eq4
      (fun _ ins =>
        magicCallIndex_eq iFn ▸ callFix_elim (lane := .defLane) ins)
      (fun _ ins =>
        callFix_ins (lane := .defLane) (magicCallIndex_eq iFn ▸ ins))
      (fun _ ins =>
        magicCallIndex_eq iFn ▸ callFix_elim (lane := .posLane) ins)
      (fun _ ins =>
        callFix_ins (lane := .posLane) (magicCallIndex_eq iFn ▸ ins))
  
end callFixDl
