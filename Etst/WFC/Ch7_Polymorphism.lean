/-
  # Chapter 7: Polymorphism
  
  Used syntax sugars:
  
  - named variables: Eg. `Ex x, x` instead of `arbUn (var 0)`
  - function calls: `f x`, see `Expr.call` in `PairExpr.lean`
    for syntax, and `Set3.call` for a restricted semantic
    version.
  - parameters: `s3 Foo (x: Bar) := [body]` instead of
    `s3 Foo := Ex x, (some x & Bar) & (x, [body])`
  
  Function calls and parameters work together just as one would expect:
  for `s3 Foo n := (n, null)`, the expression `Foo x` evaluates to the
  same value as `(x, null)`.
  
  ## The what
  
  WFC does not "natively" support polymorphism or quantification over
  types (ie. definable trisets). Nevertheless, it is powerful enough
  that we can build these features ourselves in it. This chapter shows
  how.
  
  Note: because blah blah, this "trick" allows higher order polymorphism
  as well.
  
  On a more theoretical level, the chapter can be understood as showing
  that diagonalization arguments a la the diagonal lemma and Rogers's
  fixed-point theorem go through in WFC, and we can define fixed points
  of arbitrary definable transformations of definable trisets, internally.
  
  ## The easy part
  
  The initial "showing how" proceeds by example -- here is a simple
  definition of a list of natural numbers:
  
  ```
    s3 Nat := null | (Nat, null) -- zero or successor
    s3 ListNat :=
      | null -- the empty list
      | (Nat, ListNat) -- a head and tail
  ```
  
  We would like to quantify this definition with a type of the elements
  of the list instead of hardcoding `Nat`. Thanks to `uniSetMap` from
  the previous chapter, this is a really easy task:
  
  ```
    s3 List (T: Any) :=
      | null
      | (uniSetMap T, List T)
  ```
  
  From the previous chapter, we know that for any definable triset `t`,
  there is an index pair `i` such that `uniSetMap i` evaluates to `t`.
  
  This index pair is just a mechanical encoding of an expression defining
  `t` (along with a definition list defining the constants used by the
  expression, and a list of free variables with which to interpret it),
  and is computable from these three -- see `uniSetMapIndex`. (The fourth
  param, `n`, just needs to be large enough so that all used constants
  are less than `n`.
  
  Thanks to the above, a caller wishing to use a List of eg. pairs of
  naturals just needs to mechanically convert `(Nat, Nat)` to the
  corresponding index, and then use `List i`.
  
  This also means that quantification over types collapses to
  quantification over pairs, and it is up to authors of definitions to
  decide whether they will use a parameter as a pair or an encoding of
  a type.
  
  So far, all is well... that is, unless the caller would like to pass
  to `List` the type they are trying to define in the first place. What
  about definitions like `s3 Foo := List (Foo | Nat)`?
  
  ## The self-referential case
  
  TODO diagonal lemma? we're being syntactic after all
  The answer is Rogers's fixed-point theorem. An index representing such
  a definition is guaranteed to exist, even in case of multiple mutually
  self-referential definitions. We prove that in this chapter.
  
  TODO revisit this description when the chapter is done, make sure it
  is accurate.
  
  For example, the type
  
      s3 Foo := List (Foo | null)
  
  will be defined as a fixed point of
  
      s3 FooT Foo := List (uniSetMap Foo | null)
  
  Footnotes:
  0. To quote a legend: "I am dogmatic, and I believe that 0 is the very
    zerost number." No particular reason for the quotation is given.
    https://tex.stackexchange.com/questions/325340/
-/

import Etst.WFC.Ch6_SelfDefinability
import Etst.WFC.Utils.Expr.FreeVars

namespace Etst


-- TODO the chapter lol. don't forget to clean up.

-- ## Section: Single definition version

namespace Pair
  -- Represents the encoding of `Expr.call`, see `callEncExpr_eq` below.
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
  
  noncomputable def diagMagic (op i: Pair): Set3 Pair :=
    (uniSetMap.call op).call (callEnc i i)
  
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
  s3 magic := Ex op i, (op, (i, uniSetMap op (callEnc i i)))
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
    sorry
  
  -- TODO what about this form?
  -- def callEnc_elim {fn arg p}
  --   (inCallEnc: ((vals.callEnc.call fn).call arg).posMem p)
  -- :
  --   p = fn.encodeCall arg
  -- :=
  --   sorry
  
  
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
  
end callFixDl


def callFixCallExpr (iFn: Pair): BasicExpr :=
  (BasicExpr.const callFixDl.consts.callFix).call iFn.toExpr

def callFixCallIndex (iFn: Pair): Pair :=
  uniSetMapIndex
    callFixDl.toDefList
    (callFixDl.consts.callFix + 1)
    []
    (callFixCallExpr iFn)


def callFixCallExpr_UsesConst_lt
  (iFn: Pair)
:
  callFixDl.IsExprBoundedBy
    (callFixCallExpr iFn)
    (callFixDl.consts.callFix + 1)
:=
  callFixDl.isExprBoundedBy (callFixCallExpr iFn)
  

def callFixCallIndex_eq (iFn: Pair):
  callFixDl.vals.callFix.call iFn = uniSetMap.call (callFixCallIndex iFn)
:=
  let eqL :=
    BasicExpr.pair_call_expr_call_eq
      (.const callFixDl.consts.callFix)
      (by decide)
      iFn
      []
      callFixDl.wfm
      callFixDl.wfm
  let eqR :=
    (callFixDl.uniSetMapAt_eq
      []
      ((BasicExpr.const callFixDl.consts.callFix).call iFn.toExpr))
  eqL.symm.trans eqR.symm

def callFixCallIndex_fix
  (iFn: Pair)
:
  Eq
    (uniSetMap.call (callFixCallIndex iFn))
    ((uniSetMap.call iFn).call (callFixCallIndex iFn))
:=
  callFixCallIndex_eq iFn ▸
  sorry





-- Goal: a practical way to use this. Delete later?
pairDefList ExamplePolymorphismDl extends callFixDl
  -- Note: pairDefList does not yet support param syntax, so we
  -- desugar it manually.
  s3 List :=
    Ex T, (
      T,
      | null
      | (uniSetMap T, List T)
    )
  
  -- s3 Foo := List Foo
  -- s3 FooNull := List (FooNull | null)
  s3 FooNullT := Ex T, (T, List (T | null))
pairDefList.


-- TODO either delete later, or fix the hack in the impl.
def FinBoundedDL.getConstEncoding
  (dl: FinBoundedDL)
  (x: Nat)
:
  Pair
:=
  uniSetMapIndex
    dl.toDefList
    (x + 1) -- just a hack assuming the definition does not use latter constants.
    []
    (.const x)

open ExamplePolymorphismDl in
def listIndex: Pair :=
  ExamplePolymorphismDl.getConstEncoding consts.List

open ExamplePolymorphismDl in
def fooNullIndex: Pair :=
  ExamplePolymorphismDl.getConstEncoding consts.FooNullT


pairDefList ExamplePolymorphismUsageDl extends ExamplePolymorphismDl
  -- TODO: uncomment when not reliant on sorry.
  -- s3 Foo := callFix [listIndex.toExpr]
  -- s3 FooNull := callFix [fooNullIndex.toExpr]
pairDefList.
