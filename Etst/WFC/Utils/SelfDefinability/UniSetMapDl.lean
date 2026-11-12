/-
  A note for the future: If I were to redo ch6, I would probably
  want to refactor it:
  - split into multiple, smaller modules,
  - decompose some of the large proofs, think about organisation
    of the whole thing in general,
  - improve the naming, namespaces etc.
  - make uniSetMapIndexEnc irreducible?
  
  (Most of?) the content of the Ch6 utility files is meant to be
  private (unless exposed in Ch6 itself).
-/
module
public import Etst.WFC.Ch4_S1_MembershipPs
public import Etst.WFC.Utils.NamedDefList.NamedPairExpr
public import Etst.WFC.Utils.Expr.NegationNormalForm
import Etst.WFC.Utils.DefList
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst


/-
  Naturals are encoded with null as zero, and (n, null) as n+1.
  Lists are encoded with null as the empty list, and
  (head, tail) as a non-empty list.
  
  Expressions are converted to negation normal form and then encoded
  like this:
  
  ```
    | const x         => (0, x)
    | compl (const x) => (1, x)
    | var x           => (2, x)
    | compl (var x)   => (3, x)
    | null            => (4, null)
    | prod left rite  => (5, (left, rite))
    | ir left rite    => (6, (left, rite))
    | un left rite    => (7, (left, rite))
    | full body       => (8, body)
    | some body       => (9, body)
    | arbIr body      => (10, body)
    | arbUn body      => (11, body)
  ```
  
  A (finite prefix of a) definition list (the initial `n` definitions)
  is encoded as a list of expression encodings.
  
  An index is a pair `(dlEnc, (fv, exprEnc))`, where `dlEnc` encodes
  a definition list, `fv` is a list of free variables, and `exprEnc`
  is an encoding of an expression. It represents the interpretation of
  that expression using the definition list and `fv`.
  
  `uniSetMap` interprets indices -- `uniSetMap i` evaluates to the
  triset the index represents.
  
  For convenience, `uniSetMap` supports two extra encoding cases that
  do not directly correspond to any expression encoding.
  
  ```
    | uniSetMap => (12, null)
    | toEncoding b => (13, b)
  ```
  
  - `(12, null)` represents the triset `uniSetMap` (without the index
    having to define it explicitly in its definition list), and
  - `(13, b)` represents the singleton triset containing the encoding
    of `b`. Eg. `(13, null)` represents `{ (4, null) }`.
  
  Although these are a conservative extension, we include them because
  they considerably reduce the size of the indices for some use cases
  (see eg. Chapters 7 and 8).
  
  Any pair that is not a valid index defines the empty triset.
  
  
  Note: We need to use negation normal form because the definitions
  below have different semantics, while `uniSetMap` would otherwise
  effectively convert one to the other:
  
  ```
    -- The empty set
    let T := ~~T
    
    -- The undetermined set
    let A := ~B
    let B := ~A
  ```
-/

namespace Pair
  exposed def constEnc (n: Nat): Pair := .pair (.nat 0) (.nat n)
  exposed def complConstEnc (n: Nat): Pair := .pair (.nat 1) (.nat n)
  exposed def varEnc (n: Nat): Pair := .pair (.nat 2) (.nat n)
  exposed def complVarEnc (n: Nat): Pair := .pair (.nat 3) (.nat n)
  exposed def nullEnc: Pair := .pair (.nat 4) (.nat 0)
  exposed def prodEnc (a b: Pair): Pair := .pair (.nat 5) (.pair a b)
  exposed def irEnc (a b: Pair): Pair := .pair (.nat 6) (.pair a b)
  exposed def unEnc (a b: Pair): Pair := .pair (.nat 7) (.pair a b)
  exposed def fullEnc (a: Pair): Pair := .pair (.nat 8) a
  exposed def someEnc (a: Pair): Pair := .pair (.nat 9) a
  exposed def arbIrEnc (a: Pair): Pair := .pair (.nat 10) a
  exposed def arbUnEnc (a: Pair): Pair := .pair (.nat 11) a
  exposed def uniSetMapEnc: Pair := .pair (.nat 12) .null
  exposed def toEncodingEnc (b: Pair): Pair := .pair (.nat 13) b
end Pair

namespace uniSetMapDl
  exposed def exprEncConst :=
    p3(
      dl, fv, expr;
      Ex x,
      & (?some 0 × x & expr)
      & uniSetMap (dl × null × getNth dl x)
    )
  
  exposed def exprEncComplConst :=
    p3(
      dl, fv, expr;
      Ex x,
      & (?some 1 × x & expr)
      & ! uniSetMap (dl × null × getNth dl x)
    )
  
  exposed def exprEncVar :=
    p3(
      dl, fv, expr;
      Ex x,
      & (?some 2 × x & expr)
      & getNth fv x
    )
  
  exposed def exprEncComplVar :=
    p3(
      dl, fv, expr;
      Ex x,
      & (?some 3 × x & expr)
      & ! getNth fv x
    )
  
  exposed def exprEncNull :=
    p3(
      dl, fv, expr;
      & (?some 4 × null & expr)
      & null
    )
  
  exposed def exprEncProd :=
    p3(
      dl, fv, expr;
      Ex left rite,
      & (?some 5 × left × rite & expr)
      & (
        × uniSetMap (dl × fv × left)
        × uniSetMap (dl × fv × rite)
      )
    )
  
  exposed def exprEncIr :=
    p3(
      dl, fv, expr;
      Ex left rite,
      & (?some 6 × left × rite & expr)
      & uniSetMap (dl × fv × left)
      & uniSetMap (dl × fv × rite)
    )
  
  exposed def exprEncUn :=
    p3(
      dl, fv, expr;
      Ex left rite,
      & (?some 7 × left × rite & expr)
      & (
        | uniSetMap (dl × fv × left)
        | uniSetMap (dl × fv × rite)
      )
    )
  
  exposed def exprEncFull :=
    p3(
      dl, fv, expr;
      Ex body,
      & (?some 8 × body & expr)
      & (?full uniSetMap (dl × fv × body))
    )
  
  exposed def exprEncSome :=
    p3(
      dl, fv, expr;
      Ex body,
      & (?some 9 × body & expr)
      & (?some uniSetMap (dl × fv × body))
    )
  
  exposed def exprEncArbIr :=
    p3(
      dl, fv, expr;
      Ex body,
      & (?some 10 × body & expr)
      & All p, uniSetMap (dl × (p × fv) × body)
    )
  
  exposed def exprEncArbUn :=
    p3(
      dl, fv, expr;
      Ex body,
      & (?some 11 × body & expr)
      & Ex p, uniSetMap (dl × (p × fv) × body)
    )
  
  exposed def exprEncUniSetMap :=
    p3(
      dl, fv, expr;
      & (?some 12 × null & expr)
      & uniSetMap
    )
  
  /-
    `(13, b)` encodes the singleton triset `{ b.toExpr.encoding }`, ie.
    the encoding of the expression that evaluates to `b`. As `b` may be
    the value of a runtime variable, its encoding has to be computed
    recursively, using the `(13, _)` case itself on the sub-pairs.
  -/
  exposed def exprEncToEncoding :=
    p3(
      dl, fv, expr;
      Ex b,
      & (?some 13 × b & expr)
      & (
          (b & null then 4 × null)
          |
          (Ex l r,
          (b & l × r then
            5 × (uniSetMap (dl × fv × (13 × l))
                × uniSetMap (dl × fv × (13 × r)))))
        )
    )
  
  exposed def exprEncList :=
    p3(
      dl, fv, expr;
      | <[exprEncConst]>
      | <[exprEncComplConst]>
      | <[exprEncVar]>
      | <[exprEncComplVar]>
      | <[exprEncNull]>
      | <[exprEncProd]>
      | <[exprEncIr]>
      | <[exprEncUn]>
      | <[exprEncFull]>
      | <[exprEncSome]>
      | <[exprEncArbIr]>
      | <[exprEncArbUn]>
      | <[exprEncUniSetMap]>
      | <[exprEncToEncoding]>
    )
  
end uniSetMapDl

open uniSetMapDl in
exposed pairDefList uniSetMapDl
  p3 getNth :=
    Ex head,
    Ex tail,
    | (head × tail) × 0 × head
    | (Ex i, (head × tail) × (i × null) × getNth tail i)
  
  /-
    `uniSetMap` defines a triset of pairs `((dl, (fv, expr)), p)`
    where
    - `dl` is an encoding of a definition list,
    - `fv` a list of free variables for interpreting `expr`,
    - `expr` an encoding of an expression, and
    - `p` a pair that is a member of `expr`.
    
    For any definable triset, there exists a pair
    `(dl, ([], const x))`
    that serves as an index for it in `uniSetMap`.
  -/
  p3 uniSetMap :=
    Ex dl, Ex fv, Ex expr, (dl × fv × expr) × <[exprEncList.check]>
pairDefList.

namespace uniSetMapDl
  exposed def compileExprEnc
    (namedExpr: NamedPairExpr ExprKind.basic ["expr", "fv", "dl"])
    (isWf: namedExpr.IsWF uniSetMapDl.consts := by decide)
  :
    Expr .basic
  :=
    /-
      The const list is spelled out to be syntactically identical to
      what uniSetMapDl definitions are actually compiled with.
    -/
    (namedExpr.check isWf).val.compile
      ([] ++ (["getNth", "uniSetMap"]))
  
  exposed def exprEncConstRaw := compileExprEnc exprEncConst
  exposed def exprEncComplConstRaw := compileExprEnc exprEncComplConst
  exposed def exprEncVarRaw := compileExprEnc exprEncVar
  exposed def exprEncComplVarRaw := compileExprEnc exprEncComplVar
  exposed def exprEncNullRaw := compileExprEnc exprEncNull
  exposed def exprEncProdRaw := compileExprEnc exprEncProd
  exposed def exprEncIrRaw := compileExprEnc exprEncIr
  exposed def exprEncUnRaw := compileExprEnc exprEncUn
  exposed def exprEncFullRaw := compileExprEnc exprEncFull
  exposed def exprEncSomeRaw := compileExprEnc exprEncSome
  exposed def exprEncArbIrRaw := compileExprEnc exprEncArbIr
  exposed def exprEncArbUnRaw := compileExprEnc exprEncArbUn
  exposed def exprEncUniSetMapRaw := compileExprEnc exprEncUniSetMap
  exposed def exprEncToEncodingRaw := compileExprEnc exprEncToEncoding
  exposed def exprEncListRaw := compileExprEnc exprEncList
  
  
  -- Expose "const" in the namespace.
  exposed def cst
    (x: String)
    (isIn: x ∈ uniSetMapDl.consts := by decide)
  :
    Nat
  :=
    uniSetMapDl.const x isIn
  
  exposed def cstExpr
    (x: String)
    (isIn: x ∈ uniSetMapDl.consts := by decide)
  :
    Expr .basic
  :=
    .const () (cst x isIn)
end uniSetMapDl


-- Any pair not in the codomain encodes `none`.
exposed def Expr.encodingNnf: Expr .basic → Pair
| .const () x => .pair (.nat 0) (.nat x)
| .compl (.const () x) => .pair (.nat 1) (.nat x)
| .var x => .pair (.nat 2) (.nat x)
| .compl (.var x) => .pair (.nat 3) (.nat x)
| .null => .pair (.nat 4) .null
| .prod left rite =>
  .pair (.nat 5) (.pair left.encodingNnf rite.encodingNnf)
| .ir left rite =>
  .pair (.nat 6) (.pair left.encodingNnf rite.encodingNnf)
| .compl (.ir (.compl left) (.compl rite)) =>
  .pair (.nat 7) (.pair left.encodingNnf rite.encodingNnf)
| .full body => .pair (.nat 8) body.encodingNnf
| .compl (.full (.compl body)) => .pair (.nat 9) body.encodingNnf
| .arbIr body => .pair (.nat 10) body.encodingNnf
| .compl (.arbIr (.compl body)) => .pair (.nat 11) body.encodingNnf
| _ =>
  -- We don't care what non-nnf expressions encode as, but `none`
  -- is a convenient choice.
  .pair (.nat 10) (.pair (.nat 3) (.nat 0))

exposed def Expr.encoding
  (expr: Expr .basic)
:
  Pair
:=
  Expr.encodingNnf expr.toNnf


exposed def DefList.prefixList
  (dl: DefList)
  (start: Nat)
:
  Nat → List Pair
| 0 => []
| length + 1 =>
  (dl.getDef start).encoding :: (dl.prefixList (start + 1) length)

exposed def DefList.prefixEncoding
  (dl: DefList)
  (n: Nat)
:
  Pair
:=
  .listEncoding (dl.prefixList 0 n)

theorem DefList.prefixList_length_eq
  (dl: DefList)
  (start length: Nat)
:
  (dl.prefixList start length).length = length
:=
  match length with
  | 0 => rfl
  | lengthPred+1 =>
    let ih := dl.prefixList_length_eq (start + 1) lengthPred
    Nat.succ_inj.mpr ih

theorem DefList.prefixList_at_eq_start
  (dl: DefList)
  (start length x: Nat)
:
  Eq
    (Option.getD
      (dl.prefixList start length)[x]?
      (Expr.encoding .none))
    ((dl.prefix (start + length)).getDef (start + x)).encoding
:=
  match length, x with
  | 0, x =>
    let nlt := Nat.not_lt.mpr (Nat.le_add_right start x)
    prefix_none_at nlt ▸ rfl
  | _ + 1, 0 =>
    let lt := Nat.lt_succ_of_le (Nat.le_add_right _ _)
    (prefix_eq_at lt).symm ▸ rfl
  | lengthPred + 1, xPred + 1 =>
    let eq :=
      Nat.add_comm lengthPred 1 ▸
      Nat.add_comm xPred 1 ▸
      Nat.add_assoc start 1 lengthPred ▸
      Nat.add_assoc start 1 xPred ▸
      rfl
    let ih := dl.prefixList_at_eq_start (start + 1) lengthPred xPred
    ih.trans eq

theorem DefList.prefixList_at_eq
  (dl: DefList)
  (n x: Nat)
:
  Eq
    ((dl.prefixList 0 n)[x]?.getD (Expr.encoding .none))
    ((dl.prefix n).getDef x).encoding
:= by
  conv => rhs; rw [←Nat.zero_add x, ←Nat.zero_add n]
  exact dl.prefixList_at_eq_start 0 n x


exposed noncomputable def uniSetMap: Set3 Pair :=
  uniSetMapDl.val "uniSetMap"

exposed noncomputable def uniSetMapGetNth: Set3 Pair :=
  uniSetMapDl.val "getNth"

exposed def uniSetMapIndexEnc
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (exprEnc: Pair)
:
  Pair
:=
  Pair.pair
    (dl.prefixEncoding n)
    (.pair (.listEncoding fv) exprEnc)

exposed def uniSetMapIndex
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: Expr .basic)
:
  Pair
:=
  uniSetMapIndexEnc dl n fv expr.encoding

exposed def uniSetMapIndexDef
  (dl: DefList)
  (n: Nat)
  (x: Nat)
:
  Pair
:=
  uniSetMapIndex dl n [] ((dl.prefix n).getDef x)

exposed noncomputable def uniSetMapAt
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: Expr .basic)
:
  Set3 Pair
:=
  uniSetMap.call (uniSetMapIndex dl n fv expr)

def uniSetMapIndex.emptyIndex: Pair :=
  uniSetMapIndex
    FiniteDefList.empty.toDefList
    FiniteDefList.empty.size
    []
    .none


theorem uniSetMapIndex_nnf_eq {dl n fv expr}:
  uniSetMapIndex dl n fv expr =
    uniSetMapIndex dl n fv expr.toNnf
:= by
  unfold uniSetMapIndex Expr.encoding
  rw [expr.toNnf_idem]


namespace uniSetMapDl
  open Expr
  
  exposed def getNthEnc
    (list: List Pair)
    (i: Nat)
    (valEnc: Pair)
  :
    Pair
  :=
    .pair (.listEncoding list) (.pair (.nat i) valEnc)
  
  exposed def getDefNthEnc
    (dl: DefList)
    (n i: Nat)
  :
    Pair
  :=
    getNthEnc
      (dl.prefixList 0 n)
      i
      ((dl.prefix n).getDef i).encoding
  
  theorem getNth {list i lane}
    (lt: i < list.length)
  :
    getNthEnc list i list[i] ∈ uniSetMapGetNth.getLane lane
  :=
    match list with
    | listH :: listT =>
      let ins :=
        match i with
        | 0 => inUnL (inProd (inProd rfl rfl) (inProd (inNat 0) rfl))
        | iPred + 1 =>
          let ih := getNth (Nat.lt_of_succ_lt_succ lt)
          inUnR
            (inArbUn
              iPred
              (inProd
                (inProd rfl rfl)
                (inProd
                  (inProd rfl inNull)
                  (inCall (inCall ih rfl) rfl))))
      DefList.in_def_no_fv
        (inArbUn
          listH
          (inArbUn
            (.listEncoding listT)
            ins))
  
  theorem getNthDl {dl n i lane}
    (lt: i < n)
  :
    getDefNthEnc dl n i ∈ uniSetMapGetNth.getLane lane
  := by
    let lt := (dl.prefixList_length_eq 0 n).symm ▸ lt
    unfold getDefNthEnc
    rw [←dl.prefixList_at_eq n i]
    rw [(List.getElem?_eq_some_getElem_iff lt).mpr trivial]
    exact getNth (i:=i) lt
  
  theorem getNthElim {list i valEnc lane}
    (inGetDef: getNthEnc list i valEnc ∈ uniSetMapGetNth.getLane lane)
  :
    list[i]? = valEnc
  :=
    let ins := DefList.in_def_body_no_fv inGetDef
    let ⟨_, ins⟩ := inArbUnElim ins
    let ⟨_, ins⟩ := inArbUnElim ins
    (inUnElim ins).elim
      (fun ins =>
        let ⟨inList, ins⟩ := inProdElim ins
        let ⟨_, _, listEq, inHead, _⟩ := inProdElimEx inList
        let headEq := inVarElim inHead rfl
        let ⟨inI, ins⟩ := inProdElim ins
        let iEq := Pair.nat_inj_eq (inNatElim (n:=0) inI)
        let valEncEq := inVarElim ins rfl
        match list with
        | _h :: _t =>
          let hEq := Pair.noConfusion listEq fun eq _ => eq
          iEq ▸ hEq ▸ headEq ▸ valEncEq ▸ rfl)
      (fun ins =>
        let ⟨_iPredEnc, ins⟩ := inArbUnElim ins
        let ⟨inList, ins⟩ := inProdElim ins
        let ⟨inI, insLB⟩ := inProdElim ins
          match list, i with
        | _h :: t, iPred+1 =>
          let ⟨_, inTail⟩ := inProdElim inList
          let tailEq := inVarElim inTail rfl
          let ⟨inIPred, _⟩ := inProdElim inI
          let iPredEq := inVarElim inIPred rfl
          let ins := inCallElimSingle insLB rfl
          let ins := inCallElimSingle ins rfl
          let ih: t[iPred]? = valEnc :=
            getNthElim (tailEq ▸ iPredEq ▸ ins)
          ih)
  
  theorem getNthElimLt {list i valEnc lane}
    (inGetDef:
      getNthEnc list i valEnc ∈ uniSetMapGetNth.getLane lane)
  :
    i < list.length
  :=
    let eqSome := getNthElim inGetDef
    (List.getElem?_eq_some_iff.mp eqSome).choose
  
  theorem getNthLaneSwap {list i valEnc laneA laneB}
    (inGetDef: getNthEnc list i valEnc ∈ uniSetMapGetNth.getLane laneA)
  :
    getNthEnc list i valEnc ∈ uniSetMapGetNth.getLane laneB
  :=
    let lt := getNthElimLt inGetDef
    let valEq := getNthElim inGetDef
    let eq := (List.getElem?_eq_some_getElem_iff lt).mpr trivial
    have valEq: list[i] = valEnc := Option.some.inj (eq ▸ valEq)
    valEq ▸ getNth lt
  
  theorem getNthClassical {list i valEnc}:
    Or
      (uniSetMapDl.dl.Ins
        (uniSetMapDl.const "getNth")
        (getNthEnc list i valEnc))
      (uniSetMapDl.dl.Out
        (uniSetMapDl.const "getNth")
        (getNthEnc list i valEnc))
  :=
    Classical.or_iff_not_imp_left.mpr fun nins =>
      DefList.Out.isComplete fun isPos =>
        let isDef :=
          getNthLaneSwap (laneA:=.posLane) (laneB:=.defLane) isPos
        nins (DefList.Ins.isComplete isDef)
  
  theorem getNthElimD {list i valEnc lane df}
    (inGetDef: getNthEnc list i valEnc ∈ uniSetMapGetNth.getLane lane)
  :
    list[i]?.getD df = valEnc
  :=
    getNthElim inGetDef ▸ rfl
  
  theorem getNthEq {dl: DefList} {n x exprEnc lane}
    (inGetNth:
      (uniSetMapGetNth.getLane lane).Mem
        (getNthEnc (dl.prefixList 0 n) x exprEnc))
  :
    exprEnc = ((dl.prefix n).getDef x).encoding
  :=
    dl.prefixList_at_eq n x ▸ (getNthElimD inGetNth).symm

end uniSetMapDl
