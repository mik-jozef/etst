import Etst.WFC.Syntax.FiniteDefList
import Etst.WFC.Utils.Expr.NegationNormalform

namespace Etst
open SingleLaneExpr


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
    | pair left rite  => (5, (left, rite))
    | ir left rite    => (6, (left, rite))
    | un left rite    => (7, (left, rite))
    | full body       => (8, body)
    | some body       => (9, body)
    | arbIr body      => (10, body)
    | arbUn body      => (11, body)
  ```
  
  Any pair that does not conform to one of the above encodings is
  considered as defining (an expression denoting) the empty triset.
  
  A definition list (with all but finitely many definitions at the
  start being empty) is encoded as a list of expression encodings.
  
  Note: we need to use negation normal form because the definitions
  below have different semantics, while `uniSetMap` below would
  otherwise effectively convert one to the other:
  
  ```
    -- The empty set
    let T := ~~T
    
    -- The undetermined set
    let A := ~B
    let B := ~A
  ```
-/

namespace uniSetMapDl
  def getNthConst: BasicExpr := .const 0
  def uniSetMapConst: BasicExpr := .const 1
  
  def exprEncConst: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex x,
      & (?some (0, x) & expr)
      & [uniSetMapConst] (dl, (null, [getNthConst] dl x))
    )
  
  def exprEncComplConst: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex x,
      & (?some (1, x) & expr)
      & ! [uniSetMapConst] (dl, (null, [getNthConst] dl x))
    )
  
  def exprEncVar: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex x,
      & (?some (2, x) & expr)
      & [getNthConst] fv x
    )
  
  def exprEncComplVar: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex x,
      & (?some (3, x) & expr)
      & ! [getNthConst] fv x
    )
  
  def exprEncNull: BasicExpr :=
    s3(
      null; dl, fv, expr;
      & (?some (4, null) & expr)
      & null
    )
  
  def exprEncPair: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex left,
      Ex rite,
      & (?some (5, (left, rite)) & expr)
      & (
        [uniSetMapConst] (dl, (fv, left)),
        [uniSetMapConst] (dl, (fv, rite))
      )
    )
  
  def exprEncIr: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex left,
      Ex rite,
      & (?some (6, (left, rite)) & expr)
      & [uniSetMapConst] (dl, (fv, left))
      & [uniSetMapConst] (dl, (fv, rite))
    )
  
  def exprEncUn: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex left,
      Ex rite,
      & (?some (7, (left, rite)) & expr)
      & (
        | [uniSetMapConst] (dl, (fv, left))
        | [uniSetMapConst] (dl, (fv, rite))
      )
    )
  
  def exprEncFull: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex body,
      & (?some (8, body) & expr)
      & (?full [uniSetMapConst] (dl, (fv, body)))
    )
  
  def exprEncSome: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex body,
      & (?some (9, body) & expr)
      & (?some [uniSetMapConst] (dl, (fv, body)))
    )
  
  def exprEncArbIr: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex body,
      & (?some (10, body) & expr)
      & (All p, [uniSetMapConst] (dl, ((p, fv), body)))
    )
  
  def exprEncArbUn: BasicExpr :=
    s3(
      null; dl, fv, expr;
      Ex body,
      & (?some (11, body) & expr)
      & (Ex p, [uniSetMapConst] (dl, ((p, fv), body)))
    )
  
  def exprEncList: BasicExpr :=
    s3(
      null,
      | [exprEncConst]
      | [exprEncComplConst]
      | [exprEncVar]
      | [exprEncComplVar]
      | [exprEncNull]
      | [exprEncPair]
      | [exprEncIr]
      | [exprEncUn]
      | [exprEncFull]
      | [exprEncSome]
      | [exprEncArbIr]
      | [exprEncArbUn]
    )
end uniSetMapDl

open uniSetMapDl in
pairDefList uniSetMapDl
  s3 getNth :=
    Ex head,
    Ex tail,
    | ((head, tail), (0, head))
    | (Ex i, ((head, tail), ((i, null), getNth tail i)))
  
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
  s3 uniSetMap :=
    Ex dl, Ex fv, Ex expr, ((dl, (fv, expr)), [exprEncList])
pairDefList.

namespace uniSetMapDl
  -- Assert the correctness of the consts.
  example: .const (consts.getNth) = getNthConst := rfl
  example: .const (consts.uniSetMap) = uniSetMapConst := rfl
end uniSetMapDl

-- Any pair not in the codomain encodes `none`.
def BasicExpr.encodingNnf: BasicExpr → Pair
| .const x => .pair (.nat 0) (.nat x)
| .compl (.const x) => .pair (.nat 1) (.nat x)
| .var x => .pair (.nat 2) (.nat x)
| .compl (.var x) => .pair (.nat 3) (.nat x)
| .null => .pair (.nat 4) .null
| .pair left rite =>
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

def BasicExpr.encoding
  (expr: BasicExpr)
:
  Pair
:=
  BasicExpr.encodingNnf expr.toNnf

def DefList.prefix
  (dl: DefList)
  (n: Nat)
:
  DefList
:= {
  getDef x := if x < n then dl.getDef x else .none
  isClean x :=
    if h: x < n
    then if_pos h ▸ dl.isClean x
    else if_neg h ▸ nofun
}

def DefList.prefixList
  (dl: DefList)
  (start: Nat)
:
  Nat → List Pair
| 0 => []
| length + 1 =>
  (dl.getDef start).encoding :: (dl.prefixList (start + 1) length)

def DefList.prefixEncoding
  (dl: DefList)
  (n: Nat)
:
  Pair
:=
  .listEncoding (dl.prefixList 0 n)


def DefList.prefix_eq_at
  {dl: DefList}
  {n x} (lt: x < n)
:
  (dl.prefix n).getDef x = dl.getDef x
:=
  if_pos lt

def DefList.prefix_none_at
  {dl: DefList}
  {n x} (nlt: ¬ x < n)
:
  (dl.prefix n).getDef x = .none
:=
  if_neg nlt

def DefList.prefixList_length_eq
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


def DefList.prefixList_at_eq_start
  (dl: DefList)
  (start length x: Nat)
:
  Eq
    (Option.getD
      (dl.prefixList start length)[x]?
      (BasicExpr.encoding .none))
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

def DefList.prefixList_at_eq
  (dl: DefList)
  (n x: Nat)
:
  Eq
    ((dl.prefixList 0 n)[x]?.getD (BasicExpr.encoding .none))
    ((dl.prefix n).getDef x).encoding
:= by
  conv => rhs; rw [←Nat.zero_add x, ←Nat.zero_add n]
  exact dl.prefixList_at_eq_start 0 n x


noncomputable def uniSetMap: Set3 Pair := uniSetMapDl.vals.uniSetMap

def uniSetMapIndex
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  Pair
:=
  Pair.pair
    (dl.prefixEncoding n)
    (.pair (.listEncoding fv) expr.encoding)

def uniSetMapIndexDef
  (dl: DefList)
  (n: Nat)
  (x: Nat)
:
  Pair
:=
  uniSetMapIndex dl n [] ((dl.prefix n).getDef x)

def uniSetMapAt
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  Set3 Pair
:=
  uniSetMap.pairCallJust (uniSetMapIndex dl n fv expr)


namespace uniSetMapDl
  def getNthEnc
    (list: List Pair)
    (i: Nat)
    (valEnc: Pair)
  :
    Pair
  :=
    .pair (.listEncoding list) (.pair (.nat i) valEnc)
  
  def getDefNthEnc
    (dl: DefList)
    (n i: Nat)
  :
    Pair
  :=
    getNthEnc
      (dl.prefixList 0 n)
      i
      ((dl.prefix n).getDef i).encoding
  
  def getNth {list i lane}
    (lt: i < list.length)
  :
    (uniSetMapDl.wfm consts.getNth).getLane
      lane
      (getNthEnc list i list[i])
  :=
    match list with
    | listH :: listT =>
      let ins :=
        match i with
        | 0 => inUnL (inPair (inPair rfl rfl) (inPair (inNat 0) rfl))
        | iPred + 1 =>
          let ih := getNth (Nat.lt_of_succ_lt_succ lt)
          inUnR
            (inArbUn
              iPred
              (inPair
                (inPair rfl rfl)
                (inPair
                  (inPair rfl inNull)
                  (inCall (inCall (inToggle2 8 ih) rfl) rfl))))
      InWfm.of_in_def_no_fv
        (inArbUn
          listH
          (inArbUn
            (.listEncoding listT)
            ins))
  
  def getNthDl {dl n i lane}
    (lt: i < n)
  :
    (uniSetMapDl.wfm consts.getNth).getLane
      lane
      (getDefNthEnc dl n i)
  := by
    let lt := (dl.prefixList_length_eq 0 n).symm ▸ lt
    unfold getDefNthEnc
    rw [←dl.prefixList_at_eq n i]
    rw [(List.getElem?_eq_some_getElem_iff lt).mpr trivial]
    exact getNth (i:=i) lt
  
  def getNthElim {list i valEnc lane}
    (inGetDef:
      (uniSetMapDl.wfm consts.getNth).getLane
        lane
        (getNthEnc list i valEnc))
  :
    list[i]? = valEnc
  :=
    let ins := InWfm.in_def_no_fv inGetDef
    let ⟨_, ins⟩ := inArbUnElim ins
    let ⟨_, ins⟩ := inArbUnElim ins
    (inUnElim ins).elim
      (fun ins =>
        let ⟨inList, ins⟩ := inPairElim ins
        let ⟨_, _, listEq, inHead, _⟩ := inPairElimEx inList
        let headEq := inVarElim inHead rfl
        let ⟨inI, ins⟩ := inPairElim ins
        let iEq := Pair.nat_inj_eq (inNatElim (n:=0) inI)
        let valEncEq := inVarElim ins rfl
        match list with
        | _h :: _t =>
          let hEq := Pair.noConfusion listEq fun eq _ => eq
          iEq ▸ hEq ▸ headEq ▸ valEncEq ▸ rfl)
      (fun ins =>
        let ⟨_iPredEnc, ins⟩ := inArbUnElim ins
        let ⟨inList, ins⟩ := inPairElim ins
        let ⟨inI, insLB⟩ := inPairElim ins
          match list, i with
        | _h :: t, iPred+1 =>
          let ⟨_, inTail⟩ := inPairElim inList
          let tailEq := inVarElim inTail rfl
          let ⟨inIPred, _⟩ := inPairElim inI
          let iPredEq := inVarElim inIPred rfl
          let ins := inCallElimSingle insLB rfl
          let ins := inCallElimSingle ins rfl
          let ih: t[iPred]? = valEnc :=
            getNthElim (tailEq ▸ iPredEq ▸ ins)
          ih)
  
  def getNthElimLt {list i valEnc lane}
    (inGetDef:
      (uniSetMapDl.wfm consts.getNth).getLane
        lane
        (getNthEnc list i valEnc))
  :
    i < list.length
  :=
    let eqSome := getNthElim inGetDef
    (List.getElem?_eq_some_iff.mp eqSome).choose
  
  def getNthLaneSwap {list i valEnc laneA laneB}
    (inGetDef:
      (uniSetMapDl.wfm consts.getNth).getLane
        laneA
        (getNthEnc list i valEnc))
  :
    (uniSetMapDl.wfm consts.getNth).getLane
      laneB
      (getNthEnc list i valEnc)
  :=
    let lt := getNthElimLt inGetDef
    let valEq := getNthElim inGetDef
    let eq := (List.getElem?_eq_some_getElem_iff lt).mpr trivial
    have valEq: list[i] = valEnc := Option.some.inj (eq ▸ valEq)
    valEq ▸ getNth lt
  
  def getNthElimD {list i valEnc lane df}
    (inGetDef:
      intp
        (const lane consts.getNth)
        []
        uniSetMapDl.wfm
        (getNthEnc list i valEnc))
  :
    list[i]?.getD df = valEnc
  :=
    getNthElim inGetDef ▸ rfl
  
  def getNthEq {dl: DefList} {n x exprEnc lane}
    (inGetNth:
      (uniSetMapDl.wfm consts.getNth).getLane
        lane
        (getNthEnc (dl.prefixList 0 n) x exprEnc))
  :
    exprEnc = ((dl.prefix n).getDef x).encoding
  :=
    dl.prefixList_at_eq n x ▸ (getNthElimD inGetNth).symm

end uniSetMapDl
