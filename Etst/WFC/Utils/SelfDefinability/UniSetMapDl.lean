
import Etst.WFC.Syntax.FiniteDefList

namespace Etst

/-
  Naturals are encoded with null as zero, and (n, null) as n+1.
  Lists are encoded with null as the empty list, and
  (head, tail) as a non-empty list.
  
  Expressions are encoded like this:
  
  ```
    | const x        => (0, x)
    | var x          => (1, x)
    | null           => (2, null)
    | pair left rite => (3, (left, rite))
    | ir left rite   => (4, (left, rite))
    | full body      => (5, body)
    | compl body     => (6, body)
    | arbIr body     => (7, body)
  ```
  
  Any pair that does not conform to one of the above encodings is
  considered as defining (an expression denoting) the empty triset.
  
  A definition list (with all but finitely many definitions at the
  start being empty) is encoded as a list of expression encodings.
-/

def getNthConst: BasicExpr := .const 0
def uniSetMapConst: BasicExpr := .const 1

def exprEncConst: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex x,
    & (?some (0, x) & expr)
    & [uniSetMapConst] (dl, (null, [getNthConst] dl x))
  )

def exprEncVar: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex x,
    & (?some (1, x) & expr)
    & [getNthConst] fv x
  )

def exprEncNull: BasicExpr :=
  s3(
    null; dl, fv, expr;
    & (?some (2, null) & expr)
    & null
  )

def exprEncPair: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex left,
    Ex rite,
    & (?some (3, (left, rite)) & expr)
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
    & (?some (4, (left, rite)) & expr)
    & [uniSetMapConst] (dl, (fv, left))
    & [uniSetMapConst] (dl, (fv, rite))
  )

def exprEncFull: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex body,
    & (?some (5, body) & expr)
    & (?full [uniSetMapConst] (dl, (fv, body)))
  )

def exprEncCompl: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex body,
    & (?some (6, body) & expr)
    & (! [uniSetMapConst] (dl, (fv, body)))
  )

def exprEncArbIr: BasicExpr :=
  s3(
    null; dl, fv, expr;
    Ex body,
    & (?some (7, body) & expr)
    & (All p, [uniSetMapConst] (dl, ((p, fv), body)))
  )

def exprEncList: BasicExpr :=
  s3(
    null,
    | [exprEncConst]
    | [exprEncVar]
    | [exprEncNull]
    | [exprEncPair]
    | [exprEncIr]
    | [exprEncFull]
    | [exprEncCompl]
    | [exprEncArbIr]
  )

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

-- Assert the correctness of the consts.
example: .const (uniSetMapDl.consts.getNth) = getNthConst := rfl
example: .const (uniSetMapDl.consts.uniSetMap) = uniSetMapConst := rfl


def Pair.listEncoding: List Pair → Pair
| [] => .null
| p :: ps => .pair p (listEncoding ps)

-- Any pair not in the codomain encodes `none`.
def BasicExpr.encoding: BasicExpr → Pair
| .const x => .pair (.nat 0) (.nat x)
| .var x => .pair (.nat 1) (.nat x)
| .null => .pair (.nat 2) .null
| .pair left rite =>
  .pair (.nat 3) (.pair left.encoding rite.encoding)
| .ir left rite =>
  .pair (.nat 4) (.pair left.encoding rite.encoding)
| .full body => .pair (.nat 5) body.encoding
| .compl body => .pair (.nat 6) body.encoding
| .arbIr body => .pair (.nat 7) body.encoding

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
  (dl.getDef start).encoding :: (prefixList dl (start + 1) length)

def DefList.prefixEncoding
  (dl: DefList)
  (n: Nat)
:
  Pair
:=
  .listEncoding (prefixList dl 0 n)


def DefList.prefix_eq_at
  {dl: DefList}
  {n x} (lt: x < n)
:
  (dl.prefix n).getDef x = dl.getDef x
:=
  if_pos lt

def DefList.prefixList_at_eq_start {dl length x start exprEnc}
  (eq: (DefList.prefixList dl start length)[x]? = some exprEnc)
:
  exprEnc = ((dl.prefix (start + length)).getDef (start + x)).encoding
:=
  match length, x with
  | _ + 1, 0 =>
    let lt := Nat.lt_succ_of_le (Nat.le_add_right _ _)
    Option.some_inj.mp eq ▸ prefix_eq_at lt ▸ rfl
  | lengthPred + 1, xPred + 1 =>
    Nat.add_comm lengthPred 1 ▸
    Nat.add_comm xPred 1 ▸
    Nat.add_assoc start 1 lengthPred ▸
    Nat.add_assoc start 1 xPred ▸
    prefixList_at_eq_start eq

def DefList.prefixList_at_eq {dl n x exprEnc}
  (eq: (DefList.prefixList dl 0 n)[x]? = some exprEnc)
:
  exprEnc = ((dl.prefix n).getDef x).encoding
:=
  Nat.zero_add x ▸
  Nat.zero_add n ▸
  prefixList_at_eq_start eq


noncomputable def uniSetMap: Set3 Pair := uniSetMapDl.vals.uniSetMap

def uniSetMapIndex
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:=
  Pair.pair
    (dl.prefixEncoding n)
    (.pair (.listEncoding fv) expr.encoding)

def uniSetMapAt
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:=
  uniSetMap.pairCallJust (uniSetMapIndex dl n fv expr)


open SingleLaneExpr in
def uniSetMapDl.getDefElim {list i valEnc lane}
  (inGetDef:
    intp
    (.const lane 0)
    []
    uniSetMapDl.wfm
    (.pair (.listEncoding list) (.pair (.nat i) valEnc)))
:
  list[i]? = valEnc
:=
  let ine := InWfm.in_def_no_fv inGetDef
  let ⟨_, ine⟩ := inArbUnElim ine
  let ⟨_, ine⟩ := inArbUnElim ine
  (inUnElim ine).elim
    (fun ine =>
      let ⟨inList, ine⟩ := inPairElim ine
      let ⟨_, _, listEq, inHead, _⟩ := inPairElimEx inList
      let headEq := inVarElim inHead rfl
      let ⟨inI, ine⟩ := inPairElim ine
      let iEq := Pair.nat_inj_eq (inNatElim (n:=0) inI)
      let valEncEq := inVarElim ine rfl
      match list with
      | _h :: _t =>
        let hEq := Pair.noConfusion listEq fun eq _ => eq
        iEq ▸ hEq ▸ headEq ▸ valEncEq ▸ rfl)
    (fun ine =>
      let ⟨_iPredEnc, ine⟩ := inArbUnElim ine
      let ⟨inList, ine⟩ := inPairElim ine
      let ⟨inI, ineLB⟩ := inPairElim ine
        match list, i with
      | _h :: t, iPred+1 =>
        let ⟨_, inTail⟩ := inPairElim inList
        let tailEq := inVarElim inTail rfl
        let ⟨inIPred, _⟩ := inPairElim inI
        let iPredEq := inVarElim inIPred rfl
        let ine := inCallElimSingle ineLB rfl
        let ine := inCallElimSingle ine rfl
        let ih: t[iPred]? = valEnc :=
          getDefElim (tailEq ▸ iPredEq ▸ ine)
        ih)
