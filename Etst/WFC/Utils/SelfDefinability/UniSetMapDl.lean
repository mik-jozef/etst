import Etst.WFC.Syntax.FiniteDefList

namespace Etst
open SingleLaneExpr


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

def uniSetMapAt
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  Set3 Pair
:=
  uniSetMap.pairCallJust (uniSetMapIndex dl n fv expr)

def uniSetMapIndexDef
  (dl: DefList)
  (n: Nat)
  (x: Nat)
:=
  uniSetMapIndex dl n [] ((dl.prefix n).getDef x)


namespace uniSetMapDl
  def getNth {list fv x lane}
    (lt: x < list.length)
  :
    intp
      (const lane consts.getNth)
      fv
      uniSetMapDl.wfm
      (.pair (.listEncoding list) (.pair (.nat x) list[x]))
  :=
    match list with
    | listH :: listT =>
      let ins :=
        match x with
        | 0 => inUnL (inPair (inPair rfl rfl) (inPair (inNat 0) rfl))
        | xPred + 1 =>
          let ih := getNth (Nat.lt_of_succ_lt_succ lt)
          inUnR
            (inArbUn
              xPred
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
  
  def getNthEnc
    (dl: DefList)
    (n x: Nat)
  :
    Pair
  :=
    .pair
      (dl.prefixEncoding n)
      (.pair (.nat x) ((dl.prefix n).getDef x).encoding)
  
  def getNthDl {dl n fv x lane}
    (lt: x < n)
  :
    (const lane consts.getNth).intp
      fv
      uniSetMapDl.wfm
      (getNthEnc dl n x)
  := by
    let lt := (dl.prefixList_length_eq 0 n).symm ▸ lt
    unfold getNthEnc
    rw [←dl.prefixList_at_eq n x]
    rw [(List.getElem?_eq_some_getElem_iff lt).mpr trivial]
    exact getNth (x:=x) lt
  
  def getNthElim {list i valEnc lane}
    (inGetDef:
      intp
        (const lane consts.getNth)
        []
        uniSetMapDl.wfm
        (.pair (.listEncoding list) (.pair (.nat i) valEnc)))
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
  
  def getNthElimD {list i valEnc lane df}
    (inGetDef:
      intp
        (const lane consts.getNth)
        []
        uniSetMapDl.wfm
        (.pair (.listEncoding list) (.pair (.nat i) valEnc)))
  :
    list[i]?.getD df = valEnc
  :=
    getNthElim inGetDef ▸ rfl
end uniSetMapDl
