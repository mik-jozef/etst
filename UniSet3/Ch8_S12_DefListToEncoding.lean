-- The twelfth section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S11_GetBound


/-
  See `exprEncoding.exprList`.
-/
def Pair.exprToEncoding
  (expr: Expr pairSignature)
:
  { p // uniSet3.IsExprEncoding p }
:=
  open uniSet3.IsExprEncoding in
  open uniSet3.IsExprEncoding.Bin in
  open uniSet3.IsExprEncoding.Quantifier in
  match expr with
  | Expr.var x => ⟨
      pair zero (fromNat x),
      IsVar (fromNat.isNatEncoding _)
    ⟩
  | Expr.op pairSignature.Op.zero _ => ⟨
      pair (fromNat 1) zero,
      IsZero
    ⟩

  | Expr.op pairSignature.Op.pair args =>
    let ⟨l, isEncL⟩ := exprToEncoding (args ArityTwo.zth)
    let ⟨r, isEncR⟩ := exprToEncoding (args ArityTwo.fst)
    ⟨
      pair (fromNat 2) (pair l r),
      IsBin (Is2 rfl) isEncL isEncR
    ⟩

  | Expr.un left rite =>
    let ⟨l, isEncL⟩ := exprToEncoding left
    let ⟨r, isEncR⟩ := exprToEncoding rite
    ⟨
      pair (fromNat 3) (pair l r),
      IsBin (Is3 rfl) isEncL isEncR,
    ⟩

  | Expr.ir left rite =>
    let ⟨l, isEncL⟩ := exprToEncoding left
    let ⟨r, isEncR⟩ := exprToEncoding rite
    ⟨
      pair (fromNat 4) (pair l r),
      IsBin (Is4 rfl) isEncL isEncR,
    ⟩

  | Expr.cpl expr =>
    let ⟨e, isEncE⟩ := exprToEncoding expr
    ⟨pair (fromNat 5) e, IsCpl isEncE⟩

  | Expr.ifThen cond body =>
    let ⟨c, isEncC⟩ := exprToEncoding cond
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 6) (pair c b),
      IsBin (Is6 rfl) isEncC isEncB,
    ⟩

  | Expr.Un x body =>
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 7) (pair (fromNat x) b),
      IsQuantifier (Is7 rfl) (fromNat.isNatEncoding _) isEncB
    ⟩

  | Expr.Ir x body =>
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 8) (pair (fromNat x) b),
      IsQuantifier (Is8 rfl) (fromNat.isNatEncoding _) isEncB
    ⟩

def Pair.exprToEncoding.injEq
  (eq: exprToEncoding a = exprToEncoding b)
:
  a = b
:=
  match a, b with
  | Expr.var _, Expr.var _ =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ => congr rfl ∘ fromNat.injEq
  
  | Expr.op pairSignature.Op.zero _,
    Expr.op pairSignature.Op.zero _
  =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ _ => congr rfl (funext nofun)
  
  | Expr.op pairSignature.Op.pair _argsA,
    Expr.op pairSignature.Op.pair _argsB
  =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun zthEncEq fstEncEq =>
            let zthEq := exprToEncoding.injEq (Subtype.eq zthEncEq)
            let fstEq := exprToEncoding.injEq (Subtype.eq fstEncEq)
            congr
              rfl
              (funext fun arg =>
                match arg with
                | ArityTwo.zth => zthEq
                | ArityTwo.fst => fstEq)
  
  | Expr.un _leftA _riteA, Expr.un _leftB _riteB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun leftEq riteEq =>
            let leftEq := exprToEncoding.injEq (Subtype.eq leftEq)
            let riteEq := exprToEncoding.injEq (Subtype.eq riteEq)
            congrBin rfl leftEq riteEq
  
  | Expr.ir _leftA _riteA, Expr.ir _leftB _riteB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun leftEq riteEq =>
            let leftEq := exprToEncoding.injEq (Subtype.eq leftEq)
            let riteEq := exprToEncoding.injEq (Subtype.eq riteEq)
            congrBin rfl leftEq riteEq
  
  | Expr.cpl _exprA, Expr.cpl _exprB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        congr rfl (exprToEncoding.injEq (Subtype.eq eqP))
  
  | Expr.ifThen _condA _bodyA, Expr.ifThen _condB _bodyB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun condEq bodyEq =>
            let condEq := exprToEncoding.injEq (Subtype.eq condEq)
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl condEq bodyEq
  
  | Expr.Un _xA _bodyA, Expr.Un _xB _bodyB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun xEq bodyEq =>
            let xEq := fromNat.injEq xEq
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl xEq bodyEq
  
  | Expr.Ir _xA _bodyA, Expr.Ir _xB _bodyB =>
    Pair.noConfusion
      (Subtype.val_eq_val eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun xEq bodyEq =>
            let xEq := fromNat.injEq xEq
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl xEq bodyEq

def Pair.exprToEncoding.eqVarDepth
  (isNat: IsNatEncoding p)
:
  exprToEncoding p.depth = pair zero p
:=
  by
    conv =>
      rhs; rw [(fromNat.eqOfDepth isNat).symm];
    exact rfl


structure Pair.DefListToEncoding
  (dl: DefList pairSignature)
  (iStart: Nat)
where
  val: Pair
  isDef: uniSet3.IsDefEncoding val
  eqAt:
    ∀ i < val.arrayLength,
      val.arrayAt i = Pair.exprToEncoding (dl.getDef (iStart + i))

/-
  Encodes a section of a definition list as a pair (a list of
  encodings of expressions). Recall the empty list is encoded
  as the zero pair, and `[ head, ...tail ]` is encoded as
  
      `Pair.pair headEncoding tailEncoding` \,.
  
  The lower bound `iStart` is inclusive, while the upper bound
  `iEnd` is exclusive.
-/
def Pair.defListToEncoding
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  DefListToEncoding dl iStart
:=
  if h: iEnd ≤ iStart then
    ⟨Pair.zero, trivial, nofun⟩
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    -- Perhaps not working because of:
    -- https://github.com/leanprover/lean4/issues/1694
    -- let ⟨headEncoding, isExprHead⟩ :=
    let tmp :=
      exprToEncoding (dl.getDef iStart)
    let headEncoding := tmp.val
    let isExprHead := tmp.property
    
    let ⟨tailEncoding, isDefTail, eqAtTail⟩ :=
      defListToEncoding dl iStart.succ iEnd
    
    {
      val := Pair.pair headEncoding tailEncoding
      isDef := And.intro isExprHead isDefTail
      eqAt :=
        fun i iWithinBounds =>
          match i with
          | Nat.zero => Nat.add_zero _ ▸ rfl
          | Nat.succ iPred =>
            let iPredWithinBounds :=
              Nat.lt_of_succ_lt_succ iWithinBounds
            
            Nat.succ_add_eq_add_succ iStart iPred ▸
            arrayAt.consEq
              (eqAtTail iPred iPredWithinBounds)
              headEncoding
    }
      
termination_by iEnd - iStart

def Pair.defListToEncoding.eqIfEndLe
  (dl: DefList pairSignature)
  {iStart iEnd: Nat}
  (le: iEnd ≤ iStart)
:
  (defListToEncoding dl iStart iEnd).val = Pair.zero
:=
  by unfold defListToEncoding; rw [dif_pos le]

def Pair.defListToEncoding.eqIfStartLt
  (dl: DefList pairSignature)
  {iStart iEnd: Nat}
  (lt: iStart < iEnd)
:
  (defListToEncoding dl iStart iEnd).val
    =
  Pair.pair
    (exprToEncoding (dl.getDef iStart)).val
    (defListToEncoding dl iStart.succ iEnd).val
:=
  let notLe: ¬ iEnd ≤ iStart := Nat.not_le_of_lt lt
  
  by
    conv => lhs; unfold defListToEncoding; rfl
    exact dif_neg notLe ▸ rfl

def Pair.defListToEncoding.lengthEq
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  (defListToEncoding dl iStart iEnd).val.arrayLength = iEnd - iStart
:=
  if h: iEnd ≤ iStart then
    eqIfEndLe dl h ▸
    Nat.sub_eq_zero_of_le h ▸
    rfl
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    let natEqL :=
      Nat.succ_sub_comm_of_lt (Nat.succ_le_of_lt (Nat.lt_of_not_le h))
    
    let natEqR := Nat.succ_sub_succ_eq_sub iEnd iStart
    
    eqIfStartLt dl (Nat.lt_of_not_le h) ▸
    (arrayLength.eqSuccTail _ _).trans
      (lengthEq dl iStart.succ iEnd ▸
      (natEqL.trans natEqR))
termination_by iEnd - iStart


namespace Pair
  noncomputable def encodingToExpr
    (p: Pair)
  :
    Expr pairSignature
  :=
    if h: ∃ expr, exprToEncoding expr = p then
      h.unwrap
    else
      Expr.var 0
  
  def encodingToExpr.eqOfExists
    {p: Pair}
    (ex: ∃ expr, exprToEncoding expr = p)
  :
    encodingToExpr p = ex.unwrap
  := by
    unfold encodingToExpr
    exact dif_pos ex ▸ rfl
  
  def exprToEncoding.existsOfIsEncoding
    (isExprEnc: uniSet3.IsExprEncoding p)
  :
    ∃ expr, exprToEncoding expr = p
  :=
    open uniSet3.IsExprEncoding in
    open uniSet3.IsExprEncoding.Bin in
    open uniSet3.IsExprEncoding.Quantifier in
    open PairExpr in
    match isExprEnc with
    | IsVar isNat => ⟨
      Expr.var isNat.toNat,
      Subtype.val_eq _ _ ▸
      isNat.toNatFromNatEq.symm ▸
      rfl
    ⟩
    | IsZero => ⟨
      Expr.op pairSignature.Op.zero nofun,
      rfl
    ⟩
    | IsBin isBin isExprA isExprB =>
      let ⟨exprA, eqA⟩ := existsOfIsEncoding isExprA
      let ⟨exprB, eqB⟩ := existsOfIsEncoding isExprB
      
      match isBin with
      | Is2 eq2 => ⟨
        pairExpr exprA exprB,
        eq2 ▸ eqA ▸ eqB ▸ rfl,
      ⟩
      | Is3 eq3 => ⟨
        Expr.un exprA exprB,
        eq3 ▸ eqA ▸ eqB ▸ rfl,
      ⟩
      | Is4 eq4 => ⟨
        Expr.ir exprA exprB,
        eq4 ▸ eqA ▸ eqB ▸ rfl,
      ⟩
      | Is6 eq6 => ⟨
        Expr.ifThen exprA exprB,
        eq6 ▸ eqA ▸ eqB ▸ rfl,
      ⟩
    | IsCpl isExpr =>
      let ⟨expr, eq⟩ := existsOfIsEncoding isExpr
      ⟨Expr.cpl expr, eq ▸ rfl⟩
    | IsQuantifier isQuant isNat isExpr =>
      let ⟨expr, eq⟩ := existsOfIsEncoding isExpr
      
      match isQuant with
      | Is7 eq7 => ⟨
        Expr.Un isNat.toNat expr,
        Subtype.val_eq _ _ ▸
        isNat.toNatFromNatEq.symm ▸
        eq7 ▸ eq ▸ rfl,
      ⟩
      | Is8 eq8 => ⟨
        Expr.Ir isNat.toNat expr,
        Subtype.val_eq _ _ ▸
        isNat.toNatFromNatEq.symm ▸
        eq8 ▸ eq ▸ rfl,
      ⟩
  
  def encodingToExpr.isInverse
    (expr: Expr pairSignature)
  :
    encodingToExpr (exprToEncoding expr) = expr
  :=
    let ex := ⟨expr, rfl⟩
    let eq := encodingToExpr.eqOfExists ex
    
    eq ▸ exprToEncoding.injEq (Subtype.eq ex.unwrap.property)
  
  def encodingToExpr.injEq
    (isExprA: uniSet3.IsExprEncoding a)
    (isExprB: uniSet3.IsExprEncoding b)
    (eq: encodingToExpr a = encodingToExpr b)
  :
    a = b
  :=
    let tmpA := exprToEncoding.existsOfIsEncoding isExprA
    let exprA := tmpA.unwrap.val
    let eqA: exprToEncoding exprA = a := tmpA.unwrap.property
    
    let tmpB := exprToEncoding.existsOfIsEncoding isExprB
    let exprB := tmpB.unwrap.val
    let eqB: exprToEncoding exprB = b := tmpB.unwrap.property
    
    let encEqA: a.encodingToExpr = exprA :=
      eqOfExists ⟨exprA, eqA⟩
    let encEqB: b.encodingToExpr = exprB :=
      eqOfExists ⟨exprB, eqB⟩
    
    let exprEq := encEqA.symm.trans (eq.trans encEqB)
    
    eqA.symm.trans (exprEq ▸ eqB)
  
  def exprToEncoding.isInverse
    (isExpr: uniSet3.IsExprEncoding p)
  :
    exprToEncoding (encodingToExpr p) = p
  :=
    let ex := existsOfIsEncoding isExpr
    let eq := encodingToExpr.eqOfExists ex
    
    eq ▸ ex.unwrap.property
  
  def exprToEncoding.isInverseSubtype
    (isExpr: uniSet3.IsExprEncoding p)
  :
    exprToEncoding (encodingToExpr p) = ⟨p, isExpr⟩
  :=
    Subtype.eq (isInverse isExpr)
  
  
  def encodingToExpr.toEqExprToEncoding
    (isExpr: uniSet3.IsExprEncoding exprEnc)
    (eq: exprEnc.encodingToExpr = expr)
  :
    exprEnc = exprToEncoding expr
  :=
    eq ▸ (exprToEncoding.isInverse isExpr).symm
  
  def exprToEncoding.toEqEncodingToExpr
    (expr: Expr pairSignature)
    (p: Pair)
    (eq: (exprToEncoding expr).val = p)
  :
    expr = encodingToExpr p
  :=
    eq ▸ (encodingToExpr.isInverse expr).symm
  
  
  def encodingToExpr.varEncEq
    (isNat: IsNatEncoding xEnc)
  :
    (pair zero xEnc).encodingToExpr = Expr.var xEnc.depth
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        xEnc.depth _ (exprToEncoding.eqVarDepth isNat))
  
  def encodingToExpr.zeroEncEq:
    (pair (fromNat 1) zero).encodingToExpr
      =
    PairExpr.zeroExpr
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        PairExpr.zeroExpr
        (pair (fromNat 1) zero)
        rfl)
  
  def encodingToExpr.pairEncEq
    (isExprA: uniSet3.IsExprEncoding exprA)
    (isExprB: uniSet3.IsExprEncoding exprB)
  :
    (pair (fromNat 2) (pair exprA exprB)).encodingToExpr
      =
    PairExpr.pairExpr
      (encodingToExpr exprA)
      (encodingToExpr exprB)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (PairExpr.pairExpr
          (encodingToExpr exprA)
          (encodingToExpr exprB))
        (pair (fromNat 2) (pair exprA exprB))
        (show pair (fromNat 2) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExprA]
          rw [exprToEncoding.isInverseSubtype isExprB]))
  
  def encodingToExpr.unEncEq
    (isExprA: uniSet3.IsExprEncoding exprA)
    (isExprB: uniSet3.IsExprEncoding exprB)
  :
    (pair (fromNat 3) (pair exprA exprB)).encodingToExpr
      =
    Expr.un (encodingToExpr exprA) (encodingToExpr exprB)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.un (encodingToExpr exprA) (encodingToExpr exprB))
        (pair (fromNat 3) (pair exprA exprB))
        (show pair (fromNat 3) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExprA]
          rw [exprToEncoding.isInverseSubtype isExprB]))
  
  def encodingToExpr.irEncEq
    (isExprA: uniSet3.IsExprEncoding exprA)
    (isExprB: uniSet3.IsExprEncoding exprB)
  :
    (pair (fromNat 4) (pair exprA exprB)).encodingToExpr
      =
    Expr.ir (encodingToExpr exprA) (encodingToExpr exprB)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.ir (encodingToExpr exprA) (encodingToExpr exprB))
        (pair (fromNat 4) (pair exprA exprB))
        (show pair (fromNat 4) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExprA]
          rw [exprToEncoding.isInverseSubtype isExprB]))
  
  def encodingToExpr.cplEncEq
    (isExpr: uniSet3.IsExprEncoding exprEnc)
  :
    (pair (fromNat 5) exprEnc).encodingToExpr
      =
    Expr.cpl (encodingToExpr exprEnc)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.cpl (encodingToExpr exprEnc))
        (pair (fromNat 5) exprEnc)
        (by
          unfold exprToEncoding
          rw [exprToEncoding.isInverseSubtype isExpr]))
  
  def encodingToExpr.ifThenEncEq
    (isExprA: uniSet3.IsExprEncoding exprA)
    (isExprB: uniSet3.IsExprEncoding exprB)
  :
    (pair (fromNat 6) (pair exprA exprB)).encodingToExpr
      =
    Expr.ifThen (encodingToExpr exprA) (encodingToExpr exprB)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.ifThen (encodingToExpr exprA) (encodingToExpr exprB))
        (pair (fromNat 6) (pair exprA exprB))
        (show pair (fromNat 6) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExprA]
          rw [exprToEncoding.isInverseSubtype isExprB]))
  
  def encodingToExpr.arbUnEncEq
    (isNat: IsNatEncoding xEnc)
    (isExpr: uniSet3.IsExprEncoding exprEnc)
  :
    (pair (fromNat 7) (pair xEnc exprEnc)).encodingToExpr
      =
    Expr.Un xEnc.depth (encodingToExpr exprEnc)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.Un xEnc.depth (encodingToExpr exprEnc))
        (pair (fromNat 7) (pair xEnc exprEnc))
        (show pair (fromNat 7) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExpr]
          rw [fromNat.eqOfDepth isNat]))
  
  def encodingToExpr.arbIrEncEq
    (isNat: IsNatEncoding xEnc)
    (isExpr: uniSet3.IsExprEncoding exprEnc)
  :
    (pair (fromNat 8) (pair xEnc exprEnc)).encodingToExpr
      =
    Expr.Ir xEnc.depth (encodingToExpr exprEnc)
  :=
    Eq.symm
      (exprToEncoding.toEqEncodingToExpr
        (Expr.Ir xEnc.depth (encodingToExpr exprEnc))
        (pair (fromNat 8) (pair xEnc exprEnc))
        (show pair (fromNat 8) _ = _ from by
          rw [exprToEncoding.isInverseSubtype isExpr]
          rw [fromNat.eqOfDepth isNat]))
  
  
  def InterpEnc
    (boundVars: List (ValVar Pair))
    (expr: Expr pairSignature)
    (d: Pair)
  :=
    pair
      (boundVarsEncoding boundVars)
      (pair (exprToEncoding expr) d)
  
  def IsBound
    (boundVars: List (ValVar Pair))
    (x: Nat)
  :
    Prop
  :=
    ∃ d, uniSet3.IsGetBound (boundVarsEncoding boundVars) x d
  
end Pair    
