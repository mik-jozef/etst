import Interpretation

def Valuation.update.doubleEq
  (v: Valuation D)
  {xOuter xInner: Nat}
  (xEq: xOuter = xInner)
  (dOuter: D)
  (dInner: D)
:
  v.update xOuter dOuter
    =
  (v.update xInner dInner).update xOuter dOuter
:=
  funext fun xF => by
    unfold Valuation.update; exact
      if hF: xF = xOuter then
        by rw [
          if_pos hF,
          if_pos hF,
        ]
      else
        by rw [
          if_neg hF,
          if_neg hF,
          if_neg (xEq ▸ hF),
        ]

def Valuation.update.swapEq
  (v: Valuation D)
  (neq: xA ≠ xB)
  (dA dB: D)
:
  (v.update xA dA).update xB dB = (v.update xB dB).update xA dA
:=
  funext fun xF => by
    unfold Valuation.update; exact
      if hF: xF = xA then
        by rw [
          if_pos hF,
          if_pos hF,
          if_neg (hF ▸ neq),
        ]
      else
        by rw [
          if_neg hF,
          if_neg hF,
        ]

def Expr.IsFreeVar.toSmallerBounds
  -- Sadly has to be explicit for structural recursion
  -- to pick up the right expr in case of complements.
  (expr: Expr sig)
  (isFreeVar: expr.IsFreeVar boundVarsLarge x)
  (boundVarsLe: boundVarsSmall ≤ boundVarsLarge)
:
  expr.IsFreeVar boundVarsSmall x
:=
  let updatedBoundsLe _ _ xIn :=
    xIn.elim
      (fun inSmall => Or.inl (boundVarsLe inSmall))
      (fun eq => Or.inr eq)
  
  match expr with
  | var _ =>
    And.intro
      isFreeVar.left
      (fun inBoundsSmall =>
        isFreeVar.right (boundVarsLe inBoundsSmall))
  | op _ _ =>
    let fv := isFreeVar.unwrap
    ⟨fv, toSmallerBounds _ fv.property boundVarsLe⟩
  | un _ _ =>
    isFreeVar.elim
      (fun inL => Or.inl (toSmallerBounds _ inL boundVarsLe))
      (fun inR => Or.inr (toSmallerBounds _ inR boundVarsLe))
  | ir _ _ =>
    isFreeVar.elim
      (fun inL => Or.inl (toSmallerBounds _ inL boundVarsLe))
      (fun inR => Or.inr (toSmallerBounds _ inR boundVarsLe))
  | cpl expr =>
    -- This ought to make isFreeVar structurally smaller,
    -- but on its own it does not.
    let tmp: IsFreeVar expr boundVarsLarge x := isFreeVar
    toSmallerBounds expr tmp boundVarsLe
  | ifThen _ _ =>
    isFreeVar.elim
      (fun inL => Or.inl (toSmallerBounds _ inL boundVarsLe))
      (fun inR => Or.inr (toSmallerBounds _ inR boundVarsLe))
  | Un xUn body =>
    toSmallerBounds body isFreeVar (updatedBoundsLe xUn)
  | Ir xUn body =>
    toSmallerBounds body isFreeVar (updatedBoundsLe xUn)

def Expr.IsFreeVar.boundNotFree
  (expr: Expr sig)
  (boundVars: Set Nat)
  (isBound: x ∈ boundVars)
:
  ¬expr.IsFreeVar boundVars x
:=
  let boundVarsUpdated xUn: Set Nat :=
    fun x => x ∈ boundVars ∨ x = xUn
  
  fun isFreeVar =>
    match expr with
    | var _ =>
      isFreeVar.right (isFreeVar.left ▸ isBound)
    | op _ _ =>
      let arg := isFreeVar.unwrap
      (boundNotFree _ _ isBound) arg.property
    | un _ _ =>
      isFreeVar.elim
        (boundNotFree _ _ isBound)
        (boundNotFree _ _ isBound)
    | ir _ _ =>
      isFreeVar.elim
        (boundNotFree _ _ isBound)
        (boundNotFree _ _ isBound)
    | cpl expr =>
      boundNotFree expr _ isBound isFreeVar
    | ifThen _ _ =>
      isFreeVar.elim
        (boundNotFree _ _ isBound)
        (boundNotFree _ _ isBound)
    | Un xUn body =>
      boundNotFree body (boundVarsUpdated xUn) (Or.inl isBound) isFreeVar
    | Ir xUn body =>
      boundNotFree body (boundVarsUpdated xUn) (Or.inl isBound) isFreeVar

def NotFreePointed
  (expr: Expr sig)
  (boundVars: Set Nat)
  (xBound x: Nat)
:
  Prop
:=
  ¬expr.IsFreeVar (fun xB => xB ∈ boundVars ∨ xB = xBound) x

def Expr.IsFreeVar.removeBound
  -- Sadly has to be explicit for structural recursion
  -- to pick up the right expr in case of complements.
  (expr: Expr sig)
  (notFree: NotFreePointed expr boundVars xOut x)
:
  Or
    (¬expr.IsFreeVar boundVars x)
    (x = xOut)
:=
  match expr with
  | var _ =>
    notFree.toOr.elim
      (fun xvNeq =>
        Or.inl
          (fun vIsFree => xvNeq vIsFree.left))
      (fun vInNotNot =>
        vInNotNot.dne.elim
          (fun isBound =>
            Or.inl (fun isFree => isFree.right isBound))
          (fun eqVXOut =>
            if h: x = xOut then
              Or.inr h
            else
              Or.inl
                (fun isFreeV =>
                  h (isFreeV.left.trans eqVXOut))))
  | op _ _ =>
    if h: x = xOut then
      Or.inr h
    else
      let allParamsNotFree := notFree.toAll
        (fun _ paramNotFree =>
          (removeBound _ paramNotFree).elim
            id
            (fun eq => False.elim (h eq)))
      Or.inl (all.notEx allParamsNotFree (fun _ => id))
  | un _ _ =>
    let ⟨notFreeLeft, notFreeRite⟩ := notFree.toAnd
    (removeBound _ notFreeLeft).elim
      (fun freeLeft =>
        (removeBound _ notFreeRite).elim
          (fun freeRite =>
            Or.inl (And.intro freeLeft freeRite).toNor)
          (fun eq => Or.inr eq))
      (fun eq => Or.inr eq)
  | ir _ _ =>
    let ⟨notFreeLeft, notFreeRite⟩ := notFree.toAnd
    (removeBound _ notFreeLeft).elim
      (fun freeLeft =>
        (removeBound _ notFreeRite).elim
          (fun freeRite =>
            Or.inl (And.intro freeLeft freeRite).toNor)
          (fun eq => Or.inr eq))
      (fun eq => Or.inr eq)
  | cpl exprInside =>
    let exprNotFree:
      NotFreePointed exprInside boundVars xOut x
    :=
      notFree
    removeBound exprInside exprNotFree
  | ifThen _ _ =>
    let ⟨notFreeLeft, notFreeRite⟩ := notFree.toAnd
    (removeBound _ notFreeLeft).elim
      (fun freeLeft =>
        (removeBound _ notFreeRite).elim
          (fun freeRite =>
            Or.inl (And.intro freeLeft freeRite).toNor)
          (fun eq => Or.inr eq))
      (fun eq => Or.inr eq)
  | Un xUn body =>
    (removeBound body notFree).elim
      (fun notFreeBodyXOut =>
        (removeBound body notFreeBodyXOut).elim
          (fun notFreeBody =>
            Or.inl
              fun isFree =>
                notFreeBody
                  (toSmallerBounds _ isFree fun _ inB => Or.inl inB))
          (fun eqOut => Or.inr eqOut))
        (fun eqUn =>
          let boundVarsUpdated: Set Nat :=
            fun x => x ∈ boundVars ∨ x = xUn
          Or.inl
            fun isFree =>
              boundNotFree
                _
                boundVarsUpdated (Or.inr eqUn) isFree)
  | Ir xUn body =>
    (removeBound body notFree).elim
      (fun notFreeBodyXOut =>
        (removeBound body notFreeBodyXOut).elim
          (fun notFreeBody =>
            Or.inl
              fun isFree =>
                notFreeBody
                  (toSmallerBounds _ isFree fun _ inB => Or.inl inB))
          (fun eqOut => Or.inr eqOut))
        (fun eqUn =>
          let boundVarsUpdated: Set Nat :=
            fun x => x ∈ boundVars ∨ x = xUn
          Or.inl
            fun isFree =>
              boundNotFree
                _
                boundVarsUpdated (Or.inr eqUn) isFree)

-- Proves we can update the value of an unused
-- variable without changing the interpretation
-- of an expression.
def Expr.interpretation.eqSwappedUnused
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (expr: Expr sig)
  (xNotFree: ¬expr.IsFreeVar Set.empty x)
  (d: salg.D)
:
  expr.interpretation salg b c
    =
  expr.interpretation salg (b.update x d) (c.update x d)
:=
  match expr with
  | var a =>
    let neq: a ≠ x :=
      xNotFree.toOr.elim
        (fun neq eq => neq eq.symm)
        fun nope => nope.dne.elim
    by
      unfold Expr.interpretation Valuation.update;
      rw [if_neg neq]
  | op opr args =>
    let argsI arg := interpretation salg b c (args arg)
    let argsIUpdated arg :=
      interpretation salg (b.update x d) (c.update x d) (args arg)
    
    let nFree arg:
      ¬IsFreeVar (args arg) Set.empty x
    :=
      xNotFree.toAll (fun _ => id) arg
    
    let argsEq: argsI = argsIUpdated :=
      funext fun arg =>
        Expr.interpretation.eqSwappedUnused salg b c (args arg) (nFree arg) d
    
    Set3.eq (
      let argsIDef arg := (argsI arg).defMem
      let argsIDefUpdated arg := (argsIUpdated arg).defMem
      
      let defEq: argsIDef = argsIDefUpdated :=
        let defEqArg arg:
          (argsI arg).defMem = argsIDefUpdated arg
        :=
          congr rfl (congr argsEq rfl)
        funext defEqArg
      
      show
        Salgebra.I salg opr argsIDef
          =
        Salgebra.I salg opr argsIDefUpdated
      from
        congr rfl defEq
    ) (
      let argsIPos arg := (argsI arg).posMem
      let argsIPosUpdated arg := (argsIUpdated arg).posMem
      
      let posEq: argsIPos = argsIPosUpdated :=
        let posEqArg arg:
          (argsI arg).posMem = argsIPosUpdated arg
        :=
          congr rfl (congr argsEq rfl)
        funext posEqArg
      
      show
        Salgebra.I salg opr argsIPos
          =
        Salgebra.I salg opr argsIPosUpdated
      from
        congr rfl posEq
    )
  | un left rite =>
    let ⟨notFreeL, notFreeR⟩ := xNotFree.toAnd
    let eqLeftI := Expr.interpretation.eqSwappedUnused salg b c left notFreeL d
    let eqRiteI := Expr.interpretation.eqSwappedUnused salg b c rite notFreeR d
    
    Set3.eq (
      show
        (left.interpretation salg b c).defMem ∪
          (rite.interpretation salg b c).defMem
          =
        (left.interpretation salg (b.update x d) (c.update x d)).defMem ∪
          (rite.interpretation salg (b.update x d) (c.update x d)).defMem
      from
          eqLeftI ▸ eqRiteI ▸ rfl
    ) (
      show
        (left.interpretation salg b c).posMem ∪
          (rite.interpretation salg b c).posMem
          =
        (left.interpretation salg (b.update x d) (c.update x d)).posMem ∪
          (rite.interpretation salg (b.update x d) (c.update x d)).posMem
      from
        eqLeftI ▸ eqRiteI ▸ rfl
    )
  | ir left rite =>
    let ⟨notFreeL, notFreeR⟩ := xNotFree.toAnd
    let eqLeftI := Expr.interpretation.eqSwappedUnused salg b c left notFreeL d
    let eqRiteI := Expr.interpretation.eqSwappedUnused salg b c rite notFreeR d
    
    Set3.eq (
      show
        (left.interpretation salg b c).defMem ∩
          (rite.interpretation salg b c).defMem
          =
        (left.interpretation salg (b.update x d) (c.update x d)).defMem ∩
          (rite.interpretation salg (b.update x d) (c.update x d)).defMem
      from
          eqLeftI ▸ eqRiteI ▸ rfl
    ) (
      show
        (left.interpretation salg b c).posMem ∩
          (rite.interpretation salg b c).posMem
          =
        (left.interpretation salg (b.update x d) (c.update x d)).posMem ∩
          (rite.interpretation salg (b.update x d) (c.update x d)).posMem
      from
        eqLeftI ▸ eqRiteI ▸ rfl
    )
  | cpl expr =>
    let eqExprI := Expr.interpretation.eqSwappedUnused salg b b expr xNotFree d
    
    Set3.eq (
      show
        (expr.interpretation salg b b).posMemᶜ
          =
        (expr.interpretation salg (b.update x d) (b.update x d)).posMemᶜ
      from
          eqExprI ▸ rfl
    ) (
      show
        (expr.interpretation salg b b).defMemᶜ
          =
        (expr.interpretation salg (b.update x d) (b.update x d)).defMemᶜ
      from
        eqExprI ▸ rfl
    )
  | ifThen cond expr =>
    let condI := interpretation salg b c cond
    let condIUpdated :=
      interpretation salg (b.update x d) (c.update x d) cond
    
    let exprI := interpretation salg b c expr
    let exprIUpdated :=
      interpretation salg (b.update x d) (c.update x d) expr
    
    let ⟨notFreecond, notFreeExpr⟩ := xNotFree.toAnd
    
    let eqCondI: condI = condIUpdated :=
      Expr.interpretation.eqSwappedUnused salg b c cond notFreecond d
    let eqExprI: exprI = exprIUpdated :=
      Expr.interpretation.eqSwappedUnused salg b c expr notFreeExpr d
    
    Set3.eq (
      show
        (fun d => (∃ dC, dC ∈ condI.defMem) ∧ d ∈ exprI.defMem)
          =
        fun d => (∃ dC, dC ∈ condIUpdated.defMem) ∧ d ∈ exprIUpdated.defMem
      from
        eqCondI ▸ eqExprI ▸ rfl
    ) (
      show
        (fun d => (∃ dC, dC ∈ condI.posMem) ∧ d ∈ exprI.posMem)
          =
        fun d => (∃ dC, dC ∈ condIUpdated.posMem) ∧ d ∈ exprIUpdated.posMem
      from
        eqCondI ▸ eqExprI ▸ rfl
    )
  | Un xUn body =>
    let bodyI (dX: salg.D) :=
      interpretation salg (b.update xUn dX) (c.update xUn dX) body
    
    let bodyIUpdated (dX: salg.D) :=
      interpretation
        salg
        ((b.update x d).update xUn dX)
        ((c.update x d).update xUn dX)
        body
    
    let nFreeOrXUn:
      ¬IsFreeVar body Set.empty x ∨ x = xUn
    :=
      Expr.IsFreeVar.removeBound _ xNotFree
    
    Set3.eq (
      show
        (fun d => ∃ dX, d ∈ (bodyI dX).defMem)
          =
        (fun d => ∃ dX, d ∈ (bodyIUpdated dX).defMem)
      from
        if xEq: x = xUn then
          let bodyEq:
            (fun dX => interpretation salg (b.update xUn dX) (c.update xUn dX) body)
              =
            bodyIUpdated
          :=
            funext fun dX =>
              let bEq := Valuation.update.doubleEq b xEq.symm dX d
              let cEq := Valuation.update.doubleEq c xEq.symm dX d
              
              bEq ▸ cEq ▸ rfl
          bodyEq ▸ rfl
        else
          nFreeOrXUn.elim
            (fun nFreeInBody =>
              let eq:
                bodyI
                  =
                (fun dX =>
                  interpretation
                    salg
                    ((b.update x d).update xUn dX)
                    ((c.update x d).update xUn dX)
                    body)
              :=
                funext fun dX =>
                  let bEq :=
                    Valuation.update.swapEq b xEq d dX
                  let cEq :=
                    Valuation.update.swapEq c xEq d dX
                  
                  bEq ▸ cEq ▸ Expr.interpretation.eqSwappedUnused salg
                    (b.update xUn dX) (c.update xUn dX)
                    body nFreeInBody d
              eq ▸ rfl)
            (fun eq => False.elim (xEq eq))
    ) (
      show
        (fun d => ∃ dX, d ∈ (bodyI dX).posMem)
          =
        (fun d => ∃ dX, d ∈ (bodyIUpdated dX).posMem)
      from
        if xEq: x = xUn then
          let bodyEq:
            (fun dX => interpretation salg (b.update xUn dX) (c.update xUn dX) body)
              =
            bodyIUpdated
          :=
            funext fun dX =>
              let bEq := Valuation.update.doubleEq b xEq.symm dX d
              let cEq := Valuation.update.doubleEq c xEq.symm dX d
              
              bEq ▸ cEq ▸ rfl
          bodyEq ▸ rfl
        else
          nFreeOrXUn.elim
            (fun nFreeInBody =>
              let eq:
                bodyI
                  =
                (fun dX =>
                  interpretation
                    salg
                    ((b.update x d).update xUn dX)
                    ((c.update x d).update xUn dX)
                    body)
              :=
                funext fun dX =>
                  let bEq :=
                    Valuation.update.swapEq b xEq d dX
                  let cEq :=
                    Valuation.update.swapEq c xEq d dX
                  
                  bEq ▸ cEq ▸ Expr.interpretation.eqSwappedUnused salg
                    (b.update xUn dX) (c.update xUn dX)
                    body nFreeInBody d
              eq ▸ rfl)
            (fun eq => False.elim (xEq eq))
    )
  | Ir xUn body =>
    let bodyI (dX: salg.D) :=
      interpretation salg (b.update xUn dX) (c.update xUn dX) body
    
    let bodyIUpdated (dX: salg.D) :=
      interpretation
        salg
        ((b.update x d).update xUn dX)
        ((c.update x d).update xUn dX)
        body
    
    let nFreeOrXUn:
      ¬IsFreeVar body Set.empty x ∨ x = xUn
    :=
      Expr.IsFreeVar.removeBound _ xNotFree
    
    Set3.eq (
      show
        (fun d => ∀ dX, d ∈ (bodyI dX).defMem)
          =
        (fun d => ∀ dX, d ∈ (bodyIUpdated dX).defMem)
      from
        if xEq: x = xUn then
          let bodyEq:
            (fun dX => interpretation salg (b.update xUn dX) (c.update xUn dX) body)
              =
            bodyIUpdated
          :=
            funext fun dX =>
              let bEq := Valuation.update.doubleEq b xEq.symm dX d
              let cEq := Valuation.update.doubleEq c xEq.symm dX d
              
              bEq ▸ cEq ▸ rfl
          bodyEq ▸ rfl
        else
          nFreeOrXUn.elim
            (fun nFreeInBody =>
              let eq:
                bodyI
                  =
                (fun dX =>
                  interpretation
                    salg
                    ((b.update x d).update xUn dX)
                    ((c.update x d).update xUn dX)
                    body)
              :=
                funext fun dX =>
                  let bEq :=
                    Valuation.update.swapEq b xEq d dX
                  let cEq :=
                    Valuation.update.swapEq c xEq d dX
                  
                  bEq ▸ cEq ▸ Expr.interpretation.eqSwappedUnused salg
                    (b.update xUn dX) (c.update xUn dX)
                    body nFreeInBody d
              eq ▸ rfl)
            (fun eq => False.elim (xEq eq))
    ) (
      show
        (fun d => ∀ dX, d ∈ (bodyI dX).posMem)
          =
        (fun d => ∀ dX, d ∈ (bodyIUpdated dX).posMem)
      from
        if xEq: x = xUn then
          let bodyEq:
            (fun dX => interpretation salg (b.update xUn dX) (c.update xUn dX) body)
              =
            bodyIUpdated
          :=
            funext fun dX =>
              let bEq := Valuation.update.doubleEq b xEq.symm dX d
              let cEq := Valuation.update.doubleEq c xEq.symm dX d
              
              bEq ▸ cEq ▸ rfl
          bodyEq ▸ rfl
        else
          nFreeOrXUn.elim
            (fun nFreeInBody =>
              let eq:
                bodyI
                  =
                (fun dX =>
                  interpretation
                    salg
                    ((b.update x d).update xUn dX)
                    ((c.update x d).update xUn dX)
                    body)
              :=
                funext fun dX =>
                  let bEq :=
                    Valuation.update.swapEq b xEq d dX
                  let cEq :=
                    Valuation.update.swapEq c xEq d dX
                  
                  bEq ▸ cEq ▸ Expr.interpretation.eqSwappedUnused salg
                    (b.update xUn dX) (c.update xUn dX)
                    body nFreeInBody d
              eq ▸ rfl)
            (fun eq => False.elim (xEq eq))
    )
