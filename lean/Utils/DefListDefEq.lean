/-
  Proves that structurally identical definitions define the same
  (three-valued) sets.
-/

import Utils.Interpretation
import Utils.Operators
import WFC.Ch4_Operators


/-
  In an expression, replaces every
  - variable `var x` with `var (varMapping x)`, and
  - quantifier `Un/Ir x ...` with `Un/Ir (varMapping x) ...`.
  
  Mapping bound variables is intentional -- this way we
  don't need to track whether a variable is bound or free.
  
  If I ever need to map only the free variables, I can create
  `Expr.mapFreeVars` and use it instead.
-/
def Expr.mapVars
  (varMapping: Nat → Nat)
:
  Expr sig
→
  Expr sig

| var x => Expr.var (varMapping x)

| op opr args =>
  op opr (fun arg => (args arg).mapVars varMapping)

| un left rite =>
  un (left.mapVars varMapping) (rite.mapVars varMapping)

| ir left rite =>
  ir (left.mapVars varMapping) (rite.mapVars varMapping)

| cpl expr => cpl (expr.mapVars varMapping)

| ifThen cond body =>
  ifThen (cond.mapVars varMapping) (body.mapVars varMapping)

| Un x body =>
  Un (varMapping x) (body.mapVars varMapping)

| Ir x body =>
  Ir (varMapping x) (body.mapVars varMapping)

def Expr.mapVars.eqOfId
  (expr: Expr sig)
:
  expr.mapVars id = expr
:=
  match expr with
  | Expr.var _ => rfl
  | Expr.op _ args =>
    congr rfl (funext fun arg => eqOfId (args arg))
  | Expr.un left rite =>
    congrBin rfl (eqOfId left) (eqOfId rite)
  | Expr.ir left rite =>
    congrBin rfl (eqOfId left) (eqOfId rite)
  | Expr.cpl expr =>
    @congr _ _ cpl cpl _ _ rfl (eqOfId expr)
  | Expr.ifThen cond body =>
    congrBin rfl (eqOfId cond) (eqOfId body)
  | Expr.Un _ body =>
    congrBin rfl rfl (eqOfId body)
  | Expr.Ir _ body =>
    congrBin rfl rfl (eqOfId body)

def Expr.mapVars.eqOfIsId
  (expr: Expr sig)
  (varMapping: Nat → Nat)
  (isId: ∀ x, varMapping x = x)
:
  expr.mapVars varMapping = expr
:=
  let eqId: varMapping = id := funext isId
  eqId ▸ eqOfId expr

def Expr.mapVars.eqOfIsComposition
  (expr: Expr sig)
  (varMapping mapping1 mapping0: Nat → Nat)
  (eqMapping:
    ∀ x, varMapping x = mapping1 (mapping0 x))
:
  expr.mapVars varMapping
    =
  (expr.mapVars mapping0).mapVars mapping1
:=
  match expr with
  | Expr.var x =>
    show _ = var (mapping1 (mapping0 x)) from
      eqMapping x ▸ rfl
  | Expr.op opr args =>
    show
      _
        =
      op opr (fun arg => ((args arg).mapVars mapping0).mapVars mapping1)
    from
      congr
        rfl
        (funext fun arg =>
          eqOfIsComposition
            (args arg)
            varMapping
            mapping1
            mapping0
            eqMapping)
  | Expr.un left rite =>
    show
      un (left.mapVars varMapping) (rite.mapVars varMapping) = _
    from
      congrBin
        rfl
        (eqOfIsComposition left varMapping mapping1 mapping0 eqMapping)
        (eqOfIsComposition rite varMapping mapping1 mapping0 eqMapping)
  | Expr.ir left rite =>
    show
      ir (left.mapVars varMapping) (rite.mapVars varMapping) = _
    from
      congrBin
        rfl
        (eqOfIsComposition left varMapping mapping1 mapping0 eqMapping)
        (eqOfIsComposition rite varMapping mapping1 mapping0 eqMapping)
  | Expr.cpl expr =>
    show
      cpl (expr.mapVars varMapping) = _
    from
      @congr _ _ cpl cpl _ _ rfl
        (eqOfIsComposition expr varMapping mapping1 mapping0 eqMapping)
  | Expr.ifThen cond body =>
    show
      ifThen (cond.mapVars varMapping) (body.mapVars varMapping) = _
    from
      congrBin
        rfl
        (eqOfIsComposition cond varMapping mapping1 mapping0 eqMapping)
        (eqOfIsComposition body varMapping mapping1 mapping0 eqMapping)
  | Expr.Un x body =>
    show
      Un (varMapping x) (body.mapVars varMapping) = _
    from
      congrBin
        rfl
        (eqMapping x)
        (eqOfIsComposition body varMapping mapping1 mapping0 eqMapping)
  | Expr.Ir x body =>
    show
      Ir (varMapping x) (body.mapVars varMapping) = _
    from
      congrBin
        rfl
        (eqMapping x)
        (eqOfIsComposition body varMapping mapping1 mapping0 eqMapping)
      

/-
  Assuming that we have
  - an injective mapping `varMapping` of variables,
  - expressions `exprSrc` and `exprDst` such that
    `exprDst` is the mapped version of `exprSrc`,
  - and two pairs of background and context valuations
    that "respect that mapping" (ie. for every free
    variable `x` of `exprSrc`,
    `srcVal x = dstVal (varMapping x)`)
  
  we prove that the interpretations of `exprSrc` and
  `exprDst` under the corresponding valuations are equal.
-/
def Expr.mapVars.preservesInterpretation
  (salg: Salgebra sig)
  (exprSrc exprDst: Expr sig)
  (bSrc bDst cSrc cDst: Valuation salg.D)
  (varMapping: Nat → Nat)
  (mappingIsInjective:
    ∀ {x y}, varMapping x = varMapping y → x = y)
  (eqExprDst:
      exprSrc.mapVars varMapping = exprDst)
  (eqB:
    ∀ (x: exprSrc.IsFreeVar Set.empty),
      bSrc x = bDst (varMapping x))
  (eqC:
    ∀ (x: exprSrc.IsFreeVar Set.empty),
      cSrc x = cDst (varMapping x))
:
  exprSrc.interpretation salg bSrc cSrc
    =
  exprDst.interpretation salg bDst cDst
:=
  let eqVUpdated
    (vSrc vDst: Valuation salg.D)
    (x: Nat)
    (body: Expr sig)
    (eqV:
      ∀ (x: body.IsFreeVar (fun xE => Set.empty xE ∨ xE = x)),
        vSrc x = vDst (varMapping x))
    d
  :
    ∀ (xf: body.IsFreeVar Set.empty),
      vSrc.update x d xf = vDst.update (varMapping x) d (varMapping xf)
  :=
    fun ⟨xf, isFree⟩ =>
      let isFreeUnOrBound := IsFreeVar.arbUn x isFree
      
      isFreeUnOrBound.elim
        (fun isFreeUn =>
          if h: x = xf then
            IsFreeVar.nopeFreeInUn (h ▸ isFreeUn)
          else
            let neqMapped:
              varMapping x ≠ varMapping xf
            :=
              fun eq => h (mappingIsInjective eq)
            
            let eqMid := eqV ⟨xf, isFreeUn⟩
            let eqL := Valuation.update.eqOrig vSrc h d
            let eqR := Valuation.update.eqOrig vDst neqMapped d
            
            eqL ▸ eqR ▸ eqMid)
        (fun eq =>
          let eqMapped: varMapping x = varMapping xf :=
            congr rfl eq.symm
          
          let eqL := Valuation.update.eqBoundOfEq vSrc eq.symm d
          let eqR := Valuation.update.eqBoundOfEq vDst eqMapped d
          
          eqL ▸ eqR ▸ rfl)
  
  eqExprDst ▸
  match exprSrc with
  | Expr.var x => eqC ⟨x, IsFreeVar.varEmptyBound x⟩
  
  | Expr.op opr args =>
    let eqArg arg :=
      preservesInterpretation
        salg
        (args arg)
        ((args arg).mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ => eqB ⟨xf, ⟨arg, isFree⟩⟩)
        (fun ⟨xf, isFree⟩ => eqC ⟨xf, ⟨arg, isFree⟩⟩)
    
    Set3.eq
      ((interpretation.opEqDef salg bSrc cSrc opr args).trans
        (congr rfl (funext fun arg => eqArg arg ▸ rfl)))
      ((interpretation.opEqPos salg bSrc cSrc opr args).trans
        (congr rfl (funext fun arg => eqArg arg ▸ rfl)))
  
  | Expr.un left rite =>
    let eqL :=
      preservesInterpretation
        salg
        left
        (left.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ => eqB ⟨xf, Or.inl isFree⟩)
        (fun ⟨xf, isFree⟩ => eqC ⟨xf, Or.inl isFree⟩)
    
    let eqR :=
      preservesInterpretation
        salg
        rite
        (rite.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ => eqB ⟨xf, Or.inr isFree⟩)
        (fun ⟨xf, isFree⟩ => eqC ⟨xf, Or.inr isFree⟩)
    
    Set3.eq
      ((interpretation.unEqDef salg bSrc cSrc left rite).trans
        (eqL ▸ eqR ▸ rfl))
      ((interpretation.unEqPos salg bSrc cSrc left rite).trans
        (eqL ▸ eqR ▸ rfl))
  
  | Expr.ir left rite =>
    let eqL :=
      preservesInterpretation
        salg
        left
        (left.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ => eqB ⟨xf, Or.inl isFree⟩)
        (fun ⟨xf, isFree⟩ => eqC ⟨xf, Or.inl isFree⟩)
    
    let eqR :=
      preservesInterpretation
        salg
        rite
        (rite.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ => eqB ⟨xf, Or.inr isFree⟩)
        (fun ⟨xf, isFree⟩ => eqC ⟨xf, Or.inr isFree⟩)
    
    Set3.eq
      ((interpretation.irEqDef salg bSrc cSrc left rite).trans
        (eqL ▸ eqR ▸ rfl))
      ((interpretation.irEqPos salg bSrc cSrc left rite).trans
        (eqL ▸ eqR ▸ rfl))
  
  | Expr.cpl expr =>
    let eqExpr :=
      preservesInterpretation
        salg
        expr
        (expr.mapVars varMapping)
        bSrc
        bDst
        bSrc
        bDst
        varMapping
        mappingIsInjective
        rfl
        eqB
        eqB
    
    Set3.eq
      ((interpretation.cplEqDef salg bSrc cSrc expr).trans
        (eqExpr ▸ rfl))
      ((interpretation.cplEqPos salg bSrc cSrc expr).trans
        (eqExpr ▸ rfl))
  
  | Expr.ifThen cond body =>
    let eqCond :=
      preservesInterpretation
        salg
        cond
        (cond.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ =>
          eqB ⟨xf, IsFreeVar.ifThenCond isFree body⟩)
        (fun ⟨xf, isFree⟩ =>
          eqC ⟨xf, IsFreeVar.ifThenCond isFree body⟩)
    
    let eqBody :=
      preservesInterpretation
        salg
        body
        (body.mapVars varMapping)
        bSrc
        bDst
        cSrc
        cDst
        varMapping
        mappingIsInjective
        rfl
        (fun ⟨xf, isFree⟩ =>
          eqB ⟨xf, IsFreeVar.ifThenBody cond isFree⟩)
        (fun ⟨xf, isFree⟩ =>
          eqC ⟨xf, IsFreeVar.ifThenBody cond isFree⟩)
    
    Set3.eq
      ((interpretation.ifThenEqDef salg bSrc cSrc cond body).trans
        (eqCond ▸ eqBody ▸ rfl))
      ((interpretation.ifThenEqPos salg bSrc cSrc cond body).trans
        (eqCond ▸ eqBody ▸ rfl))
  
  | Expr.Un x body =>
    let eqBody d :=
      preservesInterpretation
        salg
        body
        (body.mapVars varMapping)
        (bSrc.update x d)
        (bDst.update (varMapping x) d)
        (cSrc.update x d)
        (cDst.update (varMapping x) d)
        varMapping
        mappingIsInjective
        rfl
        (eqVUpdated bSrc bDst x body eqB d)
        (eqVUpdated cSrc cDst x body eqC d)
    
    Set3.eq
      ((interpretation.arbUnEqDef salg bSrc cSrc x body).trans
        (funext fun d =>
          propext
            (exists_congr
              (fun dBound =>
                show
                  d ∈ (
                    interpretation
                      salg
                      (bSrc.update x dBound)
                      (cSrc.update x dBound)
                      body
                  ).defMem
                    ↔
                _
                from
                  eqBody dBound ▸ Iff.rfl))))
      ((interpretation.arbUnEqPos salg bSrc cSrc x body).trans
        (funext fun d =>
          propext
            (exists_congr
              (fun dBound =>
                show
                  d ∈ (
                    interpretation
                      salg
                      (bSrc.update x dBound)
                      (cSrc.update x dBound)
                      body
                  ).posMem
                    ↔
                _
                from
                  eqBody dBound ▸ Iff.rfl))))
  
  | Expr.Ir x body =>
    let eqBody d :=
      preservesInterpretation
        salg
        body
        (body.mapVars varMapping)
        (bSrc.update x d)
        (bDst.update (varMapping x) d)
        (cSrc.update x d)
        (cDst.update (varMapping x) d)
        varMapping
        mappingIsInjective
        rfl
        (eqVUpdated bSrc bDst x body eqB d)
        (eqVUpdated cSrc cDst x body eqC d)
    
    Set3.eq
      ((interpretation.arbIrEqDef salg bSrc cSrc x body).trans
        (funext fun d =>
          propext
            (forall_congr'
              (fun dBound =>
                show
                  d ∈ (
                    interpretation
                      salg
                      (bSrc.update x dBound)
                      (cSrc.update x dBound)
                      body
                  ).defMem
                    ↔
                _
                from
                  eqBody dBound ▸ Iff.rfl))))
      ((interpretation.arbIrEqPos salg bSrc cSrc x body).trans
        (funext fun d =>
          propext
            (forall_congr'
              (fun dBound =>
                show
                  d ∈ (
                    interpretation
                      salg
                      (bSrc.update x dBound)
                      (cSrc.update x dBound)
                      body
                  ).posMem
                    ↔
                _
                from
                  eqBody dBound ▸ Iff.rfl))))


def DefList.eqDefsToEqSets.Invariant
  (salg: Salgebra sig)
  (varMapping: Nat → Nat)
  (s: Set Nat)
  (stageSrc stageDst: Valuation salg.D)
:
  Prop
:=
  ∀ x: s, stageSrc x = stageDst (varMapping x)

def DefList.eqDefsToEqSets.InvariantB
  (salg: Salgebra sig)
  (dlSrc dlDst: DefList sig)
  (varMapping: Nat → Nat)
  (s: Set Nat)
  (n: Ordinal)
:
  Prop
:=
  Invariant
    salg
    varMapping
    s
    (operatorB.stage salg dlSrc n)
    (operatorB.stage salg dlDst n)

def DefList.eqDefsToEqSets.limitCaseB
  {varMapping: Nat → Nat}
  {n: Ordinal}
  (nIsLim: n.IsActualLimit)
  (ih: ∀ nn < n, eqDefsToEqSets.InvariantB salg dlSrc dlDst varMapping IsDefMapped nn)
  (isSrcMapped: IsDefMapped xSrc)
:
  operatorB.stage salg dlSrc n xSrc
    =
  operatorB.stage salg dlDst n (varMapping xSrc)
:=
  let setOrdApx := Set3.ord.approximation salg.D
  
  let xDst := varMapping xSrc
  
  let isSupSrc :=
    operatorB.stage.limit salg dlSrc nIsLim
  
  let isSupDst :=
    operatorB.stage.limit salg dlDst nIsLim
  
  let inPrevSrc :=
    fun v => v ∈ operatorB.stage.previous salg dlSrc n
  
  let inPrevDst :=
    fun v => v ∈ operatorB.stage.previous salg dlDst n
  
  let pwAtSrc := Set.pointwiseAt inPrevSrc xSrc
  let pwAtDst := Set.pointwiseAt inPrevDst (xDst)
  
  let supAtSrc: Supremum setOrdApx pwAtSrc :=
    Set.pointwiseSup.supAt ⟨_, isSupSrc⟩ xSrc
  
  let supAtDst: Supremum setOrdApx pwAtDst :=
    Set.pointwiseSup.supAt ⟨_, isSupDst⟩ xDst
  
  let atEq: pwAtSrc = pwAtDst :=
    funext fun d =>
      propext (Iff.intro
        (fun inSrc =>
          let ⟨⟨val, valInPrevSrc⟩, dEq⟩ := inSrc.unwrap
          let ⟨i, valAt⟩ := valInPrevSrc.unwrap
          
          ⟨
            ⟨operatorB.stage salg dlDst i, ⟨i, rfl⟩⟩,
            dEq.trans (valAt ▸ ih i i.property ⟨xSrc, isSrcMapped⟩)
          ⟩)
        (fun inDst =>
          let ⟨⟨val, valInPrevDst⟩, dEq⟩ := inDst.unwrap
          let ⟨i, valAt⟩ := valInPrevDst.unwrap
          
          ⟨
            ⟨operatorB.stage salg dlSrc i, ⟨i, rfl⟩⟩,
            dEq.trans (valAt ▸ (ih i i.property ⟨xSrc, isSrcMapped⟩).symm)
          ⟩))
  
  IsSupremum.eq
    supAtSrc.property
    supAtDst.property
    atEq

def DefList.eqDefsToEqSets.InvariantC
  (salg: Salgebra sig)
  (dlSrc dlDst: DefList sig)
  (varMapping: Nat → Nat)
  (s: Set Nat)
  (bSrc bDst: Valuation salg.D)
  (n: Ordinal)
:
  Prop
:=
  ∀ x: s,
    operatorC.stage salg dlSrc bSrc n x
      =
    operatorC.stage salg dlDst bDst n (varMapping x)

def DefList.eqDefsToEqSets.limitCaseC
  {varMapping: Nat → Nat}
  {n: Ordinal}
  (nIsLim: n.IsActualLimit)
  (ih:
    ∀ nn < n,
      eqDefsToEqSets.InvariantC
        salg dlSrc dlDst varMapping IsDefMapped bSrc bDst nn)
  (isSrcMapped: IsDefMapped xSrc)
:
  operatorC.stage salg dlSrc bSrc n xSrc
    =
  operatorC.stage salg dlDst bDst n (varMapping xSrc)
:=
  let setOrdStd := Set3.ord.standard salg.D
  
  let xDst := varMapping xSrc
  
  let isSupSrc :=
    operatorC.stage.limit salg dlSrc bSrc nIsLim
  
  let isSupDst :=
    operatorC.stage.limit salg dlDst bDst nIsLim
  
  let inPrevSrc :=
    fun v => v ∈ operatorC.stage.previous salg dlSrc bSrc n
  
  let inPrevDst :=
    fun v => v ∈ operatorC.stage.previous salg dlDst bDst n
  
  let pwAtSrc := Set.pointwiseAt inPrevSrc xSrc
  let pwAtDst := Set.pointwiseAt inPrevDst xDst
  
  let supAtSrc: Supremum setOrdStd pwAtSrc :=
    Set.pointwiseSup.supAt ⟨_, isSupSrc⟩ xSrc
  
  let supAtDst: Supremum setOrdStd pwAtDst :=
    Set.pointwiseSup.supAt ⟨_, isSupDst⟩ xDst
  
  let atEq: pwAtSrc = pwAtDst :=
    funext fun d =>
      propext (Iff.intro
        (fun inSrc =>
          let ⟨⟨val, valInPrevSrc⟩, dEq⟩ := inSrc.unwrap
          let ⟨i, valAt⟩ := valInPrevSrc.unwrap
          
          ⟨
            ⟨operatorC.stage salg dlDst bDst i, ⟨i, rfl⟩⟩,
            dEq.trans (valAt ▸ ih i i.property ⟨xSrc, isSrcMapped⟩)
          ⟩)
        (fun inDst =>
          let ⟨⟨val, valInPrevDst⟩, dEq⟩ := inDst.unwrap
          let ⟨i, valAt⟩ := valInPrevDst.unwrap
          
          ⟨
            ⟨operatorC.stage salg dlSrc bSrc i, ⟨i, rfl⟩⟩,
            dEq.trans (valAt ▸ (ih i i.property ⟨xSrc, isSrcMapped⟩).symm)
          ⟩))
  
  IsSupremum.eq
    supAtSrc.property
    supAtDst.property
    atEq

def DefList.eqDefsToEqSets.succCaseC
  (nIsSucc: ¬ n.IsActualLimit)
  (ih:
    ∀ nn < n,
      eqDefsToEqSets.InvariantC
        salg dlSrc dlDst varMapping IsDefMapped bSrc bDst nn)
  (mappingIsInjective:
    ∀ {x y}, varMapping x = varMapping y → x = y)
  (defEq:
    (dlSrc.getDef xSrc).mapVars varMapping
      =
    dlDst.getDef (varMapping xSrc))
  (areUsedDefsMapped:
    ∀ (xUsed: (dlSrc.getDef xSrc).IsFreeVar Set.empty)
    ,
      IsDefMapped xUsed)
  (invB: Invariant salg varMapping IsDefMapped bSrc bDst)
:
  operatorC.stage salg dlSrc bSrc n xSrc
    =
  operatorC.stage salg dlDst bDst n (varMapping xSrc)
:=
  let xDst := varMapping xSrc
  
  let succPredEq :=
    Ordinal.succ_pred_of_not_limit nIsSucc
  
  let eqStage dl b:
    operatorC.stage salg dl b n
      =
    operatorC.stage salg dl b n.pred.succ
  :=
    succPredEq.symm ▸ rfl
  
  let eqL :=
    (eqStage dlSrc bSrc).trans
      (operatorC.stage.succEq salg dlSrc bSrc n.pred)
  
  let eqR :=
    (eqStage dlDst bDst).trans
      (operatorC.stage.succEq salg dlDst bDst n.pred)
  
  eqL ▸
  eqR.symm ▸
  Expr.mapVars.preservesInterpretation
    salg
    (dlSrc.getDef xSrc)
    (dlDst.getDef xDst)
    bSrc
    bDst
    (operatorC.stage salg dlSrc bSrc n.pred)
    (operatorC.stage salg dlDst bDst n.pred)
    varMapping
    mappingIsInjective
    defEq
    (fun isFree => invB ⟨_, areUsedDefsMapped isFree⟩)
    (fun isFree =>
      let predLt := Ordinal.predLtOfNotLimit nIsSucc
      
      ih _ predLt ⟨_, areUsedDefsMapped isFree⟩)

def DefList.eqDefsToEqSets.opC
  {dlSrc dlDst: DefList sig}
  {bSrc bDst: Valuation salg.D}
  (IsDefMapped: Set Nat)
  (isSrcMapped: IsDefMapped xSrc)
  (mappingIsInjective:
    ∀ {x y}, varMapping x = varMapping y → x = y)
  (areMappedDefsEqual:
    ∀ (xSrc: IsDefMapped),
      (dlSrc.getDef xSrc).mapVars varMapping
        =
      dlDst.getDef (varMapping xSrc))
  (areUsedDefsMapped:
    ∀ (xMapped: IsDefMapped)
      (xUsed: (dlSrc.getDef xMapped).IsFreeVar Set.empty)
    ,
      IsDefMapped xUsed)
  (invB: Invariant salg varMapping IsDefMapped bSrc bDst)
:
  operatorB salg dlSrc bSrc xSrc
    =
  operatorB salg dlDst bDst (varMapping xSrc)
:=
  let ⟨fp, ⟨eqSrc, eqDst⟩⟩ :=
    operatorC.fixedIndex2 salg dlSrc dlDst bSrc bDst
  
  let stagesEqualC :=
    fp.induction
      (fun n ih =>
        show
          eqDefsToEqSets.InvariantC
            salg dlSrc dlDst varMapping IsDefMapped
            bSrc bDst n
        from
          fun xMapped =>
            if h: n.IsActualLimit then
              limitCaseC h ih xMapped.property
            else
              succCaseC
                h
                ih
                mappingIsInjective
                (areMappedDefsEqual xMapped)
                (fun fv => areUsedDefsMapped _ fv)
                invB)
  
  show
    (operatorC.lfp salg dlSrc bSrc).val xSrc
      =
    (operatorC.lfp salg dlDst bDst).val (varMapping xSrc)
  from
    eqSrc ▸ eqDst ▸ stagesEqualC ⟨xSrc, isSrcMapped⟩

def DefList.eqDefsToEqSets.succCaseB
  {varMapping: Nat → Nat}
  {n: Ordinal}
  (nIsSucc: ¬ n.IsActualLimit)
  (ih:
    ∀ nn < n,
      eqDefsToEqSets.InvariantB
        salg dlSrc dlDst varMapping IsDefMapped nn)
  (mappingIsInjective:
    ∀ {x y}, varMapping x = varMapping y → x = y)
  (areMappedDefsEqual:
    ∀ (xSrc: IsDefMapped),
      (dlSrc.getDef xSrc).mapVars varMapping
        =
      dlDst.getDef (varMapping xSrc))
  (areUsedDefsMapped:
    ∀ (xMapped: IsDefMapped)
      (xUsed: (dlSrc.getDef xMapped).IsFreeVar Set.empty)
    ,
      IsDefMapped xUsed)
  (isSrcMapped: IsDefMapped xSrc)
:
  operatorB.stage salg dlSrc n xSrc
    =
  operatorB.stage salg dlDst n (varMapping xSrc)
:=
  let succPredEq :=
    Ordinal.succ_pred_of_not_limit nIsSucc
  
  let eqStage dl:
    operatorB.stage salg dl n
      =
    operatorB.stage salg dl n.pred.succ
  :=
    succPredEq.symm ▸ rfl
  
  let eqL :=
    (eqStage dlSrc).trans (operatorB.stage.succEq salg dlSrc n.pred)
  
  let eqR :=
    (eqStage dlDst).trans (operatorB.stage.succEq salg dlDst n.pred)
  
  eqL ▸
  eqR.symm ▸
  opC
    IsDefMapped
    isSrcMapped
    mappingIsInjective
    areMappedDefsEqual
    areUsedDefsMapped
    (fun xMapped =>
      ih
        n.pred
        (Ordinal.predLtOfNotLimit nIsSucc)
        xMapped)

def DefList.eqDefsToEqSets
  (dlSrc dlDst: DefList sig)
  (salg: Salgebra sig)
  (varMapping: Nat → Nat)
  (IsDefMapped: Set Nat)
  (mappingIsInjective:
    ∀ {x y}, varMapping x = varMapping y → x = y)
  (areMappedDefsEqual:
    ∀ (xSrc: IsDefMapped),
      (dlSrc.getDef xSrc).mapVars varMapping
        =
      dlDst.getDef (varMapping xSrc))
  (areUsedDefsMapped:
    ∀ (xMapped: IsDefMapped)
      (xUsed: (dlSrc.getDef xMapped).IsFreeVar Set.empty)
    ,
      IsDefMapped xUsed)
  (xSrc: Nat)
  (isSrcMapped: IsDefMapped xSrc)
:
  dlSrc.wellFoundedModel salg xSrc
    =
  dlDst.wellFoundedModel salg (varMapping xSrc)
:=
  let ⟨fp, ⟨eqSrc, eqDst⟩⟩ := operatorB.fixedIndex2 salg dlSrc dlDst
  
  let stagesEqualB :=
    fp.induction
      (fun n ih =>
        show
          eqDefsToEqSets.InvariantB
            salg dlSrc dlDst varMapping IsDefMapped n
        from
          fun xMapped =>
            if h: n.IsActualLimit then
              eqDefsToEqSets.limitCaseB h ih xMapped.property
            else
              eqDefsToEqSets.succCaseB
                h
                ih
                mappingIsInjective
                areMappedDefsEqual
                areUsedDefsMapped
                xMapped.property)
  
  show
    (operatorB.lfp salg dlSrc).val xSrc
      =
    (operatorB.lfp salg dlDst).val (varMapping xSrc)
  from
    eqSrc ▸ eqDst ▸ stagesEqualB ⟨xSrc, isSrcMapped⟩
