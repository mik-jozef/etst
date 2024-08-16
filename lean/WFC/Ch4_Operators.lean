/-
  # Chapter 4: Operators B and C, and the well-founded model
  
  A word of warning: this description makes simplifications and
  is a little inaccurate/incomplete here and there. It is meant
  to give an intuitive understanding of the formal machinery.
  
  Here we define the semantics of definition lists. That is, we
  will associate every definition list `dl` with a valuation
  (called the we well-founded model of `dl`) that "agrees" with
  the definitions in `dl`.
  
  Typically, the semantics of recursive definitions is defined
  as a least fixed point of their interpretation. For example,
  take `let T = 0 | T + 2` (to borrow syntax from TypeScript).
  We can imagine the least fixed point as being built in stages,
  starting with the least element of the standard ordering, the
  empty set:
  
      T₀ = ∅
      T₁ = {0}
      T₂ = {0, 2}
      T₃ = {0, 2, 4}
      ⋮
      T  = {0, 2, 4, ...}
  
  Formally, we would define an operator P as
  
      P(s) = { 0 } ∪ { n + 2 | n ∈ s }
  
  and define the semantics of T as the least fixed point of P.
  
  > Note: the stages would be
  >
  >     T_{n+1}   = P(T_n)
  >     T_{limit} = sup { T_n | n < limit }
  >
  > and would eventually converge to the least fixed point for
  > well-behaved definitions.
  
  Our problem is that least fixed points are not guaranteed to
  exist non-monotonic operators, such as those involving complements.
  For example, consider `let Bad = ~Bad`. The stages are:
  
      Bad₀ = ∅
      Bad₁ = ℕ
      Bad₂ = ∅
      Bad₃ = ℕ
      ⋮
  
  This sequence does not converge to a fixed point. In fact, no
  classical (ie. two-valued) fixed point exists.
  
  Recall, however, that our interpretation function from Chapter 3
  takes two valuations (background and context, or `b` and `c`),
  and background is used to interpret complements. If background
  is constant, then the interpretation of complements is constant
  as well.
  
  This allows us to define a monotonic family of operators C
  indexed by the background valuation like this:
  
      C_b(c) = interpretation(b, c)
  
  Since the interpretation of complements is constant, the
  interpretation of C is monotonic (with respect to the standard
  ordering).
  
  We also define the operator B as follows:
  
      B(b) = lfp(C_b)
  
  where `lfp(X)` is the least fixed point of `X`. We can show
  that B is monotonic with respect to the approximation ordering.
  
  > Aside:
  > If you're willing to entertain the idea of algorithms that
  > terminate after potentially transfinite number of steps, then
  > you can can imagine computing the least fixed point of B as
  > executing the following algorithm:
  > 
  > ```
  >   // Valuations are initialized to the least elements in their
  >   // respective orderings.
  >   let b = the undetermined valuation;
  >   
  >   while (b has changed) {
  >     let c = the empty valuation;
  >     
  >     while (c has changed) {
  >       c = interpretation(b, c);
  >     }
  >     
  >     b = c;
  >   }
  > ```
  > 
  > The background and context eventually "converge" to the same
  > valuation, which is the fixed point of the operator B.
  
  The fixed point of operator B is called the well-founded model
  of the definition list.
  
  This approach is called the well-founded semantics. More details
  and references can be found in my [magister thesis][wfs-rec-types].
  
  [wfs-rec-types]: https://is.muni.cz/th/xr8vu/Well-founded-type-semantics.pdf
-/

import Utils.Interpretation


def operatorC (salg: Salgebra sig) (dl: DefList sig) (b: Valuation salg.D):
  Valuation salg.D → Valuation salg.D
:=
  fun c => dl.interpretation salg b c

def operatorC.isMonotonic
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  IsMonotonic
    (Valuation.ord.standard salg.D)
    (Valuation.ord.standard salg.D)
    (operatorC salg dl b)
:=
  fun cLe x =>
    Expr.interpretation.isMonotonic.standard
      salg (dl.getDef x) b cLe

def operatorC.isMonotonic.approximation
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  IsMonotonic
    (Valuation.ord.approximation salg.D)
    (Valuation.ord.approximation salg.D)
    (operatorC salg dl b)
:=
  let bLe: b ⊑ b := (Valuation.ord.approximation salg.D).le_refl b
  
  fun c0LeC1 x =>
    Expr.interpretation.isMonotonic.approximation
      salg (dl.getDef x) bLe c0LeC1

noncomputable def operatorC.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  Lfp (Valuation.ord.standard salg.D) (operatorC salg dl b)
:=
  _root_.lfp
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)


noncomputable def operatorC.stage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  Valuation salg.D
:=
  lfp.stage
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

noncomputable def operatorC.fixedIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  { n: Ordinal //
    IsLfp
      (Valuation.ord.standard salg.D)
      (operatorC salg dl b)
      (stage salg dl b n)
  }
:=
  lfp.fixedIndex
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)

noncomputable def operatorC.lfpIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  { n: Ordinal //
    operatorC.stage salg dl b n = (operatorC.lfp salg dl b).val }
:= ⟨
  operatorC.fixedIndex salg dl b,
  rfl,
⟩

noncomputable def operatorC.stage.previous
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  Tuple (Valuation salg.D)
:=
  lfp.stage.previous
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

def operatorC.stage.limit
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
:
  IsSupremum
    (Valuation.ord.standard salg.D)
    (previous salg dl b n)
    (operatorC.stage salg dl b n)
:=
  lfp.stage.limit
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    nIsLimit

def operatorC.stage.limitAt
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
  (x: Nat)
:
  IsSupremum
    (Set3.ord.standard salg.D)
    (Set.pointwiseAt (fun d => d ∈ previous salg dl b n) x)
    (operatorC.stage salg dl b n x)
:=
  let isSup := operatorC.stage.limit salg dl b nIsLimit
  let supAt := Set.pointwiseSup.supAt ⟨_, isSup⟩ x
  
  supAt.property

def operatorC.stage.succEq
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
:
  operatorC.stage salg dl b n.succ =
    (operatorC salg dl b) (operatorC.stage salg dl b n)
:=
  lfp.stage.succEq
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b)
    (operatorC.isMonotonic salg dl b)
    n

def operatorC.stage.predEq
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nNotLim: ¬n.IsActualLimit)
:
  operatorC.stage salg dl b n =
    (operatorC salg dl b) (operatorC.stage salg dl b n.pred)
:=
  let nEq: n.pred.succ = n := Ordinal.succ_pred_of_not_limit nNotLim
  let stageEq:
    operatorC.stage salg dl b n.pred.succ =
      operatorC.stage salg dl b n
  :=
    congr rfl nEq
  
  stageEq.symm.trans (succEq salg dl b n.pred)

noncomputable def operatorC.stage.eqPrevN
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  {n: Ordinal}
  (nn: ↑n)
:
  operatorC.stage salg dl b nn =
    (operatorC.stage.previous salg dl b n).elements nn
:=
  rfl


def operatorC.stage.isMonotonic.approximation
  (salg: Salgebra sig)
  (dl: DefList sig)
  {b0 b1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (n: Ordinal)
:
  operatorC.stage salg dl b0 n ⊑ operatorC.stage salg dl b1 n
:=
  lfp.stage.isLeOfOpLe.multiOrder
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl b0)
    (operatorC salg dl b1)
    (operatorC.isMonotonic salg dl b0)
    (operatorC.isMonotonic salg dl b1)
    (Valuation.ord.approximation salg.D)
    (fun isLe x =>
      Expr.interpretation.isMonotonic.approximation
        salg (dl.getDef x) bLe isLe)
    Valuation.ord.standard.supPreservesLeApx
    n


noncomputable def operatorB (salg: Salgebra sig) (dl: DefList sig):
  Valuation salg.D → Valuation salg.D
:=
  fun b => (operatorC.lfp salg dl b).val

def operatorB.eqLfpC
  (lfp:
    Lfp
      (Valuation.ord.standard salg.D)
      (operatorC salg dl b))
:
  lfp.val = operatorB salg dl b
:=
  congr rfl
    (Least.eq
      (Valuation.ord.standard salg.D)
      lfp
      (operatorC.lfp salg dl b))


noncomputable def operatorB.isMonotonic.commonFixedIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b0 b1: Valuation salg.D)
:
  {
    n: Ordinal
  //
    operatorC.stage salg dl b0 n = operatorB salg dl b0 ∧
    operatorC.stage salg dl b1 n = operatorB salg dl b1
  }
:=
  let lfpI0 := operatorC.fixedIndex salg dl b0
  let lfpI1 := operatorC.fixedIndex salg dl b1
  
  if h: lfpI0.val ≤ lfpI1 then
    let isLfp:
      IsLfp
        (Valuation.ord.standard salg.D)
        (operatorC salg dl b0)
        (operatorC.stage salg dl b0 lfpI1)
    :=
      lfp.stage.gtLfpEqLfp
        (Valuation.ord.standard.isChainComplete salg.D)
        (operatorC salg dl b0)
        (operatorC.isMonotonic salg dl b0)
        h
        lfpI0.property
    ⟨
      lfpI1,
      And.intro
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b0 ↑lfpI1,
          isLfp,
        ⟩)
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b1 ↑lfpI1,
          lfpI1.property,
        ⟩)
    ⟩
  else
    let isLfp:
      IsLfp
        (Valuation.ord.standard salg.D)
        (operatorC salg dl b1)
        (operatorC.stage salg dl b1 lfpI0)
    :=
      lfp.stage.gtLfpEqLfp
        (Valuation.ord.standard.isChainComplete salg.D)
        (operatorC salg dl b1)
        (operatorC.isMonotonic salg dl b1)
        (le_of_not_le h)
        lfpI1.property
    ⟨
      lfpI0,
      And.intro
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b0 ↑lfpI0,
          lfpI0.property,
        ⟩)
        (operatorB.eqLfpC ⟨
          operatorC.stage salg dl b1 ↑lfpI0,
          isLfp,
        ⟩)
    ⟩

def operatorB.isMonotonic (salg: Salgebra sig) (dl: DefList sig):
  IsMonotonic
    (Valuation.ord.approximation salg.D)
    (Valuation.ord.approximation salg.D)
    (operatorB salg dl)
:=
  fun {b0 b1} b0LeB1 =>
    fun x =>
      let lfpI := isMonotonic.commonFixedIndex salg dl b0 b1
      
      let le := operatorC.stage.isMonotonic.approximation
        salg dl b0LeB1 lfpI
      
      (lfpI.property.left ▸ lfpI.property.right ▸ le) x

noncomputable def operatorB.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Lfp (Valuation.ord.approximation salg.D) (operatorB salg dl)
:=
  _root_.lfp
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)


noncomputable def operatorB.stage
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  Valuation salg.D
:=
  lfp.stage
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

noncomputable def operatorB.fixedIndex
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  { n: Ordinal // operatorB.stage salg dl n = (operatorB.lfp salg dl).val }
:= ⟨
  lfp.fixedIndex
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl),
  rfl
⟩

noncomputable def operatorB.stage.previous
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  Tuple (Valuation salg.D)
:=
  lfp.stage.previous
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

def operatorB.stage.limit
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
:
  IsSupremum
    (Valuation.ord.approximation salg.D)
    (operatorB.stage.previous salg dl n)
    (operatorB.stage salg dl n)
:=
  lfp.stage.limit
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    nIsLimit

def operatorB.stage.limitAt
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n: Ordinal}
  (nIsLimit: n.IsActualLimit)
  (x: Nat)
:
  IsSupremum
    (Set3.ord.approximation salg.D)
    (Set.pointwiseAt (fun d => d ∈ previous salg dl n) x)
    (operatorB.stage salg dl n x)
:=
  let isSup := operatorB.stage.limit salg dl nIsLimit
  let supAt := Set.pointwiseSup.supAt ⟨_, isSup⟩ x
  
  supAt.property

def operatorB.stage.succEq
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  operatorB.stage salg dl n.succ =
    (operatorB salg dl) (operatorB.stage salg dl n)
:=
  lfp.stage.succEq
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    n

noncomputable def operatorB.stage.eqPrevN
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
  (n: Ordinal)
  (nn: ↑n)
:
  operatorC.stage salg dl b nn =
    (operatorC.stage.previous salg dl b n).elements nn
:=
  rfl

def operatorB.stage.isMonotonic
  (salg: Salgebra sig)
  (dl: DefList sig)
  {n nn: Ordinal}
  (nnLt: nn ≤ n)
:
  stage salg dl nn ⊑ stage salg dl n
:=
  lfp.stage.isMono
    (Valuation.ord.approximation.isChainComplete salg.D)
    (operatorB salg dl)
    (operatorB.isMonotonic salg dl)
    (nnLt)


/-
  A valuation is a model of a definition list `dl` if interpreting
  `dl` in the valuation gives the same valuation.
-/
def Valuation.IsModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Set (Valuation salg.D)
:=
  fun v => v = dl.interpretation salg v v

/-
  The well-founded model of a definition list `dl` defines the
  semantics of the definition list.
-/
noncomputable def DefList.wellFoundedModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  (operatorB.lfp salg dl).val

def DefList.wellFoundedModel.eqLfpC
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  dl.wellFoundedModel salg
    =
  (operatorC.lfp salg dl (dl.wellFoundedModel salg)).val
:=
  (operatorB.lfp salg dl).property.isMember

/-
  A fixed point of the operator B is a model of the definition
  list.
-/
def operatorB.lfp.isModel
  (salg: Salgebra sig)
  (dl: DefList sig)
  {fp: Valuation salg.D}
  (isFp: IsFixedPoint (operatorB salg dl) fp)
:
  fp.IsModel salg dl
:= show
  fp ∈ IsFixedPoint (operatorC salg dl fp)
from by
  conv => lhs; rw [isFp]
  exact (operatorC.lfp salg dl fp).property.isMember

def DefList.wellFoundedModel.isLfpC
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  IsLfp
    (Valuation.ord.standard salg.D)
    (operatorC salg dl (dl.wellFoundedModel salg))
    (dl.wellFoundedModel salg)
:=
  by
    conv => rhs; rw [eqLfpC salg dl]
    exact
    (operatorC.lfp salg dl (dl.wellFoundedModel salg)).property

-- The well-founded model is the least fixed point of the operator B.
def DefList.wellFoundedModel.isLfpB
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  IsLfp
    (Valuation.ord.approximation salg.D)
    (operatorB salg dl)
    (dl.wellFoundedModel salg)
:=
  (operatorB.lfp salg dl).property

-- The well-founded model is a model of the definition list.
def DefList.wellFoundedModel.isModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  (dl.wellFoundedModel salg).IsModel salg dl
:=
  operatorB.lfp.isModel
    salg
    dl
    (DefList.wellFoundedModel.isLfpB salg dl).isMember


/-
  A triset is definable in a salgebra if there exists a finitely
  bounded definition list whose well-founded model contains the
  triset.
  
  See `DefList.IsFinBounded` from Chapter 3.
-/
def Salgebra.IsDefinable
  (salg: Salgebra sig)
  (set: Set3 salg.D)
:
  Prop
:=
  ∃
    (dl: FinBoundedDL sig)
    (x: Nat)
  ,
    set = dl.wellFoundedModel salg x

-- The type of trisets definable in a salgebra.
def Salgebra.Definable
  (salg: Salgebra sig)
:
  Type
:=
  { set: Set3 salg.D // salg.IsDefinable set }
