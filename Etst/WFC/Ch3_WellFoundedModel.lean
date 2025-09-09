/-
  # Chapter 4: Operators B and C, and the Well-Founded Model
  
  Note: this description is meant to give an intuitive understanding
  of what's going on in the chapter.
  
  Here we define the semantics of definition lists. That is, we
  associate every definition list `dl` with a valuation (called
  the well-founded model of `dl`) that "agrees" with the definitions
  in `dl`.
  
  Typically, the semantics of recursive definitions is defined
  as a least fixed point of their interpretation. For example,
  take `let T = 0 | T + 2` (to borrow syntax from TypeScript).
  We can imagine the least fixed point as being built in stages,
  starting with the least element of the standard order, the empty
  set:
  
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
  exist for some operators, such as those involving complements.
  For example, consider `let Bad = ~Bad`. The stages are:
  
      Bad₀ = ∅
      Bad₁ = ℕ
      Bad₂ = ∅
      Bad₃ = ℕ
      ⋮
  
  This sequence does not converge to a fixed point. In fact, no
  classical (ie. two-valued) fixed point exists. One way to guarantee
  the existence of a fixed point is to show the operator is monotonic
  with respect to a chain-complete order.

  Recall that our interpretation function from Chapter 3 takes two
  valuations (background and context, or `b` and `c`), and background
  is used to interpret complements. If background is constant, then
  the interpretation of complements is constant as well.
  
  This allows us to define a monotonic family of operators C
  indexed by the background valuation like this:
  
      C_b(c) = interpretation(b, c)
  
  Since the interpretation of complements is constant, the inter-
  pretation of C_b is monotonic (with respect to the standard
  order).
  
  We also define the operator B as follows:
  
      B(b) = lfp(C_b)
  
  where `lfp(X)` is the least fixed point of `X`. We can show
  that B is monotonic with respect to the approximation order.
  
  > Aside:
  > If you're willing to entertain the idea of algorithms that
  > terminate after potentially transfinite number of steps, then
  > you can can imagine computing the least fixed point of B as
  > executing the following algorithm:
  > 
  > ```
  >   // Valuations are initialized to the least elements in their
  >   // respective orders.
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
  
  This approach to semantics is called the well-founded semantics,
  and the existence of the least fixed point is guaranteed by
  a variant of the Knaster-Tarski theorem. More details and
  and references can be found in my [magister thesis][wfs-rec-types].
  
  [wfs-rec-types]: https://is.muni.cz/th/xr8vu/Well-founded-type-semantics.pdf
-/

import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.General.LfpStages
import Etst.WFC.Utils.General.LfpStagesCc
import Etst.WFC.Utils.Interpretation
import Etst.WFC.Utils.SupPreservesOtherOrder

namespace Etst


-- Fuck type classes.
abbrev IsMonotonic (ordA: PartialOrder A) (ordB: PartialOrder B) :=
  @Monotone _ _ ordA.toPreorder ordB.toPreorder

abbrev OrderHomWrt (ordA: PartialOrder A) (ordB: PartialOrder B) :=
  @OrderHom A B ordA.toPreorder ordB.toPreorder

def isCcStd {T} := Valuation.ordStd.isChainComplete T
def isCcApx {T} := Valuation.ordApx.isChainComplete T


-- The family of operators C_b (often called "the" operator C).
def operatorC
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  OrderHomWrt (Valuation.ordStd salg.D) (Valuation.ordStd salg.D)
:=
  -- :/
  -- https://github.com/leanprover/lean4/issues/952
  let _ := Valuation.ordStd salg.D
  {
    toFun := dl.interpretation salg b
    monotone' := fun _ _ => dl.interpretation_mono_std
  }

-- The least fixed point of the operator C.
def operatorC.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  Valuation salg.D
:=
  let _ := Valuation.ordStdLattice salg.D
  (operatorC salg dl b).lfp

-- The operator C is monotonic wrt. the standard order.
def operatorC.mono_std
  (salg: Salgebra sig)
  (dl: DefList sig)
  (b: Valuation salg.D)
:
  IsMonotonic
    (Valuation.ordStd salg.D)
    (Valuation.ordStd salg.D)
    (operatorC salg dl b)
:=
  let _ := Valuation.ordStd salg.D
  (operatorC salg dl b).monotone'

-- The operator C is monotonic wrt. the approximation order (incl.
-- across different background valuations).
def operatorC.mono_apx
  (salg: Salgebra sig)
  (dl: DefList sig)
  {b0 b1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  {c0 c1: Valuation salg.D}
  (cLe: c0 ⊑ c1)
:
  operatorC salg dl b0 c0 ⊑ operatorC salg dl b1 c1
:=
  dl.interpretation_mono_apx bLe cLe


def operatorB.monotone'
  (salg: Salgebra sig)
  (dl: DefList sig)
  ⦃a b: Valuation salg.D⦄
  (le: a ⊑ b)
:
  operatorC.lfp salg dl a ⊑ operatorC.lfp salg dl b
:=
  let _ := Valuation.ordStdLattice salg.D
  OrderHom.lfpStage_induction2
    (operatorC salg dl a)
    (operatorC salg dl b)
    (Valuation.ordApx salg.D).le
    (fun _n _isLim ih =>
      Valuation.ordStd.lubPreservesLeApxLub
        isLUB_iSup
        isLUB_iSup
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC salg dl b).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩)
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC salg dl a).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩))
    (fun _n _notLim prevLt ih =>
      operatorC.mono_apx salg dl le (ih ⟨_, prevLt⟩))

-- The operator B.
noncomputable def operatorB
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  OrderHomWrt (Valuation.ordApx salg.D) (Valuation.ordApx salg.D)
:=
  let := Valuation.ordApx salg.D
  {
    toFun := operatorC.lfp salg dl,
    monotone' := operatorB.monotone' salg dl
  }

noncomputable def operatorB.lfp
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  (operatorB salg dl).lfpCc isCcApx


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
  semantics of the definition list. It is the least fixed point
  of the operator B.
-/
noncomputable def DefList.wfm
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  (operatorB salg dl).lfpCc isCcApx

def DefList.wfm_is_fp_operatorB
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  dl.wfm salg = operatorC.lfp salg dl (dl.wfm salg)
:=
  ((operatorB salg dl).lfpCc_isLfp isCcApx).left.symm

noncomputable def DefList.exprInterp
  (salg: Salgebra sig)
  (dl: DefList sig)
  (expr: Expr sig)
:
  Set3 salg.D
:=
  expr.interpretation salg [] (dl.wfm salg) (dl.wfm salg)


/-
  A fixed point of the operator B is a model of the definition
  list.
-/
def operatorB.fp_is_model
  (salg: Salgebra sig)
  (dl: DefList sig)
  {fp: Valuation salg.D}
  (isFp: Function.fixedPoints (operatorB salg dl) fp)
:
  fp.IsModel salg dl
:= by
  let _ := Valuation.ordStdLattice salg.D
  let eqC: fp = (operatorC salg dl fp).lfp := isFp.symm
  let eq: fp = operatorC.lfp salg dl fp := isFp.symm
  rw [operatorC.lfp, ←(operatorC salg dl fp).map_lfp] at eq
  conv at eq => rhs; rw [←eqC]
  exact eq

def DefList.wfm_isLfpC
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  IsLfp
    (Valuation.ordStd salg.D).le
    (operatorC salg dl (dl.wfm salg))
    (dl.wfm salg)
:= by
  let _ := Valuation.ordStdLattice
  let eq: (dl.wfm salg) = (operatorC salg dl (dl.wfm salg)).lfp :=
    ((operatorB salg dl).lfpCc_isLfp isCcApx).left.symm
  conv => rhs; rw [eq]
  exact (operatorC salg dl (dl.wfm salg)).isLeast_lfp

def DefList.wfm_isLfpB
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  IsLfp
    (Valuation.ordApx salg.D).le
    (operatorB salg dl)
    (dl.wfm salg)
:=
  (operatorB salg dl).lfpCc_isLfp isCcApx

-- The well-founded model is a model of the definition list.
def DefList.wfm_isModel
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  (dl.wfm salg).IsModel salg dl
:=
  operatorB.fp_is_model salg dl (wfm_isLfpB salg dl).left


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
  ∃ (dl: FinBoundedDL sig)
    (x: Nat),
    set = dl.wfm salg x

-- The type of trisets definable in a salgebra.
def Salgebra.Definable
  (salg: Salgebra sig)
:
  Type
:=
  { set: Set3 salg.D // salg.IsDefinable set }
