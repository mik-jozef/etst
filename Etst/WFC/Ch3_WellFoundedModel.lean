/-
  # Chapter 3: Operators B and C, and the Well-Founded Model
  
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
abbrev IsMonotonic {A B} (ordA: PartialOrder A) (ordB: PartialOrder B) :=
  @Monotone _ _ ordA.toPreorder ordB.toPreorder

abbrev OrderHomWrt {A B} (ordA: PartialOrder A) (ordB: PartialOrder B) :=
  @OrderHom A B ordA.toPreorder ordB.toPreorder

def isCcStd {T} := Valuation.ordStd.isChainComplete T
def isCcApx {T} := Valuation.ordApx.isChainComplete T


-- The family of operators C_b (often called "the" operator C).
def operatorC
  (dl: DefList)
  (b: Valuation Pair)
:
  OrderHomWrt (Valuation.ordStd Pair) (Valuation.ordStd Pair)
:=
  -- :/
  -- https://github.com/leanprover/lean4/issues/952
  let _ := Valuation.ordStd Pair
  {
    toFun := dl.triIntp2 b
    monotone' := fun _ _ => dl.triIntp2_mono_std
  }

-- The least fixed point of the operator C.
def operatorC.lfp
  (dl: DefList)
  (b: Valuation Pair)
:
  Valuation Pair
:=
  let _ := Valuation.ordStdLattice Pair
  (operatorC dl b).lfp

-- The operator C is monotonic wrt. the standard order.
def operatorC.mono_std
  (dl: DefList)
  (b: Valuation Pair)
:
  IsMonotonic
    (Valuation.ordStd Pair)
    (Valuation.ordStd Pair)
    (operatorC dl b)
:=
  let _ := Valuation.ordStd Pair
  (operatorC dl b).monotone'

-- The operator C is monotonic wrt. the approximation order (incl.
-- across different background valuations).
def operatorC.mono_apx
  (dl: DefList)
  {b0 b1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  {c0 c1: Valuation Pair}
  (cLe: c0 ⊑ c1)
:
  operatorC dl b0 c0 ⊑ operatorC dl b1 c1
:=
  dl.triIntp2_mono_apx bLe cLe


def operatorB.monotone'
  (dl: DefList)
  ⦃a b: Valuation Pair⦄
  (le: a ⊑ b)
:
  operatorC.lfp dl a ⊑ operatorC.lfp dl b
:=
  let _ := Valuation.ordStdLattice Pair
  OrderHom.lfpStage_induction2
    (operatorC dl a)
    (operatorC dl b)
    (Valuation.ordApx Pair).le
    (fun _n _isLim ih =>
      Valuation.ordStd.lubPreservesLeApxLub
        isLUB_iSup
        isLUB_iSup
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC dl b).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩)
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC dl a).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩))
    (fun _n _notLim prevLt ih =>
      operatorC.mono_apx dl le (ih ⟨_, prevLt⟩))

-- The operator B.
noncomputable def operatorB
  (dl: DefList)
:
  OrderHomWrt (Valuation.ordApx Pair) (Valuation.ordApx Pair)
:=
  let := Valuation.ordApx Pair
  {
    toFun := operatorC.lfp dl,
    monotone' := operatorB.monotone' dl
  }

noncomputable def operatorB.lfp
  (dl: DefList)
:
  Valuation Pair
:=
  (operatorB dl).lfpCc isCcApx


/-
  A valuation is a model of a definition list `dl` if interpreting
  `dl` in the valuation gives the same valuation.
-/
def Valuation.IsModel
  (dl: DefList)
:
  Set (Valuation Pair)
:=
  fun v => v = dl.triIntp v

/-
  The well-founded model of a definition list `dl` defines the
  semantics of the definition list. It is the least fixed point
  of the operator B.
-/
noncomputable def DefList.wfm
  (dl: DefList)
:
  Valuation Pair
:=
  (operatorB dl).lfpCc isCcApx

def DefList.wfm_is_fp_operatorB
  (dl: DefList)
:
  dl.wfm = operatorC.lfp dl (dl.wfm)
:=
  ((operatorB dl).lfpCc_isLfp isCcApx).left.symm

noncomputable def DefList.exprIntp
  (dl: DefList)
  (expr: BasicExpr)
:
  Set3 Pair
:=
  expr.triIntp [] dl.wfm


/-
  A fixed point of the operator B is a model of the definition
  list.
-/
def operatorB.fp_is_model
  (dl: DefList)
  {fp: Valuation Pair}
  (isFp: Function.fixedPoints (operatorB dl) fp)
:
  fp.IsModel dl
:= by
  let _ := Valuation.ordStdLattice Pair
  let eqC: fp = (operatorC dl fp).lfp := isFp.symm
  let eq: fp = operatorC.lfp dl fp := isFp.symm
  rw [operatorC.lfp, ←(operatorC dl fp).map_lfp] at eq
  conv at eq => rhs; rw [←eqC]
  exact eq

def DefList.wfm_isLfpC
  (dl: DefList)
:
  IsLfp
    (Valuation.ordStd Pair).le
    (operatorC dl (dl.wfm))
    (dl.wfm)
:= by
  let _ := Valuation.ordStdLattice
  let eq: (dl.wfm) = (operatorC dl (dl.wfm)).lfp :=
    ((operatorB dl).lfpCc_isLfp isCcApx).left.symm
  conv => rhs; rw [eq]
  exact (operatorC dl (dl.wfm)).isLeast_lfp

def DefList.wfm_eq_lfpC
  (dl: DefList)
:
  let := Valuation.ordStdLattice Pair
  dl.wfm = (operatorC dl (dl.wfm)).lfp
:=
  let := Valuation.ordStdLattice Pair
  IsLeast.unique (dl.wfm_isLfpC) (OrderHom.isLeast_lfp _)

def DefList.wfm_isLfpB
  (dl: DefList)
:
  IsLfp
    (Valuation.ordApx Pair).le
    (operatorB dl)
    (dl.wfm)
:=
  (operatorB dl).lfpCc_isLfp isCcApx

-- The well-founded model is a model of the definition list.
def DefList.wfm_isModel
  (dl: DefList)
:
  (dl.wfm).IsModel dl
:=
  operatorB.fp_is_model dl (wfm_isLfpB dl).left

def DefList.wfm_eq_def
  (dl: DefList)
  (x: Nat)
:
  dl.wfm x = dl.triIntp dl.wfm x
:=
  congr dl.wfm_isModel rfl


/-
  A triset is definable in aebra if there exists a finitely
  bounded definition list whose well-founded model contains the
  triset.
  
  See `DefList.IsFinBounded` from Chapter 3.
-/
def DefList.IsDefinable
  (set: Set3 Pair)
:
  Prop
:=
  ∃ (dl: FinBoundedDL)
    (x: Nat),
    set = dl.wfm x

-- The type of trisets definable in aebra.
def DefList.Definable: Type :=
  { set: Set3 Pair // IsDefinable set }
