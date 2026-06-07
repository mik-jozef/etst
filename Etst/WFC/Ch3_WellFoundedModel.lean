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
  with respect to a chain-complete partial order.

  Recall that our interpretation function from Chapter 3 takes two
  valuations (background and context, or `b` and `c`), and background
  is used to interpret complements. If background is constant, then
  the interpretation of (odd-depth) complements is constant as well.
  
  This allows us to define a monotonic family of operators C
  indexed by the background valuation like this:
  
      C_b(c) = interpretation(b, c)
  
  Since the interpretation of odd-depth complements is constant,
  the interpretation of C_b is monotonic (with respect to the
  standard order).
  
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
  (b o: Valuation Pair)
:
  OrderHomWrt (Valuation.ordStd Pair) (Valuation.ordStd Pair)
:=
  -- :/
  -- https://github.com/leanprover/lean4/issues/952
  let _ := Valuation.ordStd Pair
  {
    toFun c := dl.intpDefs2 b c o
    monotone' _ _ := dl.intpDefs2_mono_std (le_refl _)
  }

-- The least fixed point of the operator C.
def operatorC.lfp
  (dl: DefList)
  (b o: Valuation Pair)
:
  Valuation Pair
:=
  let _ := Valuation.ordStdLattice Pair
  (operatorC dl b o).lfp

-- The operator C is monotonic wrt. the standard order.
def operatorC.mono_std
  (dl: DefList)
  (b o: Valuation Pair)
:
  IsMonotonic
    (Valuation.ordStd Pair)
    (Valuation.ordStd Pair)
    (operatorC dl b o)
:=
  let _ := Valuation.ordStd Pair
  (operatorC dl b o).monotone'

-- The operator C is monotonic wrt. the approximation order (incl.
-- across different background valuations).
def operatorC.mono_apx
  (dl: DefList)
  {b0 b1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  {c0 c1: Valuation Pair}
  (cLe: c0 ⊑ c1)
  (o: Valuation Pair)
:
  operatorC dl b0 o c0 ⊑ operatorC dl b1 o c1
:=
  dl.intpDefs2_mono_apx bLe cLe


def operatorB.monotone'
  (dl: DefList)
  (o: Valuation Pair)
  ⦃a b: Valuation Pair⦄
  (le: a ⊑ b)
:
  operatorC.lfp dl a o ⊑ operatorC.lfp dl b o
:=
  let _ := Valuation.ordStdLattice Pair
  OrderHom.lfpStage_induction2
    (operatorC dl a o)
    (operatorC dl b o)
    (Valuation.ordApx Pair).le
    (fun _n _isLim ih =>
      Valuation.ordStd.lubPreservesLeApxLub
        isLUB_iSup
        isLUB_iSup
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC dl b o).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩)
        (fun _ ⟨m, eq⟩ => ⟨
          (operatorC dl a o).lfpStage m,
          ⟨m, rfl⟩,
          eq ▸ ih m,
        ⟩))
    (fun _n _notLim prevLt ih =>
      operatorC.mono_apx dl le (ih ⟨_, prevLt⟩) o)

-- The operator B.
noncomputable def operatorB
  (dl: DefList)
  (o: Valuation Pair)
:
  OrderHomWrt (Valuation.ordApx Pair) (Valuation.ordApx Pair)
:=
  let := Valuation.ordApx Pair
  {
    toFun b := operatorC.lfp dl b o,
    monotone' := operatorB.monotone' dl o
  }

noncomputable def operatorB.lfp
  (dl: DefList)
  (o: Valuation Pair)
:
  Valuation Pair
:=
  (operatorB dl o).lfpCc isCcApx


/-
  A valuation is a model of a definition list `dl` if interpreting
  `dl` in the valuation gives the same valuation.
-/
def Valuation.IsModel
  (dl: DefList)
  (o: Valuation Pair)
:
  Set (Valuation Pair)
:=
  fun v => v = dl.intpDefs v o

/-
  The well-founded model of a definition list `dl` defines the
  semantics of the definition list. It is the least fixed point
  of the operator B.
-/
noncomputable def DefList.wfm
  (dl: DefList)
  (o: Valuation Pair)
:
  Valuation Pair
:=
  (operatorB dl o).lfpCc isCcApx

def DefList.wfm_is_fp_operatorB
  (dl: DefList)
  (o: Valuation Pair)
:
  dl.wfm o = operatorC.lfp dl (dl.wfm o) o
:=
  ((operatorB dl o).lfpCc_isLfp isCcApx).left.symm

noncomputable def DefList.triIntp
  (dl: DefList)
  (o: Valuation Pair)
  (fv: List Pair)
  (expr: BasicExpr)
:
  Set3 Pair
:=
  expr.triIntp fv (dl.wfm o) o


/-
  A fixed point of the operator B is a model of the definition
  list.
-/
def operatorB.fp_is_model
  (dl: DefList)
  (o: Valuation Pair)
  {fp: Valuation Pair}
  (isFp: Function.fixedPoints (operatorB dl o) fp)
:
  Valuation.IsModel dl o fp
:= by
  let _ := Valuation.ordStdLattice Pair
  let eqC: fp = (operatorC dl fp o).lfp := isFp.symm
  let eq: fp = operatorC.lfp dl fp o := isFp.symm
  rw [operatorC.lfp, ←(operatorC dl fp o).map_lfp] at eq
  conv at eq => rhs; rw [←eqC]
  exact eq

def DefList.wfm_isLfpC
  (dl: DefList)
  (o: Valuation Pair)
:
  IsLfp
    (Valuation.ordStd Pair).le
    (operatorC dl (dl.wfm o) o)
    (dl.wfm o)
:= by
  let _ := Valuation.ordStdLattice
  let eq: dl.wfm o = (operatorC dl (dl.wfm o) o).lfp :=
    ((operatorB dl o).lfpCc_isLfp isCcApx).left.symm
  conv => rhs; rw [eq]
  exact (operatorC dl (dl.wfm o) o).isLeast_lfp

def DefList.wfm_eq_lfpC
  (dl: DefList)
  (o: Valuation Pair)
:
  let := Valuation.ordStdLattice Pair
  dl.wfm o = (operatorC dl (dl.wfm o) o).lfp
:=
  let := Valuation.ordStdLattice Pair
  IsLeast.unique (dl.wfm_isLfpC o) (OrderHom.isLeast_lfp _)

def DefList.wfm_isLfpB
  (dl: DefList)
  (o: Valuation Pair)
:
  IsLfp
    (Valuation.ordApx Pair).le
    (operatorB dl o)
    (dl.wfm o)
:=
  (operatorB dl o).lfpCc_isLfp isCcApx

-- The well-founded model is a model of the definition list.
def DefList.wfm_isModel
  (dl: DefList)
  (o: Valuation Pair)
:
  Valuation.IsModel dl o (dl.wfm o)
:=
  operatorB.fp_is_model dl o (wfm_isLfpB dl o).left

def DefList.wfm_eq_def
  (dl: DefList)
  (o: Valuation Pair)
  (x: Nat)
:
  dl.wfm o x = dl.intpDefs (dl.wfm o) o x
:=
  congr (dl.wfm_isModel o) rfl


/-
  A triset is definable relative to an oracle `o` if there exists
  a finitely bounded definition list whose well-founded model
  (computed wrt. the oracle `o`) contains the triset.
  
  See `DefList.IsFinBounded` from Chapter 3.
-/
def DefList.IsOracleDefinable
  (o: Valuation Pair)
  (set: Set3 Pair)
:
  Prop
:=
  ∃ (dl: FinBoundedDl)
    (x: Nat),
    set = dl.wfm o x

/-
  A triset is definable if it is oracle-definable wrt. the empty
  valuation.
-/
def DefList.IsDefinable
  (set: Set3 Pair)
:
  Prop
:=
  DefList.IsOracleDefinable .empty set

-- The type of definable trisets.
def DefList.Definable: Type :=
  { set: Set3 Pair // IsDefinable set }
