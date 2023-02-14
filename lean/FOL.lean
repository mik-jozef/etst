/-
  Defines First order logic.
-/

import Arities
import Set

open Classical

namespace FOL
  @[reducible] def Variable := Nat
  
  structure Signature where
    Fn: Type
    Rel: Type
    arityFn: Fn → Type
    arityRel: Rel → Type
  
  inductive Term (sig: Signature) where
  | var (v: Variable)
  | fn (op: sig.Fn) (args: sig.arityFn op → Term sig)
  
  inductive Formula (sig: Signature) where
  | eq (left right: Term sig)
  | rel (rel: sig.Rel) (args: sig.arityRel rel → Term sig)
  | and (left right: Formula sig)
  | or (left right: Formula sig)
  | not (t: Formula sig)
  | Ex (var: Variable) (body: Formula sig)
  | All (var: Variable) (body: Formula sig)
  
  def Theory (sig: Signature) (T: Type): Type := T → Formula sig
  
  
  structure Structure (sig: Signature) where
    Domain: Type
    fns: (fn: sig.Fn) → (args: sig.arityFn fn → Domain) → Domain
    rels: (rel: sig.Rel) → (args: sig.arityRel rel → Domain) → Bool
  
  
  def Valuation (sre: Structure sig) := Variable → sre.Domain
  
  noncomputable def updateValuation
    (val: Valuation sre)
    (var: Variable)
    (d: sre.Domain)
  :
    Valuation sre
  :=
    fun v =>
      if v = var then
        d
      else
        val v
  
  
  def Term.interpretation
    {sig: Signature}
    (term: Term sig)
    (sre: Structure sig)
    (val: Valuation sre)
  :
    sre.Domain
  :=
    match term with
    | Term.var v => val v
    | Term.fn op args =>
        sre.fns op (fun arg => (args arg).interpretation sre val)
  
  noncomputable def Formula.interpretation
    {sig: Signature}
    (fm: Formula sig)
    (sre: Structure sig)
    (val: Valuation sre)
  :
    Bool
  :=
    match fm with
    | Formula.eq left rite =>
        left.interpretation sre val = rite.interpretation sre val
    | Formula.rel r args =>
        sre.rels r (fun arg => (args arg).interpretation sre val)
    | Formula.and left rite =>
        left.interpretation sre val ∧ rite.interpretation sre val
    | Formula.or left rite =>
        left.interpretation sre val ∨ rite.interpretation sre val
    | Formula.not negFm =>
        ¬ negFm.interpretation sre val
    | Formula.Ex var body =>
        ∃ d: sre.Domain, body.interpretation sre (updateValuation val var d)
    | Formula.All var body =>
        ∀ d: sre.Domain, body.interpretation sre (updateValuation val var d)
  
  
  def Structure.satisfies (sre: Structure sig) (fm: Formula sig): Prop :=
    ∀ val: Valuation sre, fm.interpretation sre val = true
  
  def Structure.satisfiesTheory (sre: Structure sig) (th: Theory sig T): Prop :=
    ∀ t: T, sre.satisfies (th t)
  
  def Theory.says (th: Theory sig T) (f: Formula sig): Prop :=
    ∀ sre: Structure sig, sre.satisfiesTheory th → sre.satisfies f
end FOL

namespace ZFC
  open FOL.Formula
  
  inductive Rel where
  | isIn
  
  def sig: FOL.Signature := {
    Fn := Empty
    Rel := Rel
    arityFn := fun _ => Empty
    arityRel := fun _ => ArityTwo
  }
  
  def isIn (a b: FOL.Variable): FOL.Formula sig :=
    rel
      Rel.isIn
      (fun v =>
        match v with
        | ArityTwo.zth => FOL.Term.var a
        | ArityTwo.fst => FOL.Term.var b)
  
  inductive Axiom where
  | extensionality
  | foundation
  | specification
  | union
    -- TODO make sure there isn't a certain free variable in fm
  | replacement (fm: FOL.Formula sig)
  | infinity
  | powerset
  | choice
  
  def theory: FOL.Theory sig Axiom :=
    fun zfcAxiom =>
      match zfcAxiom with
      | Axiom.extensionality =>
          All 0 (All 1 (All 2 (
            or
              (and (isIn 2 0) (isIn 2 1))
              (not (and (isIn 2 0) (isIn 2 1))))))
      
      | Axiom.foundation => sorry
      | Axiom.specification => sorry
      | Axiom.union => sorry
      | Axiom.replacement fm => sorry
      | Axiom.infinity => sorry
      | Axiom.powerset => sorry
      | Axiom.choice => sorry
end ZFC