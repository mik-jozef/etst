import Interpretation
import ExampleWFCs


namespace Pair
  /-
    This could be generalized for any signature with finite number
    of operators (and their arguments) -- only the op case would
    need to be able to handle that. Does mathlib have something
    like `(list: List A) → (m: A → B) → a ∈ list → m a ∈ list.map m`?
    I don't feel like coding it myself and it's basic enough
    that it should be in a standard library.
  -/
  def freeVars.givenBounds
    (expr: Expr pairSignature)
    (boundVars: List Nat)
  :
    {
      list: List Nat
    //
      ∀ x: expr.IsFreeVar (fun x => x ∈ boundVars), x.val ∈ list
    }
  :=
    match expr with
    | Expr.var x =>
        let freeVars := if x ∈ boundVars then [] else [x]
        ⟨
          freeVars,
          fun freeVar =>
            let eqVar: ↑freeVar = x := freeVar.property.left
            let ninBound: x ∉ boundVars := freeVar.property.right
            let eqVars: freeVars = [ x ] := if_neg ninBound
            let xIn: x ∈ [ x ] := List.Mem.head []
            by rewrite [eqVar, eqVars]; exact xIn
        ⟩
    | Expr.op pairSignature.Op.zero args => ⟨
        [],
        let expr: Expr pairSignature := Expr.op pairSignature.Op.zero args
        let eq:
          Expr.IsFreeVar (expr) fun x => x ∈ boundVars =
            fun x =>
              ∃ param,
                (args param).IsFreeVar (fun x => x ∈ boundVars) x
        :=
          rfl
        fun freeVar =>
          (eq ▸ freeVar).property.unwrap.val.elim,
      ⟩
    | Expr.op pairSignature.Op.pair args =>
        let freeVarsZth := givenBounds (args ArityTwo.zth) boundVars
        let freeVarsFst := givenBounds (args ArityTwo.fst) boundVars
        
        ⟨
          List.concatUnique freeVarsZth freeVarsFst,
          
          fun freeVar =>
            let freeVarParam := freeVar.property.unwrap
            match freeVarParam with
            | ⟨ArityTwo.zth, prop⟩ =>
                let freeVarInVars: freeVar.val ∈ freeVarsZth.val :=
                  freeVarsZth.property ⟨freeVar, prop⟩
                
                let freeVarIn:
                  ↑freeVar ∈ List.concatUnique freeVarsZth.val ↑freeVarsFst
                :=
                  /-
                    If I remove the "[DecidableEq T]" from the
                    append/concatUnique theorems, I get:
                    
                    > type mismatch
                    >   List.concatUnique.inLeftToIn freeVarInVars ↑freeVarsFst
                    > has type
                    >   ↑freeVar ∈ @List.concatUnique ℕ (fun a b => propDecidable (a = b)) ↑freeVarsZth ↑freeVarsFst : Prop
                    > but is expected to have type
                    >   ↑freeVar ∈ @List.concatUnique ℕ (fun a b => instDecidableEqNat a b) ↑freeVarsZth ↑freeVarsFst : Prop
                    
                    I swear typeclass instantiation is the most fucking retarded
                    part of Lean. And I love* the language.
                  -/
                  List.concatUnique.inLeftToIn freeVarInVars freeVarsFst
                freeVarIn
            | ⟨ArityTwo.fst, prop⟩ =>
                let freeVarInVars: freeVar.val ∈ freeVarsFst.val :=
                  freeVarsFst.property ⟨freeVar, prop⟩
                
                List.concatUnique.inRiteToIn freeVarsZth freeVarInVars
        ⟩
    | Expr.un left rite =>
        let freeVarsLeft := givenBounds left boundVars
        let freeVarsRite := givenBounds rite boundVars
        
        ⟨
          List.concatUnique freeVarsLeft freeVarsRite,
          fun freeVar =>
            freeVar.property.elim
              (fun isFreeInLeft =>
                let isInFreeVarsLeft :=
                  freeVarsLeft.property ⟨freeVar, isFreeInLeft⟩
                List.concatUnique.inLeftToIn isInFreeVarsLeft freeVarsRite)
              (fun isFreeInRite =>
                let isInFreeVarsRite :=
                  freeVarsRite.property ⟨freeVar, isFreeInRite⟩
                List.concatUnique.inRiteToIn freeVarsLeft isInFreeVarsRite),
        ⟩
    | Expr.ir left rite =>
        let freeVarsLeft := givenBounds left boundVars
        let freeVarsRite := givenBounds rite boundVars
        
        ⟨
          List.concatUnique freeVarsLeft freeVarsRite,
          fun freeVar =>
            freeVar.property.elim
              (fun isFreeInLeft =>
                let isInFreeVarsLeft :=
                  freeVarsLeft.property ⟨freeVar, isFreeInLeft⟩
                List.concatUnique.inLeftToIn isInFreeVarsLeft freeVarsRite)
              (fun isFreeInRite =>
                let isInFreeVarsRite :=
                  freeVarsRite.property ⟨freeVar, isFreeInRite⟩
                List.concatUnique.inRiteToIn freeVarsLeft isInFreeVarsRite),
        ⟩
    | Expr.cpl expr => givenBounds expr boundVars
    | Expr.ifThen cond expr =>
        let freeVarsCond := givenBounds cond boundVars
        let freeVarsExpr := givenBounds expr boundVars
        
        ⟨
          List.concatUnique freeVarsCond freeVarsExpr,
          fun freeVar =>
            freeVar.property.elim
              (fun isFreeInCond =>
                let isInFreeVarsCond :=
                  freeVarsCond.property ⟨freeVar, isFreeInCond⟩
                List.concatUnique.inLeftToIn isInFreeVarsCond freeVarsExpr)
              (fun isFreeInExpr =>
                let isInFreeVarsExpr :=
                  freeVarsExpr.property ⟨freeVar, isFreeInExpr⟩
                List.concatUnique.inRiteToIn freeVarsCond isInFreeVarsExpr),
        ⟩
    | Expr.Un x expr =>
        let freeVarsExpr := givenBounds expr (boundVars.appendUnique x)
        ⟨
          freeVarsExpr,
          fun freeVar =>
            let xInBoundOr bv := bv ∈ boundVars ∨ bv = x
            -- let xInAppend bv := bv ∈ boundVars.appendUnique x
            
            let eq:
              xInBoundOr =
              -- Should be "xInAppend" but "▸" is a pussy.
              (fun bv => bv ∈ boundVars.appendUnique x)
            :=
              funext fun bv =>
                propext
                  (Iff.intro
                    (fun bvInBoundOr =>
                      bvInBoundOr.elim
                        (List.appendUnique.inToIn x)
                        (fun eq =>
                          eq ▸ List.appendUnique.eqToIn boundVars x))
                    (List.appendUnique.inToOrInEq))
            
            freeVarsExpr.property ⟨freeVar, eq ▸ freeVar.property⟩,
        ⟩
    | Expr.Ir x expr =>
        let freeVarsExpr := givenBounds expr (boundVars.appendUnique x)
        ⟨
          freeVarsExpr,
          fun freeVar =>
            let xInBoundOr bv := bv ∈ boundVars ∨ bv = x
            
            let eq:
              xInBoundOr =
              (fun bv => bv ∈ boundVars.appendUnique x)
            :=
              funext fun bv =>
                propext
                  (Iff.intro
                    (fun bvInBoundOr =>
                      bvInBoundOr.elim
                        (List.appendUnique.inToIn x)
                        (fun eq =>
                          eq ▸ List.appendUnique.eqToIn boundVars x))
                    (List.appendUnique.inToOrInEq))
            
            freeVarsExpr.property ⟨freeVar, eq ▸ freeVar.property⟩,
        ⟩
  
  def freeVars (expr: Expr pairSignature):
    {
      list: List Nat
    //
      ∀ x: expr.IsFreeVar Set.empty, x.val ∈ list
    }
  :=
    let eq: Set.empty = fun x: Nat => x ∈ [] :=
      funext fun _ =>
        (propext (Iff.intro nofun nofun))
    
    let fv := freeVars.givenBounds expr []
    -- Using `eq ▸ fv` directly breaks `freeVars.eq` :(
    ⟨fv.val, eq.symm ▸ fv.property⟩
  
  def freeVars.eq (expr: Expr pairSignature):
    (freeVars expr).val = freeVars.givenBounds expr []
  :=
    rfl
end Pair
