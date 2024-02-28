import UniDefList
import Wfm

namespace Pair
  namespace uniSet
    open Expr
    open PairExpr
    open uniDefList
    
    def IsNatEncoding: Set Pair
    | zero => True
    | pair a b => (IsNatEncoding a) ∧ b = zero
    
    def NatEncoding := { p // IsNatEncoding p }
    
    def ins := wfm.insWfm pairSalgebra uniDefList.defList
    def inw := wfm.inwWfm pairSalgebra uniDefList.defList
    
    def insV := wfm.insWfm pairSalgebra
    def inwV := wfm.inwWfm pairSalgebra
    
    
    def natIns (isPn: IsNatEncoding pn): ins nat pn :=
      match pn with
      | Pair.zero =>
        wfm.insWfmDef.toInsWfm (ins.unL (insZero _) _)
      
      | Pair.pair a b =>
        let insA: ins nat a := natIns isPn.left
        let insExpr: ins nat.expr (Pair.pair a b) :=
          ins.unR _ (insPair
            insA
            ((insZeroIff _ _).mpr isPn.right))
        wfm.insWfmDef.toInsWfm insExpr
    
    def inwNat.isNatEncoding (w: inw nat pn): IsNatEncoding pn :=
      let inwNatDef: inw nat.expr pn :=
        wfm.inwWfm.toInwWfmDef w
      
      inwNatDef.elim
        (fun (pnInwZero: inw zeroExpr pn) =>
          let pnEqZero: pn = Pair.zero := (inwZeroIff _ _).mp pnInwZero
          pnEqZero ▸ trivial)
        (fun (w: inw (pairExpr nat zeroExpr) pn) =>
          match pn with
          | zero => trivial
          | pair _a _b =>
            And.intro
              (inwNat.isNatEncoding (inwPairElim _ w).inwL)
              (inwPairElim _ w).inwR)
    
    def natNinw: ¬IsNatEncoding pn → ¬inw nat pn :=
      inwNat.isNatEncoding.contra
    
    
    structure IsNatPairAA.Str (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAA.Str p n
    def NatPairAA := { p // IsNatPairAA p }
    
    def natPairAAIns (isPnaa: IsNatPairAA p): ins natPairAA p :=
      let np := isPnaa.unwrap
      
      let insD := insFree (natIns np.property.isNat) Nat.noConfusion
      let insPairAA := insPair insBound insBound
      
      np.property.eq ▸
        wfm.insWfmDef.toInsWfm (ins.unDom insD insPairAA)
    
    def inwNatPairAA.isNatPairAA (w: inw natPairAA p): IsNatPairAA p :=
      let inwDef := wfm.inwWfm.toInwWfmDef w
      let n := (inw.unDomElim inwDef).unwrap
      
      let inwNatN: inw nat n :=
        inwFreeElim n.property.insDomain Nat.noConfusion
      
      let ⟨pairL, exR⟩ := inwPairElim.ex _ n.property.insBody
      let ⟨pairR, ⟨eq, insL, insR⟩⟩ := exR.unwrap
      
      let eqL := inwBoundEq insL
      let eqR := inwBoundEq insR
      let eqN := eqR.trans eqL.symm
      
      ⟨n.val, {
        isNat := inwNat.isNatEncoding inwNatN
        eq := eq ▸ (inwBoundEq insL) ▸ eqN ▸ rfl
      }⟩
    
  end uniSet
end Pair
