-- See the file `./UniDefList.lean`.

import UniSet3.Defs


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insPairDictLt (isPD: IsPairDictLt p):
      InsEdl pairDictLt p
    :=
      let inListZeroPair:
        pairDictLt.zeroPair ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      let inListLtLeft:
        pairDictLt.ltLeft ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      let inListEqLeft:
        pairDictLt.eqLeft ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      match p with
      | zero => isPD.elim
      | pair zero zero => isPD.elim
      | pair zero (pair _ _) =>
        insWfmDef.toInsWfm
          (insFinUn
            inListZeroPair
            (insPair insZero (insPair insAny insAny)))
      | pair (pair aA aB) zero => isPD.elim
      | pair (pair aA aB) (pair bA bB) =>
        
        open IsComparable in
        match Pair.dictOrder.ltTotal aA bA with
        | IsLt ab =>
          let ipd: IsPairDictLt (pair aA bA) := ab
          let aInsAB := insPairDictLt ipd
          
          insWfmDef.toInsWfm
            (insFinUn
              inListLtLeft
              (insUnDom aInsAB
                (insPair
                  (insPair
                    (insZthMember (insFree insBound nat502Neq500))
                    insAny)
                  (insPair
                    (insFstMember (insFree insBound nat502Neq500))
                    insAny))))
        | IsGt ba =>
          isPD.elim
            (fun ab => dictOrder.Lt.antisymm ab ba)
            (fun ⟨eq, _⟩ => (eq ▸ ba).irefl)
        | IsEq eq =>
          let ipd: IsPairDictLt (pair aB bB) :=
            isPD.elim
              (fun ab => (eq ▸ ab).irefl)
              (fun ⟨_, lt⟩ => lt)
          let bInsAB := insPairDictLt ipd
          
          insWfmDef.toInsWfm
            (insFinUn
              inListEqLeft
              (insUnDom bInsAB
                (insArbUn aA
                  (insPair
                    (insPair
                      insBound
                      (insZthMember
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))
                    (insPair
                      (eq ▸ insBound)
                      (insFstMember
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))))))
    
    def Inw.toIsPairDictLt.p p (inw: InwEdl pairDictLt p):
      IsPairDictLt p
    :=
      inwFinUnElim (inwWfm.toInwWfmDef inw)
        (fun inwZeroPair =>
          match p with
          | zero => inwPairElim.nope inwZeroPair
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwZeroPair
            match b with
            | zero => inwPairElim.nope r
            | pair _ _ =>
              (inwZeroElim l) ▸ trivial)
        (fun inwLtLeft =>
          let ⟨pBound, inwDomain, inwBody⟩ := inwUnDomElim inwLtLeft
          match p with
          | zero => inwPairElim.nope inwBody
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwBody
            match a, b with
            | zero, _ => inwPairElim.nope l
            | _, zero => inwPairElim.nope r
            | pair aA aB, pair bA bB =>
              let ⟨inwZth, _⟩ := inwPairElim l
              let ⟨inwFst, _⟩ := inwPairElim r
              
              let eq: pair aA bA = pBound := inwBoundElim
                (inwZthFstElim inwZth inwFst nat502Neq500 rfl)
              
              let inwA: InwEdl pairDictLt (pair aA bA) :=
                eq ▸ inwFreeElim inwDomain nat500NeqPairDictLt
              
              have := depth.leZth aA aB bA bB
              Or.inl (toIsPairDictLt.p (pair aA bA) inwA))
        (fun inwEqLeft =>
          let ⟨pRBound, inwDomain, inwBody⟩ := inwUnDomElim inwEqLeft
          let ⟨pLBound, inwBody⟩ := inwArbUnElim inwBody
          
          match p with
          | zero => inwPairElim.nope inwBody
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwBody
            match a, b with
            | zero, _ => inwPairElim.nope l
            | _, zero => inwPairElim.nope r
            | pair aA aB, pair bA bB =>
              let ⟨inw501A, inwZth⟩ := inwPairElim l
              let ⟨inw501B, inwFst⟩ := inwPairElim r
              
              let eq := inwBoundElim
                (inwZthFstElim inwZth inwFst nat502Neq500 rfl)
              
              let inwB: InwEdl pairDictLt (pair aB bB) :=
                eq ▸ inwFreeElim inwDomain nat500NeqPairDictLt
              
              have:
                (pair aB bB).depth
                  <
                (pair (pair aA aB) (pair bA bB)).depth
              :=
                let leSL := Pair.depthSuccLeR aA aB
                let leSR := Pair.depthSuccLeR bA bB
                (Pair.depth.casesEq aB bB).elim
                  (fun ⟨eq, _⟩ => eq ▸ (leSL.trans_lt (Pair.depthLtL _ _)))
                  (fun ⟨eq, _⟩ => eq ▸ (leSR.trans_lt (Pair.depthLtR _ _)))
              
              let r := toIsPairDictLt.p (pair aB bB) inwB
              
              Or.inr
                (And.intro
                  ((inwBoundElim inw501A).trans (inwBoundElim inw501B).symm)
                  r))
    termination_by p.depth
    
    def Inw.toIsPairDictLt (inw: InwEdl pairDictLt p):
      IsPairDictLt p
    :=
      Inw.toIsPairDictLt.p p inw
  end uniSet3
end Pair
