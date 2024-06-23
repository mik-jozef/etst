import Utils.DefListDefEq
import UniSet3.DefListToEncoding
import UniSet3.TheDefList


set_option linter.unusedVariables false

def Set3.pairCall (fn arg: Set3 Pair): Set3 Pair := {
  defMem := fun p => ∃ (a: arg.defMem), fn.defMem (Pair.pair a p)
  posMem := fun p => ∃ (a: arg.posMem), fn.posMem (Pair.pair a p)
  defLePos :=
    fun _p pInDef =>
      let ⟨⟨a, aInArgDef⟩, apInFnDef⟩ := pInDef
      
      ⟨
        ⟨a, (arg.defLePos aInArgDef)⟩,
        fn.defLePos apInFnDef
      ⟩
}

def Set3.pairCallJust
  (fn: Set3 Pair)
  (arg: Pair)
:
  Set3 Pair
:= {
  defMem := fun p => fn.defMem (Pair.pair arg p)
  posMem := fun p => fn.posMem (Pair.pair arg p)
  defLePos := fun _ pInDef => fn.defLePos pInDef
}


namespace Pair
  namespace uniSet3
    open uniDefList
    
    def decodeValuation
      (s3: Set3 Pair)
    :
      Valuation Pair
    :=
      fun n => Set3.pairCallJust s3 (fromNat n)
    
    def internalOfExternal
      (v: Valuation Pair)
    :
      Valuation Pair
    :=
      decodeValuation (v theSet)
    
    
    def theInternalValuation: Valuation Pair :=
      internalOfExternal wfModel
    
    def internalOfExternal.isMonoStd:
      IsMonotonic
        (Valuation.ord.standard Pair)
        (Valuation.ord.standard Pair)
        internalOfExternal
    :=
      fun valLe _ => {
        -- Would be nice if this worked: `defLe t inVal := ...`
        defLe :=
          fun _ inVal => (valLe theSet).defLe inVal,
        posLe :=
          fun _ inVal => (valLe theSet).posLe inVal,
      }
    
    def internalOfExternal.isMonoApx:
      IsMonotonic
        (Valuation.ord.approximation Pair)
        (Valuation.ord.approximation Pair)
        internalOfExternal
    :=
      fun valLe _ => {
        defLe :=
          fun _ inVal => (valLe theSet).defLe inVal,
        posLe :=
          fun _ inVal => (valLe theSet).posLe inVal,
      }
    
    def internalOfExternal.preservesSupremaStd
      (ch: Chain (Valuation.ord.standard Pair))
    :
      let isCc := Valuation.ord.standard.isChainComplete Pair
      
      IsSupremum
        (Valuation.ord.standard Pair)
        (internalOfExternal '' ch.set)
        (internalOfExternal (ch.sup isCc).val)
    :=
      -- In your language, the vars of the return type should be
      -- in scope (I guess)?
      let isCc := Valuation.ord.standard.isChainComplete Pair
      
      {
        isMember :=
          fun ⟨v, vIn⟩ =>
            let ⟨preV, ⟨preVInCh, isPre⟩⟩ := vIn.unwrap
            let preLeSup :=
              (ch.sup isCc).property.isMember ⟨preV, preVInCh⟩
            
            isPre ▸ isMonoStd preLeSup
        isLeMember :=
          fun ub isUb x => {
            defLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.standard.inSup.inSomeSet.defMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨internalOfExternal v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.defLe insTheSet
            posLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.standard.inSup.inSomeSet.posMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨internalOfExternal v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.posLe insTheSet
          }
      }
    
    def internalOfExternal.preservesSupremaApx
      (ch: Chain (Valuation.ord.approximation Pair))
    :
      let isCc := Valuation.ord.approximation.isChainComplete Pair
      
      IsSupremum
        (Valuation.ord.approximation Pair)
        (internalOfExternal '' ch.set)
        (internalOfExternal (ch.sup isCc).val)
    :=
      let isCc := Valuation.ord.approximation.isChainComplete Pair
      
      {
        isMember :=
          fun ⟨v, vIn⟩ =>
            let ⟨preV, ⟨preVInCh, isPre⟩⟩ := vIn.unwrap
            let preLeSup :=
              (ch.sup isCc).property.isMember ⟨preV, preVInCh⟩
            
            isPre ▸ isMonoApx preLeSup
        isLeMember :=
          fun ub isUb x => {
            defLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.approximation.inSup.inSomeSet.defMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨internalOfExternal v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.defLe insTheSet
            posLe :=
              fun p inUb =>
                Valuation.ord.approximation.allInSet.inSup.posMem
                  (ch.sup isCc)
                  (fun v =>
                    let leUb :=
                      isUb
                        ⟨
                          internalOfExternal v,
                          v,
                          v.property,
                          rfl,
                        ⟩
                        x
                    
                    leUb.posLe inUb)
          }
      }
    
  end uniSet3
end Pair
