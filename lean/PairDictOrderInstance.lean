import Utils
import PairDictOrder

namespace Pair
  -- This has to be in a separate file to not inferfere with
  -- the definition of the depth dict order.
  noncomputable instance dictOrder: LinearOrder Pair where
    le := dictOrder.Le
    lt := dictOrder.Lt
    
    lt_iff_le_not_le _ _ :=
      Iff.intro
        (fun ab =>
          And.intro
            (Or.inl ab)
            (fun ba =>
              ba.elim
                (fun ba => ab.antisymm ba)
                (fun eq => (eq ▸ ab).irefl)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            id
            (fun eq => False.elim (notBaLe (Or.inr eq.symm))))
    
    le_refl _ := Or.inr rfl
    
    le_antisymm _ _ := dictOrder.Le.antisymm
    
    le_trans _ _ _ := dictOrder.Le.trans
    
    le_total := dictOrder.leTotal
    
    decidableLE := inferInstance
end Pair
