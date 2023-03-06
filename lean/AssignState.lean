import Set

open Classical


namespace Program
  namespace Assign
    inductive State (srcAddress destAddress: Nat) where
      | goToSrc (n: ↑(srcAddress + 1))
      | goToDest0 (n: ↑(srcAddress + destAddress + 1))
      | goToDest1 (n: ↑(srcAddress + destAddress + 1))
      | halt
    
    /-
      The rest of this file is dedicated to proving State is finite.
      
      How can I prove this in three lines? Please tell me such an obvious
      thing can be proven in three lines and I'm just <del>dumb</del>
      ignorant of The Way.
    -/
    
    def State.isFinite.s {srcAddress destAddress: Nat}
      (n: Nat)
      (nLt: n < srcAddress + 1)
    :
      {
        list: List (State srcAddress destAddress)
      //
        --∀ (nn: Nat) (nnLe: nn ≤ n),
        ∀ (nn: Nat) (nnLe: nn < n + 1),
          --list.has (State.goToSrc ⟨nn, Nat.letTrans nnLe nLt⟩)
          list.has (State.goToSrc ⟨nn, Nat.lteTrans nnLe nLt⟩)
      }
    :=
      if h: n = 0 then ⟨
        [ State.goToSrc ⟨0, Nat.succ_pos _⟩],
        fun nn nnLe =>
          match nn with
          | Nat.zero => ⟨⟨0, Nat.succ_pos 0⟩, rfl⟩
          --| Nat.succ nnn => False.elim (Nat.not_succ_le_zero nnn (h ▸ nnLe))
          | Nat.succ nnn =>
              let nnnSuccLtOne: Nat.succ nnn < 0 + 1 := h ▸ nnLe
              let nnnLtZero: nnn < 0 := Nat.le_of_succ_le_succ nnnSuccLtOne
              False.elim (Nat.not_succ_le_zero nnn nnnLtZero)
      ⟩ else
        let sN := State.goToSrc ⟨n, nLt⟩
        let lPred := s (n - 1) (Nat.letTrans (Nat.sub_le _ _) nLt)
        let lN := [ sN ]
        let l := lPred.val ++ lN
        ⟨
          l,
          fun nn nnLe =>
            (Nat.eq_or_lt_of_le nnLe).elim
              (fun eq =>
                let eq: nn = n := Nat.noConfusion eq id
                let sNn: State srcAddress destAddress :=
                  State.goToSrc ⟨nn, eq ▸ nLt⟩
                let sNn.eq: sN = sNn := congr rfl (Subtype.eq eq.symm)
                
                let mem: sNn ∈ lN := sNn.eq ▸ List.Mem.head _ _
                let sNInL: sNn ∈ l := List.mem_append_of_mem_right lPred.val mem
                List.has.fromMem sNInL)
              (fun lt =>
                let nnLt: nn < n := Nat.lt_of_succ_lt_succ lt
                let sNn: State srcAddress destAddress :=
                  --State.goToSrc ⟨nn, Nat.lt_trans lt nLt⟩
                  State.goToSrc ⟨nn, Nat.lt_trans nnLt nLt⟩
                
                --let lPredHas := lPred.property nn (Nat.le_sub_of_add_le lt)
                let nEq: n = n - 1 + 1 :=
                  match n with
                  | 0 => False.elim (h rfl)
                  | Nat.succ _ => rfl
                let lPredHas := lPred.property nn (nEq ▸ nnLt)
                let sNInLPred: sNn ∈ lPred.val := List.has.toMem lPredHas
                let sNInL: sNn ∈ l := List.mem_append_of_mem_left lN sNInLPred
                List.has.fromMem sNInL
              )
        ⟩
    
    def State.isFinite.d0 {srcAddress destAddress: Nat}
      (n: Nat)
      (nLt: n < srcAddress + destAddress + 1)
    :
      {
        list: List (State srcAddress destAddress)
      //
        ∀ (nn: Nat) (nnLe: nn < n + 1),
          list.has (State.goToDest0 ⟨nn, Nat.lteTrans nnLe nLt⟩)
      }
    :=
      if h: n = 0 then ⟨
        [ State.goToDest0 ⟨0, Nat.succ_pos _⟩],
        fun nn nnLe =>
          match nn with
          | Nat.zero => ⟨⟨0, Nat.succ_pos 0⟩, rfl⟩
          --| Nat.succ nnn => False.elim (Nat.not_succ_le_zero nnn (h ▸ nnLe))
          | Nat.succ nnn =>
              let nnnSuccLtOne: Nat.succ nnn < 0 + 1 := h ▸ nnLe
              let nnnLtZero: nnn < 0 := Nat.le_of_succ_le_succ nnnSuccLtOne
              False.elim (Nat.not_succ_le_zero nnn nnnLtZero)
      ⟩ else
        let sN := State.goToDest0 ⟨n, nLt⟩
        let lPred := d0 (n - 1) (Nat.letTrans (Nat.sub_le _ _) nLt)
        let lN := [ sN ]
        let l := lPred.val ++ lN
        ⟨
          l,
          fun nn nnLe =>
            (Nat.eq_or_lt_of_le nnLe).elim
              (fun eq =>
                let eq: nn = n := Nat.noConfusion eq id
                let sNn: State srcAddress destAddress :=
                  State.goToDest0 ⟨nn, eq ▸ nLt⟩
                let sNn.eq: sN = sNn := congr rfl (Subtype.eq eq.symm)
                
                let mem: sNn ∈ lN := sNn.eq ▸ List.Mem.head _ _
                let sNInL: sNn ∈ l := List.mem_append_of_mem_right lPred.val mem
                List.has.fromMem sNInL)
              (fun lt =>
                let nnLt: nn < n := Nat.lt_of_succ_lt_succ lt
                let sNn: State srcAddress destAddress :=
                  State.goToDest0 ⟨nn, Nat.lt_trans nnLt nLt⟩
                
                --let lPredHas := lPred.property nn (Nat.le_sub_of_add_le lt)
                let nEq: n = n - 1 + 1 :=
                  match n with
                  | 0 => False.elim (h rfl)
                  | Nat.succ _ => rfl
                let lPredHas := lPred.property nn (nEq ▸ nnLt)
                let sNInLPred: sNn ∈ lPred.val := List.has.toMem lPredHas
                let sNInL: sNn ∈ l := List.mem_append_of_mem_left lN sNInLPred
                List.has.fromMem sNInL
              )
        ⟩
    
    def State.isFinite.d1 {srcAddress destAddress: Nat}
      (n: Nat)
      (nLt: n < srcAddress + destAddress + 1)
    :
      {
        list: List (State srcAddress destAddress)
      //
        ∀ (nn: Nat) (nnLe: nn < n + 1),
          list.has (State.goToDest1 ⟨nn, Nat.lteTrans nnLe nLt⟩)
      }
    :=
      if h: n = 0 then ⟨
        [ State.goToDest1 ⟨0, Nat.succ_pos _⟩],
        fun nn nnLe =>
          match nn with
          | Nat.zero => ⟨⟨0, Nat.succ_pos 0⟩, rfl⟩
          --| Nat.succ nnn => False.elim (Nat.not_succ_le_zero nnn (h ▸ nnLe))
          | Nat.succ nnn =>
              let nnnSuccLtOne: Nat.succ nnn < 0 + 1 := h ▸ nnLe
              let nnnLtZero: nnn < 0 := Nat.le_of_succ_le_succ nnnSuccLtOne
              False.elim (Nat.not_succ_le_zero nnn nnnLtZero)
      ⟩ else
        let sN := State.goToDest1 ⟨n, nLt⟩
        let lPred := d1 (n - 1) (Nat.letTrans (Nat.sub_le _ _) nLt)
        let lN := [ sN ]
        let l := lPred.val ++ lN
        ⟨
          l,
          fun nn nnLe =>
            (Nat.eq_or_lt_of_le nnLe).elim
              (fun eq =>
                let eq: nn = n := Nat.noConfusion eq id
                let sNn: State srcAddress destAddress :=
                  State.goToDest1 ⟨nn, eq ▸ nLt⟩
                let sNn.eq: sN = sNn := congr rfl (Subtype.eq eq.symm)
                
                let mem: sNn ∈ lN := sNn.eq ▸ List.Mem.head _ _
                let sNInL: sNn ∈ l := List.mem_append_of_mem_right lPred.val mem
                List.has.fromMem sNInL)
              (fun lt =>
                let nnLt: nn < n := Nat.lt_of_succ_lt_succ lt
                let sNn: State srcAddress destAddress :=
                  State.goToDest1 ⟨nn, Nat.lt_trans nnLt nLt⟩
                
                --let lPredHas := lPred.property nn (Nat.le_sub_of_add_le lt)
                let nEq: n = n - 1 + 1 :=
                  match n with
                  | 0 => False.elim (h rfl)
                  | Nat.succ _ => rfl
                let lPredHas := lPred.property nn (nEq ▸ nnLt)
                let sNInLPred: sNn ∈ lPred.val := List.has.toMem lPredHas
                let sNInL: sNn ∈ l := List.mem_append_of_mem_left lN sNInLPred
                List.has.fromMem sNInL
              )
        ⟩
    
    def State.isFinite {srcAddress destAddress: Nat}:
      Type.isFinite (State srcAddress destAddress)
    :=
      let lS := isFinite.s srcAddress Nat.le.refl
      let lD0 := isFinite.d0 (srcAddress + destAddress) Nat.le.refl
      let lD1 := isFinite.d1 (srcAddress + destAddress) Nat.le.refl
      let lH := [State.halt]
      let l := lS.val ++ lD0.val ++ lD1.val ++ lH
      
      ⟨
        l,
        fun s =>
          match s with
          | State.goToSrc i =>
              let mem: State.goToSrc i ∈ lS.val :=
                List.has.toMem (lS.property i i.property)
              
              let eqL: l = lS.val ++ (lD0.val ++ lD1.val) ++ lH :=
                (List.append_assoc lS.val lD0.val lD1.val) ▸ rfl
              let eqR: lS.val ++ (lD0.val ++ lD1.val) ++ lH =
                lS.val ++ (lD0.val ++ lD1.val ++ lH)
              :=
                (List.append_assoc lS.val (lD0.val ++ lD1.val) lH)
              let eq := eqL.trans eqR
              
              List.has.fromMem
                (eq ▸ List.mem_append_of_mem_left (lD0.val ++ lD1.val ++ lH) mem)
          | State.goToDest0 i =>
              let mem: State.goToDest0 i ∈ lD0.val :=
                List.has.toMem (lD0.property i i.property)
              
              List.has.fromMem
                (List.mem_append_of_mem_left _
                  (List.mem_append_of_mem_left _
                    (List.mem_append_of_mem_right lS.val mem)))
          | State.goToDest1 i =>
              let mem: State.goToDest1 i ∈ lD1.val :=
                List.has.toMem (lD1.property i i.property)
              
              List.has.fromMem
                (List.mem_append_of_mem_left _
                  (List.mem_append_of_mem_right _ mem))
          | State.halt =>
              let mem: State.halt ∈ lH := List.Mem.head State.halt []
              let memL: State.halt ∈ l :=
                List.mem_append_of_mem_right (lS.val ++ lD0.val ++ lD1.val) mem
              List.has.fromMem memL
      ⟩
  end Assign
end Program
