/-
  Glorious 1700+ lines of code dedicated to proving that
  Program.assign is computable by a Hamkins machine. Fuck me.
-/

import old.Set
import old.HM.Hamkins

open Classical


namespace Program
  namespace Assign
    inductive State (srcAddress destAddress: Nat) where
      | goToSrc (n: ↑(srcAddress + 1))
      | goToDest0 (n: ↑(srcAddress + destAddress + 1))
      | goToDest1 (n: ↑(srcAddress + destAddress + 1))
      | halt
    
    def State.initial: State sa da := State.goToSrc ⟨0, Nat.succ_pos _⟩
    
    -- Ordered by number of steps till halts.
    def State.wfRel: (sA sB: State sadr dadr) → Prop
      | goToSrc a, goToSrc b => b.val < a.val
      | goToSrc _, goToDest0 _ => False
      | goToSrc _, goToDest1 _ => False
      | goToSrc _, halt => False
      
      | goToDest0 _, goToSrc _ => True
      | goToDest0 a, goToDest0 b =>
          b.val < a.val ∧ a.val ≤ dadr ∨ dadr ≤ a.val ∧ a.val < b.val
      | goToDest0 _, goToDest1 _ => False
      | goToDest0 _, halt => False
      
      | goToDest1 _, goToSrc _ => True
      | goToDest1 _, goToDest0 _ => False
      | goToDest1 a, goToDest1 b =>
          b.val < a.val ∧ a.val ≤ dadr ∨ dadr ≤ a.val ∧ a.val < b.val
      | goToDest1 _, halt => False
      
      | halt, goToSrc _ => True
      | halt, goToDest0 _ => True
      | halt, goToDest1 _ => True
      | halt, halt => False
    
    def accHalt:
      Acc State.wfRel (@State.halt sadr dadr)
    :=
      Acc.intro State.halt fun s wfLt =>
        match s with
        | State.goToSrc _ => False.elim wfLt
        | State.goToDest0 _ => False.elim wfLt
        | State.goToDest1 _ => False.elim wfLt
        | State.halt => False.elim wfLt
    
    def accDest0
      (n: { n: Nat // n < srcAddress + destAddress + 1 })
      (dist: Nat) -- Poor man's decreases_by
      (eqDist: dist = Nat.abs n destAddress)
    :
      Acc State.wfRel (State.goToDest0 n)
    :=
      Acc.intro (State.goToDest0 n) fun s wfLt =>
        match s with
        | State.goToSrc _ => False.elim wfLt
        | State.goToDest0 nOther =>
            let wfLtNow:
              n.val < nOther.val ∧ nOther.val ≤ destAddress ∨
                destAddress ≤ nOther.val ∧ nOther.val < n.val
            :=
              wfLt
            
            have: Nat.abs nOther destAddress < dist :=
              eqDist ▸ (n.val.isTotal destAddress).elim
                (fun nLtDest =>
                  let ⟨nLtOther, nOtherLeDest⟩:
                    n.val < nOther.val ∧ nOther ≤ destAddress
                  :=
                    wfLtNow.elim id
                      (fun r =>
                        let destLtN: destAddress < n :=
                          Nat.letTrans r.left r.right
                        Nat.ltAntisymm nLtDest destLtN)
                  
                  Nat.abs.ltle.rite nLtOther nOtherLeDest)
                (fun destLtNOrEq => destLtNOrEq.elim
                  (fun destLtN =>
                  let ⟨destLeOther, nOtherLtN⟩:
                    destAddress ≤ nOther.val ∧ nOther.val < n.val
                  :=
                    wfLtNow.elim
                      (fun l =>
                        let nLtDest: n < destAddress :=
                          Nat.lteTrans l.left l.right
                        Nat.ltAntisymm nLtDest destLtN)
                      id
                  
                  Nat.abs.symm n destAddress ▸
                    Nat.abs.symm nOther destAddress ▸
                    Nat.abs.lelt.left destLeOther nOtherLtN)
                  (fun eq =>
                    let nNeqDest: n < destAddress ∨ destAddress < n :=
                      wfLtNow.elim
                        (fun r => Or.inl (Nat.lteTrans r.left r.right))
                        (fun l => Or.inr (Nat.letTrans l.left l.right))
                    let nLtN: n.val < n :=
                      nNeqDest.elim
                        (fun nLt => by conv => rhs rw [eq] exact nLt)
                        (fun nGt => by conv => lhs rw [eq] exact nGt)
                    Nat.ltAntisymm nLtN nLtN))
            
            accDest0 nOther (Nat.abs nOther destAddress) rfl
        | State.goToDest1 _ => False.elim wfLt
        | State.halt => accHalt
      termination_by accDest0 _ _ n dist eqDist => dist
    
    def accDest1
      (n: { n: Nat // n < srcAddress + destAddress + 1 })
      (dist: Nat) -- Poor man's decreases_by (?)
      (eqDist: dist = Nat.abs n destAddress)
    :
      Acc State.wfRel (State.goToDest1 n)
    :=
      Acc.intro (State.goToDest1 n) fun s wfLt =>
        match s with
        | State.goToSrc _ => False.elim wfLt
        | State.goToDest0 _ => False.elim wfLt
        | State.goToDest1 nOther =>
            let wfLtNow:
              n.val < nOther.val ∧ nOther.val ≤ destAddress ∨
                destAddress ≤ nOther.val ∧ nOther.val < n.val
            :=
              wfLt
            
            have: Nat.abs nOther destAddress < dist :=
              eqDist ▸ (n.val.isTotal destAddress).elim
                (fun nLtDest =>
                  let ⟨nLtOther, nOtherLeDest⟩:
                    n.val < nOther.val ∧ nOther ≤ destAddress
                  :=
                    wfLtNow.elim id
                      (fun r =>
                        let destLtN: destAddress < n :=
                          Nat.letTrans r.left r.right
                        Nat.ltAntisymm nLtDest destLtN)
                  
                  Nat.abs.ltle.rite nLtOther nOtherLeDest)
                (fun destLtNOrEq => destLtNOrEq.elim
                  (fun destLtN =>
                  let ⟨destLeOther, nOtherLtN⟩:
                    destAddress ≤ nOther.val ∧ nOther.val < n.val
                  :=
                    wfLtNow.elim
                      (fun l =>
                        let nLtDest: n < destAddress :=
                          Nat.lteTrans l.left l.right
                        Nat.ltAntisymm nLtDest destLtN)
                      id
                  
                  Nat.abs.symm n destAddress ▸
                    Nat.abs.symm nOther destAddress ▸
                    Nat.abs.lelt.left destLeOther nOtherLtN)
                  (fun eq =>
                    let nNeqDest: n < destAddress ∨ destAddress < n :=
                      wfLtNow.elim
                        (fun r => Or.inl (Nat.lteTrans r.left r.right))
                        (fun l => Or.inr (Nat.letTrans l.left l.right))
                    let nLtN: n.val < n :=
                      nNeqDest.elim
                        (fun nLt => by conv => rhs rw [eq] exact nLt)
                        (fun nGt => by conv => lhs rw [eq] exact nGt)
                    Nat.ltAntisymm nLtN nLtN))
            
            accDest1 nOther (Nat.abs nOther destAddress) rfl
        | State.halt => accHalt
      termination_by accDest1 _ _ n dist eqDist => dist
    
    def accSrc
      {destAddress: Nat}
      (n: { n: Nat // n < srcAddress + 1 })
    :
      Acc State.wfRel (@State.goToSrc _ destAddress n)
    :=
      Acc.intro (State.goToSrc n) fun s wfLt =>
        match s with
        | State.goToSrc nOther =>
            have: srcAddress - nOther.val < srcAddress - n.val :=
              Nat.ltle.subLt wfLt (Nat.le_of_succ_le_succ nOther.property)
            accSrc nOther
        | State.goToDest0 n => accDest0 n (Nat.abs n.val destAddress) rfl
        | State.goToDest1 n => accDest1 n (Nat.abs n.val destAddress) rfl
        | State.halt => accHalt
      termination_by accSrc _ n => srcAddress - n
    
    instance State.wf: WellFoundedRelation (State sA dA) where
      rel := State.wfRel
      wf := ⟨fun state =>
        match state with
        | State.goToSrc n => accSrc n
        | State.goToDest0 n => accDest0 n (Nat.abs n.val dA) rfl
        | State.goToDest1 n => accDest1 n (Nat.abs n.val dA) rfl
        | State.halt => accHalt⟩
    
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
        [ State.initial ],
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
    
    def next.src {ub: Nat} {i: ↑(ub + 1)} (neq: i.val ≠ ub): ↑(ub + 1) := ⟨
      i + 1,
      (Nat.eq_or_lt_of_le i.property).elim
        (fun eq => False.elim (neq (Nat.noConfusion eq id)))
        id
    ⟩
    
    def next.src.eq {ub: Nat}
      {i0 i1: ↑(ub + 1)}
      (neq0: i0.val ≠ ub)
      (neq1: i1.val ≠ ub)
      (iEq: i0 = i1)
    :
      next.src neq0 = next.src neq1
    :=
      iEq ▸ rfl
    
    def next.destDir (i dAddr: Nat) :=
      if i = dAddr then
        Dir.none
      else if dAddr < i then
        Dir.left
      else
        Dir.right
    
    def next.destDir.noneEq
      (i dAddr: Nat)
      (eqLeft: next.destDir i dAddr = Dir.none)
    :
      i = dAddr
    :=
      (Nat.isTotalLt i dAddr).elim
        (fun lt =>
          let neq: i ≠ dAddr := fun eq => Nat.lt_irrefl i (eq ▸ lt)
          let ngt: dAddr ≮ i := fun gt => Nat.ltAntisymm gt lt
          let eqRite: next.destDir i dAddr = Dir.right :=
            (if_neg neq).trans (if_neg ngt)
          Dir.noConfusion (eqRite.symm.trans eqLeft))
        (fun geOrEq =>
          (geOrEq.elim
            (fun gt =>
              let neq: i ≠ dAddr := fun eq => Nat.lt_irrefl i (eq ▸ gt)
              let eqRite: next.destDir i dAddr = Dir.left :=
                (if_neg neq).trans (if_pos gt)
              Dir.noConfusion (eqRite.symm.trans eqLeft))
            id))
    
    def next.destDir.leftIGtAddr
      (i dAddr: Nat)
      (eqLeft: next.destDir i dAddr = Dir.left)
    :
      dAddr < i
    :=
      (Nat.isTotalLt i dAddr).elim
        (fun lt =>
              let neq: i ≠ dAddr := fun eq => Nat.lt_irrefl i (eq ▸ lt)
              let ngt: dAddr ≮ i := fun gt => Nat.ltAntisymm gt lt
              let eqRite: next.destDir i dAddr = Dir.right :=
                (if_neg neq).trans (if_neg ngt)
              Dir.noConfusion (eqRite.symm.trans eqLeft))
        (fun geOrEq =>
          (geOrEq.elim
            id
            (fun eq =>
              let eqNone: next.destDir i dAddr = Dir.none := (if_pos eq)
              Dir.noConfusion (eqNone.symm.trans eqLeft))))
    
    def next.destDir.riteILtAddr
      (i dAddr: Nat)
      (eqLeft: next.destDir i dAddr = Dir.right)
    :
      i < dAddr
    :=
      (Nat.isTotalLt i dAddr).elim id
        (fun geOrEq =>
          (geOrEq.elim
            (fun gt =>
              let neq: i ≠ dAddr := fun eq => Nat.lt_irrefl i (eq ▸ gt)
              let eqRite: next.destDir i dAddr = Dir.left :=
                (if_neg neq).trans (if_pos gt)
              Dir.noConfusion (eqRite.symm.trans eqLeft))
            (fun eq =>
              let eqNone: next.destDir i dAddr = Dir.none := (if_pos eq)
              Dir.noConfusion (eqNone.symm.trans eqLeft))))
    
    def next.destDir.leftIPos
      (i dAddr: Nat)
      (eqLeft: next.destDir i dAddr = Dir.left)
    :
      0 < i
    :=
      let geAddr := next.destDir.leftIGtAddr i dAddr eqLeft
      match h: dAddr with
      | 0 => h.symm ▸ geAddr
      | n+1 => Nat.lt_trans (Nat.succ_pos n) (h ▸ geAddr)
    
    def next.destAddr {sAddr dAddr: Nat} (i: ↑(sAddr + dAddr + 1)):
      ↑(sAddr + dAddr + 1)
    :=
      if h: i < dAddr then
        ⟨i + 1, Nat.add_lt_add_right (Nat.lt.addNatLeft h sAddr) 1⟩
      else
        ⟨
          i - 1,
          match h: i with
          | ⟨Nat.zero, prop⟩ => prop
          | ⟨Nat.succ n, _⟩ =>
            let iH := Nat.succ n
            let hVal: i.val = iH := congr rfl h
            let predLt: iH - 1 < iH := Nat.le.refl
            Nat.lt_trans predLt (hVal ▸ i.property)
        ⟩
    
    def next.destAddr.up {sAddr dAddr: Nat} {i: ↑(sAddr + dAddr + 1)}
      (iLt: i < dAddr)
    :
      next.destAddr i = i.val + 1
    :=
      congr rfl (dif_pos iLt)
    
    def next.destAddr.upLt {sAddr dAddr: Nat} {i: ↑(sAddr + dAddr + 1)}
      (iLt: i < dAddr)
    :
      i.val < next.destAddr i
    :=
      (next.destAddr.up iLt) ▸ Nat.le.refl
    
    def next.destAddr.down {sAddr dAddr: Nat} {i: ↑(sAddr + dAddr + 1)}
      (iGt: dAddr < i)
    :
      next.destAddr i = i.val - 1
    :=
      let notLt: ¬i < dAddr := fun iLt => Nat.ltAntisymm iGt iLt
      congr rfl (dif_neg notLt)
    
    def next.destAddr.downGt {sAddr dAddr: Nat} {i: ↑(sAddr + dAddr + 1)}
      (iGt: dAddr < i)
    :
      next.destAddr i < i.val
    :=
      (next.destAddr.down iGt) ▸ (Nat.pred_lt (Nat.not_eq_zero_of_lt iGt))
    
    
    def srcAddressDest
      {srcAddress destAddress: Nat}
    :
      ↑(srcAddress + destAddress + 1)
    := ⟨
      srcAddress,
      let srcLt: srcAddress < srcAddress + 1 := Nat.le.refl
      let ltWrongOrder := Nat.lt.addNatLeft srcLt destAddress
      (Nat.add_comm destAddress srcAddress) ▸ ltWrongOrder
    ⟩
    
    def hm.getMove (srcAddress destAddress: Nat):
      HamkinsMachine.GetMove (State srcAddress destAddress)
    :=
      fun state symbol =>
        match state with
        | State.goToSrc i => {
            state :=
              if h: i = srcAddress then
                match symbol with
                  | Two.zero => State.goToDest0 srcAddressDest
                  | Two.one => State.goToDest1 srcAddressDest
              else
                State.goToSrc (next.src h)
            symbol := symbol
            dir := if i = srcAddress then Dir.none else Dir.right
          }
        | State.goToDest0 i => {
            state :=
              if i = destAddress then
                State.halt
              else
                State.goToDest0 (next.destAddr i)
            symbol :=
              if i = destAddress then
                Two.zero
              else
                symbol
            dir := next.destDir i destAddress
          }
        | State.goToDest1 i => {
            state :=
              if i = destAddress then
                State.halt
              else
                State.goToDest1 (next.destAddr i)
            symbol :=
              if i = destAddress then
                Two.one
              else
                symbol
            dir := next.destDir i destAddress
          }
        | State.halt => {
            state := state
            symbol := symbol
            dir := Dir.none
          }
    
    def hm.getMove.eq.srcLt
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + 1))
      (iNeq: i.val ≠ srcAddress)
      (symbol: Two)
    :
      hm.getMove srcAddress destAddress (State.goToSrc i) symbol = {
        state := State.goToSrc (next.src iNeq)
        symbol := symbol
        dir := Dir.right
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToSrc i) symbol
      
      let stateEq: move.state = State.goToSrc (next.src iNeq) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := rfl
      let dirEq: move.dir = Dir.right := if_neg iNeq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.srcEq
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + 1))
      (iEq: i.val = srcAddress)
      (symbol: Two)
    :
      hm.getMove srcAddress destAddress (State.goToSrc i) symbol = {
        state :=
          match symbol with
          | Two.zero => State.goToDest0 srcAddressDest
          | Two.one => State.goToDest1 srcAddressDest
        symbol := symbol
        dir := Dir.none
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToSrc i) symbol
      
      let stateEq: move.state = 
        match symbol with
          | Two.zero => State.goToDest0 srcAddressDest
          | Two.one => State.goToDest1 srcAddressDest
      := dif_pos iEq
      let symbolEq: move.symbol = symbol := rfl
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest0Lt
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + destAddress + 1))
      (iNeq: i.val ≠ destAddress)
      (symbol: Two)
    :
      hm.getMove srcAddress destAddress (State.goToDest0 i) symbol = {
        state := State.goToDest0 (next.destAddr i)
        symbol := symbol
        dir := next.destDir i destAddress
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToDest0 i) symbol
      
      let stateEq: move.state = State.goToDest0 (next.destAddr i) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := dif_neg iNeq
      let dirEq: move.dir = next.destDir i destAddress := rfl
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest0Eq
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + destAddress + 1))
      (iEq: i.val = destAddress)
    :
      hm.getMove srcAddress destAddress (State.goToDest0 i) symbol = {
        state := State.halt
        symbol := Two.zero
        dir := Dir.none
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToDest0 i) symbol
      
      let stateEq: move.state = State.halt := dif_pos iEq
      let symbolEq: move.symbol = Two.zero := dif_pos iEq
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest1Lt
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + destAddress + 1))
      (iNeq: i.val ≠ destAddress)
      (symbol: Two)
    :
      hm.getMove srcAddress destAddress (State.goToDest1 i) symbol = {
        state := State.goToDest1 (next.destAddr i)
        symbol := symbol
        dir := next.destDir i destAddress
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToDest1 i) symbol
      
      let stateEq: move.state = State.goToDest1 (next.destAddr i) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := dif_neg iNeq
      let dirEq: move.dir = next.destDir i destAddress := rfl
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest1Eq
      (srcAddress destAddress: Nat)
      (i: ↑(srcAddress + destAddress + 1))
      (iEq: i.val = destAddress)
    :
      hm.getMove srcAddress destAddress (State.goToDest1 i) symbol = {
        state := State.halt
        symbol := Two.one
        dir := Dir.none
      }
    :=
      let move := hm.getMove srcAddress destAddress (State.goToDest1 i) symbol
      
      let stateEq: move.state = State.halt := dif_pos iEq
      let symbolEq: move.symbol = Two.one := dif_pos iEq
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    
    def hm (srcAddress destAddress: Nat): HamkinsMachine := {
      State := State srcAddress destAddress
      isFinite := State.isFinite
      
      initialState := State.initial
      haltState := State.halt
      limitState := State.halt
      
      getMove := hm.getMove srcAddress destAddress
      
      haltHalts := fun _ => rfl
    }
    
    def finalTape
      (srcAddress destAddress: Nat)
      (input: Nat2)
    :
      Nat2
    :=
      fun i => input (if i = destAddress then srcAddress else i)
    
    structure Invariant
      (srcAddress destAddress: Nat)
      (input: Nat2)
      (config: HamkinsMachine.Configuration (hm srcAddress destAddress))
    :
      Prop
    where
      (invSrc (i: _): config.state = State.goToSrc i →
          config.head = i ∧ config.tape = input)
      (invDest0 (i: _): config.state = State.goToDest0 i →
          config.head = i ∧ config.tape = input
          ∧ input srcAddress = Two.zero)
      (invDest1 (i: _): config.state = State.goToDest1 i →
          config.head = i ∧ config.tape = input
          ∧ input srcAddress = Two.one)
      (invHalt: config.state = State.halt →
        config.tape = (finalTape srcAddress destAddress input))
    
    structure InvariantNext
      (srcAddress destAddress: Nat)
      (input: Nat2)
      (config: HamkinsMachine.Configuration (hm srcAddress destAddress))
    :
      Prop
    where
      (invSrcLt (i: _):
        config.state = State.goToSrc i →
        (h: i.val ≠ srcAddress) →
          ((hm srcAddress destAddress).step config).state = State.goToSrc (next.src h))
      
      (invSrcEq0 (i: _):
        config.state = State.goToSrc i →
        i = srcAddress → config.tape config.head = Two.zero →
          ((hm srcAddress destAddress).step config).state = State.goToDest0 srcAddressDest)
      
      (invSrcEq1 (i: _):
        config.state = State.goToSrc i →
        i = srcAddress → config.tape config.head = Two.one →
          ((hm srcAddress destAddress).step config).state = State.goToDest1 srcAddressDest)
      
      (invDest0Lt (i: _):
        config.state = State.goToDest0 i →
        (h: i.val ≠ destAddress) →
          ((hm srcAddress destAddress).step config).state = State.goToDest0 (next.destAddr i))
      
      (invDest0Eq (i: _):
        config.state = State.goToDest0 i →
        i = destAddress →
          ((hm srcAddress destAddress).step config).state = State.halt)
      
      (invDest1Lt (i: _):
        config.state = State.goToDest1 i →
        (h: i.val ≠ destAddress) →
          ((hm srcAddress destAddress).step config).state = State.goToDest1 (next.destAddr i))
      
      (invDest1Eq (i: _):
        config.state = State.goToDest1 i →
        i = destAddress →
          ((hm srcAddress destAddress).step config).state = State.halt)
    
    /-
      This should be easier to work with. The casts shoudln't
      be necessary. Keeping for historical reasons. (A proof for
      finite ordinals in git history.)
    -/
    def invariant
      (srcAddress destAddress: Nat)
      (input: Nat2)
      (config: HamkinsMachine.Configuration (hm srcAddress destAddress))
    :
      Prop
    :=
      match config.state with
      | State.goToSrc i => config.head = i ∧ config.tape = input
      | State.goToDest0 i => config.head = i ∧ config.tape = input
          ∧ input srcAddress = Two.zero
      | State.goToDest1 i => config.head = i ∧ config.tape = input
          ∧ input srcAddress = Two.one
      | State.halt => config.tape = (finalTape srcAddress destAddress input)
    
    def invariantsHold.fin
      (srcAddress destAddress: Nat)
      (input: Nat2)
      (n: Ordinal)
      (nFin: n.isFinite)
    :
      And
        (Invariant srcAddress destAddress input ((hm srcAddress destAddress).stage input n))
        ((notLim: ¬n.isLimit) →
          let nPred := Ordinal.nLimit.pred n notLim
          InvariantNext srcAddress destAddress input
            ((hm srcAddress destAddress).stage input nPred))
    :=
      let stageN := (hm srcAddress destAddress).stage input n
      
      if h: n = Ordinal.zero then
        let eqZero := HamkinsMachine.stage.eq.zero (hm srcAddress destAddress) input
        
        let stateEq: stageN.state = State.initial :=
          show
            ((hm srcAddress destAddress).stage input n).state = State.initial
          from
            h ▸ (eqZero.stateEq)
        
        And.intro {
          invSrc := fun ii eq =>
            let iiEq: ii.val = 0 :=
              (State.noConfusion (stateEq.symm.trans eq))
              (fun eq => congr rfl eq.symm)
            h ▸ ⟨
              iiEq ▸ eqZero.headEq,
              eqZero.tapeEq
            ⟩
          invDest0 := fun ii eq =>
            False.elim (State.noConfusion (stateEq.symm.trans eq))
          invDest1 := fun ii eq =>
            False.elim (State.noConfusion (stateEq.symm.trans eq))
          invHalt := fun eq =>
            False.elim (State.noConfusion (stateEq.symm.trans eq))
        } fun notLimit => False.elim (notLimit (h ▸ Ordinal.zero.isLimit))
      else
        let notLim: ¬n.isLimit := Ordinal.isFinite.pos.notLimit nFin h
        let nPred := Ordinal.nLimit.pred n notLim
        let _nPred.lt := Ordinal.nLimit.pred.lt n notLim
        
        let hmSD := hm srcAddress destAddress
        let stageNPred := hmSD.stage input nPred
        
        let ih := invariantsHold.fin
          srcAddress destAddress input nPred (Ordinal.isFinite.pred nFin h)
        
        let ih.inv := ih.left
        
        let stageN.eq: stageN = hmSD.step stageNPred :=
          HamkinsMachine.stage.eq.step _ _ _ _
        
        let stageN.eq.state: stageN.state = (hmSD.step stageNPred).state :=
          congr rfl stageN.eq
        
        let stageN.eq.tape: stageN.tape = (hmSD.step stageNPred).tape :=
          congr rfl stageN.eq
        
        let stageN.eq.head: stageN.head = (hmSD.step stageNPred).head :=
          congr rfl stageN.eq
        
        match h: stageNPred.state with
          | State.goToSrc i =>
              let ⟨invEqHead, invEqTape⟩:
                stageNPred.head = i ∧ stageNPred.tape = input
              :=
                ih.inv.invSrc i h
              
              let stageNPred.eq:
                stageNPred = ⟨State.goToSrc i, input, i⟩
              :=
                HamkinsMachine.Configuration.eq h invEqTape invEqHead
              
              let move := hmSD.getMove (State.goToSrc i) (input i)
              
              if hh: i = srcAddress then
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state :=
                    match input i with
                      | Two.zero => State.goToDest0 srcAddressDest
                      | Two.one => State.goToDest1 srcAddressDest
                  symbol := input i
                  dir := Dir.none
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := i
                }
                let stepObj.tapeEq: stepObj.tape = input :=
                  funext fun n =>
                    if h: n = i then
                      (if_pos h).trans (h ▸ rfl)
                    else
                      if_neg h
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.srcEq srcAddress destAddress i hh (input i)
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToSrc i, input, i⟩
                    moveObj
                    move.eq.symm
                    i
                    rfl
                
                let stageN.eq0.state: stageN.state =
                  match input i with
                    | Two.zero => State.goToDest0 srcAddressDest
                    | Two.one => State.goToDest1 srcAddressDest
                :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq0.tape: stageN.tape = input :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                let stageN.eq0.head: stageN.head = i :=
                  stageN.eq.head.trans (congr rfl stepEq)
                
                match hhh: input i.val with
                | Two.zero =>
                    let stageN.eq.state0:
                      stageN.state = State.goToDest0 srcAddressDest
                    := stageN.eq0.state.trans (hhh ▸ rfl)
                    
                    And.intro {
                      invDest0 := fun ii eq =>
                        let iiEq: i.val = ii := hh.trans
                          (State.noConfusion (stageN.eq.state0.symm.trans eq)
                            (fun eq => show srcAddressDest = ii.val from congr rfl eq))
                        And.intro (iiEq ▸ stageN.eq0.head)
                          (And.intro stageN.eq0.tape (hh ▸ hhh))
                      
                      invSrc := fun ii eq =>
                        State.noConfusion (stageN.eq.state0.symm.trans eq)
                      invDest1 := fun ii eq =>
                        State.noConfusion (stageN.eq.state0.symm.trans eq)
                      invHalt := fun eq =>
                        State.noConfusion (stageN.eq.state0.symm.trans eq)
                    } fun _ => {
                      invSrcLt := fun ii eq iNeq =>
                        let iiEq: i.val = ii := State.noConfusion (h.symm.trans eq)
                          (fun eq => congr rfl eq)
                        False.elim (iNeq (iiEq.symm.trans hh))
                      invSrcEq0 := fun ii _ _ _ =>
                        stageN.eq.state ▸ stageN.eq.state0
                      invSrcEq1 := fun ii _ _
                        (ns: stageNPred.tape stageNPred.head = Two.one)
                      =>
                        let eq: stageNPred.tape stageNPred.head = Two.zero :=
                          invEqHead ▸ invEqTape ▸ hhh
                        Two.noConfusion (ns.symm.trans eq)
                      invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                    }
                | Two.one =>
                    let stageN.eq.state1:
                      stageN.state = State.goToDest1 srcAddressDest
                    := stageN.eq0.state.trans (hhh ▸ rfl)
                    
                    And.intro {
                      invDest1 := fun ii eq =>
                        let iiEq: i.val = ii := hh.trans
                          (State.noConfusion (stageN.eq.state1.symm.trans eq)
                            (fun eq => show srcAddressDest = ii.val from congr rfl eq))
                        And.intro (iiEq ▸ stageN.eq0.head)
                          (And.intro stageN.eq0.tape (hh ▸ hhh))
                      
                      invSrc := fun ii eq =>
                        State.noConfusion (stageN.eq.state1.symm.trans eq)
                      invDest0 := fun ii eq =>
                        State.noConfusion (stageN.eq.state1.symm.trans eq)
                      invHalt := fun eq =>
                        State.noConfusion (stageN.eq.state1.symm.trans eq)
                    } fun _ => {
                      invSrcLt := fun ii eq iNeq =>
                        let iiEq: i.val = ii := State.noConfusion (h.symm.trans eq)
                          (fun eq => congr rfl eq)
                        False.elim (iNeq (iiEq.symm.trans hh))
                      invSrcEq0 := fun ii _ _
                        (ns: stageNPred.tape stageNPred.head = Two.zero)
                      =>
                        let eq: stageNPred.tape stageNPred.head = Two.one :=
                          invEqHead ▸ invEqTape ▸ hhh
                        Two.noConfusion (ns.symm.trans eq)
                      invSrcEq1 := fun ii _ _ _ =>
                        stageN.eq.state ▸ stageN.eq.state1
                      invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                    }
              else
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state := State.goToSrc (next.src hh)
                  symbol := input i
                  dir := Dir.right
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := i + 1
                }
                let stepObj.tapeEq: stepObj.tape = input :=
                  funext fun n =>
                    if h: n = i then
                      (if_pos h).trans (h ▸ rfl)
                    else
                      if_neg h
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.srcLt srcAddress destAddress i hh (input i)
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToSrc i, input, i⟩
                    moveObj
                    move.eq.symm
                    (i + 1)
                    rfl
                
                let stageN.eq0.state: stageN.state = State.goToSrc (next.src hh) :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq0.tape: stageN.tape = input :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                And.intro {
                      invSrc := fun ii eq =>
                        let nextEq: next.src hh = ii :=
                          State.noConfusion
                            (stageN.eq0.state.symm.trans eq) id
                        let iSuccEq: i + 1 = ii.val :=
                          show (next.src hh).val = ii from congr rfl nextEq
                        
                        And.intro
                          (stageN.eq.head.trans (stepEq ▸ iSuccEq ▸ rfl))
                          stageN.eq0.tape
                      
                      invDest0 := fun ii eq => False.elim
                        (State.noConfusion (stageN.eq0.state.symm.trans eq))
                      invDest1 := fun ii eq => False.elim
                        (State.noConfusion (stageN.eq0.state.symm.trans eq))
                      invHalt := fun eq =>
                        let sd :=
                          (congr rfl stepEq).symm.trans (stageN.eq.state.symm.trans eq)
                        False.elim (State.noConfusion sd)
                    } fun _ => {
                      invSrcLt := fun ii eq iNeq =>
                        let iiEq := State.noConfusion (h.symm.trans eq)
                          id
                        let nextEq: next.src hh = next.src iNeq :=
                          next.src.eq hh iNeq iiEq
                        stageN.eq.state ▸ nextEq ▸ stageN.eq0.state
                      invSrcEq0 := fun ii eq iEq _ =>
                        let iiEq: i.val = ii :=
                          State.noConfusion (h.symm.trans eq)
                            (fun eq => congr rfl eq)
                        
                        False.elim (hh (iiEq.trans iEq))
                      invSrcEq1 := fun ii eq iEq _ =>
                        let iiEq: i.val = ii :=
                          State.noConfusion (h.symm.trans eq)
                            (fun eq => congr rfl eq)
                        
                        False.elim (hh (iiEq.trans iEq))
                      invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                      invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                    }
          | State.goToDest0 i =>
              let ⟨invHead, invTape, invSymbol⟩:
                stageNPred.head = i
                  ∧ stageNPred.tape = input
                  ∧ input srcAddress = Two.zero
              :=
                ih.inv.invDest0 i h
              
              let stageNPred.eq:
                stageNPred = ⟨State.goToDest0 i, input, i⟩
              :=
                HamkinsMachine.Configuration.eq h invTape invHead
              
              let move := hmSD.getMove (State.goToDest0 i) (input i)
              
              if hh: i = destAddress then
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state := State.halt
                  symbol := Two.zero
                  dir := Dir.none
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := i
                }
                let stepObj.tapeEq:
                  stepObj.tape = finalTape srcAddress destAddress input
                :=
                  funext fun n =>
                    if hhh: n = i then
                      let nEq: n = destAddress := hhh.trans hh
                      let finEq:
                        finalTape srcAddress destAddress input destAddress
                          = input srcAddress
                      :=
                        by unfold finalTape exact congr rfl (if_pos rfl)
                      (if_pos hhh).trans
                        (invSymbol.symm.trans (nEq ▸ finEq.symm))
                    else
                      let nNeq: n ≠ destAddress :=
                        fun eq => hhh (eq.trans hh.symm)
                      (if_neg hhh).trans (by
                        unfold finalTape;
                        exact congr rfl (if_neg nNeq).symm)
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.dest0Eq srcAddress destAddress i hh
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToDest0 i, input, i⟩
                    moveObj
                    move.eq.symm
                    i
                    rfl
                
                let stageN.eq0.state: stageN.state = State.halt :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq0.tape:
                  stageN.tape = finalTape srcAddress destAddress input
                :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                And.intro {
                  invSrc := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq0.state.symm.trans eq))
                  invDest0 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq0.state.symm.trans eq))
                  invDest1 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq0.state.symm.trans eq))
                  invHalt := fun _ => stageN.eq0.tape
                } fun _ => {
                  invSrcLt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq0 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq1 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Lt := fun ii eq iiNeq =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    False.elim (iiNeq (iEq ▸ hh))
                  invDest0Eq := fun ii _ _ => stepEq ▸ rfl
                  invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                }
              else
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state := State.goToDest0 (next.destAddr i)
                  symbol := input i
                  dir := next.destDir i destAddress
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := next.destAddr i
                }
                let stepObj.tapeEq: stepObj.tape = input :=
                  funext fun n =>
                    if h: n = i then
                      (if_pos h).trans (h ▸ rfl)
                    else
                      if_neg h
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.dest0Lt srcAddress destAddress i hh (input i)
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToDest0 i, input, i⟩
                    moveObj
                    move.eq.symm
                    (next.destAddr i)
                    (match h: moveObj.dir with
                      | Dir.left =>
                          let iPos := next.destDir.leftIPos i destAddress h
                          let iGt := next.destDir.leftIGtAddr i destAddress h
                          let iNLt: i.val ≮ destAddress :=
                            fun iLt => Nat.ltAntisymm iLt iGt
                          
                          match hh: i with
                          | ⟨0, _⟩ =>
                              let iValEq: i.val = 0 := congr rfl hh
                              False.elim (Nat.lt_irrefl 0 (iValEq ▸ iPos))
                          | ⟨ii+1, prop⟩ =>
                              show (next.destAddr ⟨ii+1, prop⟩).val = some ii
                              from congr rfl (congr rfl (dif_neg (hh ▸ iNLt)))
                      | Dir.right =>
                          let iLt := next.destDir.riteILtAddr i destAddress h
                          show some (next.destAddr i).val = some (i.val + 1) from
                              congr rfl (congr rfl (dif_pos iLt))
                      | Dir.none =>
                          let iEqDestAddr :=
                            next.destDir.noneEq i destAddress h
                          False.elim (hh iEqDestAddr))
                
                let stageN.eq.state:
                  stageN.state = State.goToDest0 (next.destAddr i)
                :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq.tape: stageN.tape = input :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                let stageN.eq.head: stageN.head = (next.destAddr i) :=
                  stageN.eq.head.trans (congr rfl stepEq)
                
                And.intro {
                  invSrc := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invDest0 := fun ii eq =>
                    let nextEq: next.destAddr i = ii :=
                      State.noConfusion (stageN.eq.state.symm.trans eq) id
                    nextEq ▸ ⟨stageN.eq.head, stageN.eq.tape, invSymbol⟩
                  invDest1 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invHalt := fun eq =>
                    let sd := stageN.eq.state.symm.trans eq
                    False.elim (State.noConfusion sd)
                } fun _ => {
                  invSrcLt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq0 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq1 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Lt := fun ii eq _ =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    stepEq ▸ iEq ▸ rfl
                  invDest0Eq := fun ii eq iiEq =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    False.elim (hh (iEq ▸ iiEq))
                  invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                }
          | State.goToDest1 i =>
              let ⟨invHead, invTape, invSymbol⟩:
                stageNPred.head = i
                  ∧ stageNPred.tape = input
                  ∧ input srcAddress = Two.one
              :=
                ih.inv.invDest1 i h
              
              let stageNPred.eq:
                stageNPred = ⟨State.goToDest1 i, input, i⟩
              :=
                HamkinsMachine.Configuration.eq h invTape invHead
              
              let move := hmSD.getMove (State.goToDest1 i) (input i)
              
              if hh: i = destAddress then
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state := State.halt
                  symbol := Two.one
                  dir := Dir.none
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := i
                }
                let stepObj.tapeEq:
                  stepObj.tape = finalTape srcAddress destAddress input
                :=
                  funext fun n =>
                    if hhh: n = i then
                      let nEq: n = destAddress := hhh.trans hh
                      let finEq:
                        finalTape srcAddress destAddress input destAddress
                          = input srcAddress
                      :=
                        by unfold finalTape exact congr rfl (if_pos rfl)
                      (if_pos hhh).trans
                        (invSymbol.symm.trans (nEq ▸ finEq.symm))
                    else
                      let nNeq: n ≠ destAddress :=
                        fun eq => hhh (eq.trans hh.symm)
                      (if_neg hhh).trans (by
                        unfold finalTape;
                        exact congr rfl (if_neg nNeq).symm)
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.dest1Eq srcAddress destAddress i hh
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToDest1 i, input, i⟩
                    moveObj
                    move.eq.symm
                    i
                    rfl
                
                let stageN.eq.state: stageN.state = State.halt :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq.tape:
                  stageN.tape = finalTape srcAddress destAddress input
                :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                And.intro {
                  invSrc := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invDest0 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invDest1 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invHalt := fun _ => stageN.eq.tape
                } fun _ => {
                  invSrcLt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq0 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq1 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest1Lt := fun ii eq iiNeq =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    False.elim (iiNeq (iEq ▸ hh))
                  invDest1Eq := fun ii _ _ => stepEq ▸ rfl
                }
              else
                let moveObj: HamkinsMachine.Move hmSD.State := {
                  state := State.goToDest1 (next.destAddr i)
                  symbol := input i
                  dir := next.destDir i destAddress
                }
                
                let stepObj: HamkinsMachine.Configuration (hmSD) := {
                  state := moveObj.state
                  tape := fun n =>
                    if n = i then moveObj.symbol else input n
                  head := next.destAddr i
                }
                let stepObj.tapeEq: stepObj.tape = input :=
                  funext fun n =>
                    if h: n = i then
                      (if_pos h).trans (h ▸ rfl)
                    else
                      if_neg h
                
                let move.eq: move = moveObj :=
                  hm.getMove.eq.dest1Lt srcAddress destAddress i hh (input i)
                
                let stepEq: hmSD.step stageNPred = stepObj :=
                  stageNPred.eq ▸ HamkinsMachine.step.eq.some
                    hmSD
                    ⟨State.goToDest1 i, input, i⟩
                    moveObj
                    move.eq.symm
                    (next.destAddr i)
                    (match h: moveObj.dir with
                      | Dir.left =>
                          let iPos := next.destDir.leftIPos i destAddress h
                          let iGt := next.destDir.leftIGtAddr i destAddress h
                          let iNLt: i.val ≮ destAddress :=
                            fun iLt => Nat.ltAntisymm iLt iGt
                          
                          match hh: i with
                          | ⟨0, _⟩ =>
                              let iValEq: i.val = 0 := congr rfl hh
                              False.elim (Nat.lt_irrefl 0 (iValEq ▸ iPos))
                          | ⟨ii+1, prop⟩ =>
                              show (next.destAddr ⟨ii+1, prop⟩).val = some ii
                              from congr rfl (congr rfl (dif_neg (hh ▸ iNLt)))
                      | Dir.right =>
                          let iLt := next.destDir.riteILtAddr i destAddress h
                          show some (next.destAddr i).val = some (i.val + 1) from
                              congr rfl (congr rfl (dif_pos iLt))
                      | Dir.none =>
                          let iEqDestAddr :=
                            next.destDir.noneEq i destAddress h
                          False.elim (hh iEqDestAddr))
                
                let stageN.eq.state:
                  stageN.state = State.goToDest1 (next.destAddr i)
                :=
                  stageN.eq.state.trans (congr rfl stepEq)
                
                let stageN.eq.tape: stageN.tape = input :=
                  stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
                
                let stageN.eq.head: stageN.head = (next.destAddr i) :=
                  stageN.eq.head.trans (congr rfl stepEq)
                
                And.intro {
                  invSrc := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invDest0 := fun ii eq => False.elim
                    (State.noConfusion (stageN.eq.state.symm.trans eq))
                  invDest1 := fun ii eq =>
                    let nextEq: next.destAddr i = ii :=
                      State.noConfusion (stageN.eq.state.symm.trans eq) id
                    nextEq ▸ ⟨stageN.eq.head, stageN.eq.tape, invSymbol⟩
                  invHalt := fun eq =>
                    let sd := stageN.eq.state.symm.trans eq
                    False.elim (State.noConfusion sd)
                } fun _ => {
                  invSrcLt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq0 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invSrcEq1 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                  invDest1Lt := fun ii eq _ =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    stepEq ▸ iEq ▸ rfl
                  invDest1Eq := fun ii eq iiEq =>
                    let iEq: i = ii :=
                      State.noConfusion (h.symm.trans eq) id
                    False.elim (hh (iEq ▸ iiEq))
                }
          | State.halt =>
              let invPred:
                stageNPred.tape = finalTape srcAddress destAddress input
              :=
                ih.inv.invHalt h
              
              let eq := HamkinsMachine.step.halt hmSD stageNPred h
              
              let stageN.eqPred: stageN = stageNPred := stageN.eq.trans eq
              
              let stageN.eq.state: stageN.state = State.halt :=
                stageN.eqPred ▸ h
              
              let stageN.eq.tape:
                stageN.tape = finalTape srcAddress destAddress input
              :=
                stageN.eqPred ▸ invPred
              
              And.intro {
                invSrc := fun ii eq => False.elim
                  (State.noConfusion (stageN.eq.state.symm.trans eq))
                invDest0 := fun ii eq => False.elim
                  (State.noConfusion (stageN.eq.state.symm.trans eq))
                invDest1 := fun ii eq => False.elim
                  (State.noConfusion (stageN.eq.state.symm.trans eq))
                invHalt := fun _ => stageN.eq.tape
              } fun _ => {
                invSrcLt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invSrcEq0 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invSrcEq1 := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invDest0Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invDest0Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invDest1Lt := fun _ eq _ => State.noConfusion (h.symm.trans eq)
                invDest1Eq := fun _ eq _ => State.noConfusion (h.symm.trans eq)
              }
    termination_by invariantsHold.fin srcAddress destAddress input n nFin => n
    
    structure TerminatesLow
      (srcAddress destAddress: Nat)
      (input: Nat2)
    where
      n: Ordinal
      isFinite: n.isFinite
      haltsAtN: HamkinsMachine.stage.haltsAt (hm srcAddress destAddress) input n
    
    noncomputable def hm.terminatesLow
      {srcAddress destAddress: Nat}
      {input: Nat2}
      
      (n: Ordinal)
      (nFin: n.isFinite)
      
      -- This is to prove termination
      (state: State srcAddress destAddress)
      (stateAt: ((hm srcAddress destAddress).stage input n).state = state)
      
    :
      TerminatesLow srcAddress destAddress input
    :=
      if hHalt: state = (hm srcAddress destAddress).haltState then
        {
          n := n
          isFinite := nFin
          haltsAtN :=
            by unfold HamkinsMachine.stage.haltsAt exact hHalt ▸ stateAt
        }
      else
        let succNotLim: ¬n.succ.isLimit := Ordinal.succ.notLimit
        
        let nSuccPred := Ordinal.nLimit.pred n.succ succNotLim
        let succPredEq: nSuccPred = n :=
          Ordinal.succ.inj nSuccPred.property
        
        let stageN := (hm srcAddress destAddress).stage input n
        let nextStage := (hm srcAddress destAddress).step ((hm srcAddress destAddress).stage input n)
        
        let nextState := nextStage.state
        
        let inv:
          InvariantNext srcAddress destAddress input ((hm srcAddress destAddress).stage input n)
        :=
          succPredEq ▸ (
            invariantsHold.fin srcAddress destAddress input n.succ nFin.succ
          ).right succNotLim
        
        have: State.wfRel nextState state :=
          match h: state with
          | State.goToSrc i =>
              if hAddr: i = srcAddress then
                match hSymbol: stageN.tape stageN.head with
                | Two.zero =>
                    let nextEq: nextState = State.goToDest0 srcAddressDest :=
                      inv.invSrcEq0 i stateAt hAddr hSymbol
                    
                    nextEq ▸ trivial
                | Two.one =>
                    let nextEq: nextState = State.goToDest1 srcAddressDest :=
                      inv.invSrcEq1 i stateAt hAddr hSymbol
                    
                    nextEq ▸ trivial
              else
                let nextEq: nextState = State.goToSrc (next.src hAddr) :=
                  inv.invSrcLt i stateAt hAddr
                
                nextEq ▸ Nat.le.refl
          | State.goToDest0 i =>
              if hAddr: i = destAddress then
                let nextEq: nextState = State.halt :=
                  inv.invDest0Eq i stateAt hAddr
                
                nextEq ▸ trivial
              else
                let nextEq:
                  nextState = State.goToDest0 (next.destAddr i)
                :=
                  inv.invDest0Lt i stateAt hAddr
                
                nextEq ▸ (i.val.isTotal destAddress).elim
                  (fun lt =>
                    Or.inl (And.intro
                      (next.destAddr.upLt lt)
                      (let eqSucc := next.destAddr.up lt
                      eqSucc ▸ lt)))
                  (fun gtOrEq =>
                    gtOrEq.elim
                      (fun gt => Or.inr (And.intro
                        (let eqPred := next.destAddr.down gt
                        eqPred ▸ Nat.le_pred_of_lt gt)
                        (next.destAddr.downGt gt)))
                      (fun eq => False.elim (hAddr eq)))
          | State.goToDest1 i =>
              if hAddr: i = destAddress then
                let nextEq: nextState = State.halt :=
                  inv.invDest1Eq i stateAt hAddr
                
                nextEq ▸ trivial
              else
                let nextEq:
                  nextState = State.goToDest1 (next.destAddr i)
                :=
                  inv.invDest1Lt i stateAt hAddr
                
                nextEq ▸ (i.val.isTotal destAddress).elim
                  (fun lt =>
                    Or.inl (And.intro
                      (next.destAddr.upLt lt)
                      (let eqSucc := next.destAddr.up lt
                      eqSucc ▸ lt)))
                  (fun gtOrEq =>
                    gtOrEq.elim
                      (fun gt => Or.inr (And.intro
                        (let eqPred := next.destAddr.down gt
                        eqPred ▸ Nat.le_pred_of_lt gt)
                        (next.destAddr.downGt gt)))
                      (fun eq => False.elim (hAddr eq)))
          | State.halt => False.elim (hHalt rfl)
        
        hm.terminatesLow
          n.succ
          (Ordinal.isFinite.succ nFin)
          nextState
          (congr rfl (HamkinsMachine.stage.eq.step.succ (hm srcAddress destAddress) input n))
    
    termination_by hm.terminatesLow n nFin state stateAt => state
    
    def hm.terminates (srcAddress destAddress: Nat) (input: Nat2):
      (hm srcAddress destAddress).halts input
    :=
      let eqZero := HamkinsMachine.stage.eq.zero (hm srcAddress destAddress) input
      
      let tl := hm.terminatesLow Ordinal.zero Ordinal.isFinite.zero
        State.initial eqZero.stateEq
      
      ⟨tl.n, tl.haltsAtN⟩
    
    def invariantsHold
      (srcAddress destAddress: Nat)
      (input: Nat2)
      (n: Ordinal)
    :
      And
        (Invariant srcAddress destAddress input ((hm srcAddress destAddress).stage input n))
        ((notLim: ¬n.isLimit) →
          let nPred := Ordinal.nLimit.pred n notLim
          InvariantNext srcAddress destAddress input
            ((hm srcAddress destAddress).stage input nPred))
    :=
      if hFin: n.isFinite then
        invariantsHold.fin srcAddress destAddress input n hFin
      else
        let eqZero := HamkinsMachine.stage.eq.zero (hm srcAddress destAddress) input
        
        let tl := hm.terminatesLow Ordinal.zero Ordinal.isFinite.zero
          State.initial eqZero.stateEq
        
        let tl.nLt: tl.n < n := Ordinal.isFinite.ltNotFin tl.isFinite hFin
        
        let haltsAtN := HamkinsMachine.stage.haltsAt.gt tl.haltsAtN tl.nLt
        
        let invTln := (
          invariantsHold.fin srcAddress destAddress input tl.n tl.isFinite
        ).left.invHalt tl.haltsAtN
        
        let tapeFinal := (finalTape srcAddress destAddress input)
        let tapeAtN := (HamkinsMachine.stage (hm srcAddress destAddress) input n).tape
        
        let haltsWithTln:
          HamkinsMachine.stage.haltsWith (hm srcAddress destAddress) input tapeFinal tl.n
        :=
          And.intro tl.haltsAtN invTln
        
        let haltsWithN:
          HamkinsMachine.stage.haltsWith (hm srcAddress destAddress) input tapeAtN n
        :=
          And.intro haltsAtN rfl
        
        And.intro {
          invSrc := fun _ eq => False.elim
            (State.noConfusion (eq.symm.trans haltsAtN))
          invDest0 := fun _ eq => False.elim
            (State.noConfusion (eq.symm.trans haltsAtN))
          invDest1 := fun _ eq => False.elim
            (State.noConfusion (eq.symm.trans haltsAtN))
          invHalt := fun _ =>
            HamkinsMachine.stage.haltsConsistent haltsWithN haltsWithTln
        } fun nNotLim =>
          let nPred := Ordinal.nLimit.pred n nNotLim
          
          let tl.nPredLt := Ordinal.notFinite.predGtFinite
            tl.isFinite hFin nPred.property
          
          let haltsAtNPred :=
            HamkinsMachine.stage.haltsAt.gt tl.haltsAtN tl.nPredLt
          
          {
            invSrcLt := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invSrcEq0 := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invSrcEq1 := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invDest0Lt := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invDest0Eq := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invDest1Lt := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
            invDest1Eq := fun _ eq _ => False.elim
              (State.noConfusion (eq.symm.trans haltsAtNPred))
          }
    
  end Assign
end Program
