/-
  Glorious 1000+ lines of code dedicated to proving that
  Program.assign is computable by a Hamkins machine. Fuck me.
  
  TODO update the number after this file is finished.
-/

import Set
import HM.Hamkins

open Classical


namespace Program
  namespace Assign
    inductive State (srcAddress destAddress: Nat) where
      | goToSrc (n: ↑(srcAddress + 1))
      | goToDest0 (n: ↑(srcAddress + destAddress + 1))
      | goToDest1 (n: ↑(srcAddress + destAddress + 1))
      | halt
    
    -- Ordered by number of steps till halts.
    @[reducible] def State.wfRel: (sA sB: State sadr dadr) → Prop
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
    
    def next.src {ub: Nat} (i: ↑(ub + 1)) (neq: i.val ≠ ub): ↑(ub + 1) := ⟨
      i + 1,
      (Nat.eq_or_lt_of_le i.property).elim
        (fun eq => False.elim (neq (Nat.noConfusion eq id)))
        id
    ⟩
    
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
    
    
    def srcAddressDest
      {layout: Layout}
      {src dest: layout.Location}
    :
      ↑(src.address + dest.address + 1)
    := ⟨
      src.address,
      let srcLt: src.address < src.address + 1 := Nat.le.refl
      let ltWrongOrder := Nat.lt.addNatLeft srcLt dest.address
      (Nat.add_comm dest.address src.address) ▸ ltWrongOrder
    ⟩
    
    def hm.getMove {layout: Layout} (src dest: layout.Location):
      HamkinsMachine.GetMove (State src.address dest.address)
    :=
      fun state symbol =>
        match state with
        | State.goToSrc i => {
            state :=
              if h: i = src.address then
                match symbol with
                  | Two.zero => State.goToDest0 srcAddressDest
                  | Two.one => State.goToDest1 srcAddressDest
              else
                State.goToSrc (next.src i h)
            symbol := symbol
            dir := if i = src.address then Dir.none else Dir.right
          }
        | State.goToDest0 i => {
            state :=
              if i = dest.address then
                State.halt
              else
                State.goToDest0 (next.destAddr i)
            symbol :=
              if i = dest.address then
                Two.zero
              else
                symbol
            dir := next.destDir i dest.address
          }
        | State.goToDest1 i => {
            state :=
              if i = dest.address then
                State.halt
              else
                State.goToDest1 (next.destAddr i)
            symbol :=
              if i = dest.address then
                Two.one
              else
                symbol
            dir := next.destDir i dest.address
          }
        | State.halt => {
            state := state
            symbol := symbol
            dir := Dir.none
          }
    
    def hm.getMove.eq.srcLt
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + 1))
      (iNeq: i.val ≠ src.address)
      (symbol: Two)
    :
      hm.getMove src dest (State.goToSrc i) symbol = {
        state := State.goToSrc (next.src i iNeq)
        symbol := symbol
        dir := Dir.right
      }
    :=
      let move := hm.getMove src dest (State.goToSrc i) symbol
      
      let stateEq: move.state = State.goToSrc (next.src i iNeq) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := rfl
      let dirEq: move.dir = Dir.right := if_neg iNeq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.srcEq
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + 1))
      (iEq: i.val = src.address)
      (symbol: Two)
    :
      hm.getMove src dest (State.goToSrc i) symbol = {
        state :=
          match symbol with
          | Two.zero => State.goToDest0 srcAddressDest
          | Two.one => State.goToDest1 srcAddressDest
        symbol := symbol
        dir := Dir.none
      }
    :=
      let move := hm.getMove src dest (State.goToSrc i) symbol
      
      let stateEq: move.state = 
        match symbol with
          | Two.zero => State.goToDest0 srcAddressDest
          | Two.one => State.goToDest1 srcAddressDest
      := dif_pos iEq
      let symbolEq: move.symbol = symbol := rfl
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest0Lt
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + dest.address + 1))
      (iNeq: i.val ≠ dest.address)
      (symbol: Two)
    :
      hm.getMove src dest (State.goToDest0 i) symbol = {
        state := State.goToDest0 (next.destAddr i)
        symbol := symbol
        dir := next.destDir i dest.address
      }
    :=
      let move := hm.getMove src dest (State.goToDest0 i) symbol
      
      let stateEq: move.state = State.goToDest0 (next.destAddr i) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := dif_neg iNeq
      let dirEq: move.dir = next.destDir i dest.address := rfl
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest0Eq
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + dest.address + 1))
      (iEq: i.val = dest.address)
    :
      hm.getMove src dest (State.goToDest0 i) symbol = {
        state := State.halt
        symbol := Two.zero
        dir := Dir.none
      }
    :=
      let move := hm.getMove src dest (State.goToDest0 i) symbol
      
      let stateEq: move.state = State.halt := dif_pos iEq
      let symbolEq: move.symbol = Two.zero := dif_pos iEq
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest1Lt
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + dest.address + 1))
      (iNeq: i.val ≠ dest.address)
      (symbol: Two)
    :
      hm.getMove src dest (State.goToDest1 i) symbol = {
        state := State.goToDest1 (next.destAddr i)
        symbol := symbol
        dir := next.destDir i dest.address
      }
    :=
      let move := hm.getMove src dest (State.goToDest1 i) symbol
      
      let stateEq: move.state = State.goToDest1 (next.destAddr i) := dif_neg iNeq
      let symbolEq: move.symbol = symbol := dif_neg iNeq
      let dirEq: move.dir = next.destDir i dest.address := rfl
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    def hm.getMove.eq.dest1Eq
      {layout: Layout}
      (src dest: layout.Location)
      (i: ↑(src.address + dest.address + 1))
      (iEq: i.val = dest.address)
    :
      hm.getMove src dest (State.goToDest1 i) symbol = {
        state := State.halt
        symbol := Two.one
        dir := Dir.none
      }
    :=
      let move := hm.getMove src dest (State.goToDest1 i) symbol
      
      let stateEq: move.state = State.halt := dif_pos iEq
      let symbolEq: move.symbol = Two.one := dif_pos iEq
      let dirEq: move.dir = Dir.none := if_pos iEq
      
      HamkinsMachine.Move.eq stateEq symbolEq dirEq
    
    
    def hm {layout: Layout} (src dest: layout.Location): HamkinsMachine := {
      State := State src.address dest.address
      isFinite := State.isFinite
      
      initialState := State.goToSrc ⟨0, Nat.succ_pos _⟩
      haltState := State.halt
      limitState := State.halt
      
      getMove := hm.getMove src dest
      
      haltHalts := fun _ => rfl
    }
    
    def finalTape
      {layout: Layout}
      (src dest: layout.Location)
      (initialTape: Nat2)
    :
      Nat2
    :=
      fun i => initialTape (if i = dest.address then src.address else i)
    
    def invariant
      {layout: Layout}
      (src dest: layout.Location)
      (initialTape: Nat2)
      (config: HamkinsMachine.Configuration (hm src dest))
    :
      Prop
    :=
      match config.state with
      | State.goToSrc i => config.head = i ∧ config.tape = initialTape
      | State.goToDest0 i => config.head = i ∧ config.tape = initialTape
          ∧ initialTape src.address = Two.zero
      | State.goToDest1 i => config.head = i ∧ config.tape = initialTape
          ∧ initialTape src.address = Two.one
      | State.halt => config.tape = (finalTape src dest initialTape)
    
    def invariantHolds.fin
      {layout: Layout}
      (src dest: layout.Location)
      (initialTape: Nat2)
      (n: Ordinal)
      (nFin: n.isFinite)
    :
      invariant src dest initialTape ((hm src dest).stage initialTape n)
    :=
      let stageN := (hm src dest).stage initialTape n
      
      let notLim: ¬n.isLimit := Ordinal.isFinite.notLimit nFin
      let nPred := Ordinal.nLimit.pred n notLim
      let _nPred.lt := Ordinal.nLimit.pred.lt n notLim
      
      let hmSD := hm src dest
      let stageNPred := hmSD.stage initialTape nPred
      
      let ih := invariantHolds.fin
        src dest initialTape nPred (Ordinal.isFinite.pred nFin)
      
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
            let invPred:
              stageNPred.head = i ∧ stageNPred.tape = initialTape
            :=
              -- In Lyo, `invPred.eq` should not be necessary.
              let invPred.eq:
                invariant src dest initialTape stageNPred =
                  (stageNPred.head = i ∧ stageNPred.tape = initialTape)
              :=
                by conv => lhs unfold invariant rw [h] rfl
              invPred.eq ▸ ih
            
            let stageNPred.eq:
              stageNPred = ⟨State.goToSrc i, initialTape, i⟩
            :=
              HamkinsMachine.Configuration.eq h (invPred.right) (invPred.left)
            
            let move := hmSD.getMove (State.goToSrc i) (initialTape i)
            
            if hh: i = src.address then
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state :=
                  match initialTape i with
                    | Two.zero => State.goToDest0 srcAddressDest
                    | Two.one => State.goToDest1 srcAddressDest
                symbol := initialTape i
                dir := Dir.none
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := i
              }
              let stepObj.tapeEq: stepObj.tape = initialTape :=
                funext fun n =>
                  if h: n = i then
                    (if_pos h).trans (h ▸ rfl)
                  else
                    if_neg h
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.srcEq src dest i hh (initialTape i)
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToSrc i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  i
                  rfl
              
              let stageN.eq.state: stageN.state =
                match initialTape i with
                  | Two.zero => State.goToDest0 srcAddressDest
                  | Two.one => State.goToDest1 srcAddressDest
              :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape: stageN.tape = initialTape :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let stageN.eq.head: stageN.head = i :=
                stageN.eq.head.trans (congr rfl stepEq)
              
              match hhh: initialTape i.val with
              | Two.zero =>
                  let stageN.eq.state0:
                    stageN.state = State.goToDest0 srcAddressDest
                  := stageN.eq.state.trans (hhh ▸ rfl)
                  
                  let inv.eq:
                    invariant src dest initialTape stageN =
                      (stageN.head = srcAddressDest
                        ∧ stageN.tape = initialTape
                        ∧ initialTape src.address = Two.zero)
                  :=
                    by conv => lhs unfold invariant rw [stageN.eq.state0] rfl
                  
                  inv.eq ▸ And.intro
                    (stageN.eq.head.trans hh)
                    (And.intro stageN.eq.tape (hh ▸ hhh))
              | Two.one =>
                  let stageN.eq.state0:
                    stageN.state = State.goToDest1 srcAddressDest
                  := stageN.eq.state.trans (hhh ▸ rfl)
                  
                  let inv.eq:
                    invariant src dest initialTape stageN =
                      (stageN.head = srcAddressDest
                        ∧ stageN.tape = initialTape
                        ∧ initialTape src.address = Two.one)
                  :=
                    by conv => lhs unfold invariant rw [stageN.eq.state0] rfl
                  
                  inv.eq ▸ And.intro
                    (stageN.eq.head.trans hh)
                    (And.intro stageN.eq.tape (hh ▸ hhh))
            else
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state := State.goToSrc (next.src i hh)
                symbol := initialTape i
                dir := Dir.right
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := i + 1
              }
              let stepObj.tapeEq: stepObj.tape = initialTape :=
                funext fun n =>
                  if h: n = i then
                    (if_pos h).trans (h ▸ rfl)
                  else
                    if_neg h
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.srcLt src dest i hh (initialTape i)
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToSrc i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  (i + 1)
                  rfl
              
              let stageN.eq.state: stageN.state = State.goToSrc (next.src i hh) :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape: stageN.tape = initialTape :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let stageN.eq.head: stageN.head = i + 1 :=
                stageN.eq.head.trans (congr rfl stepEq)
              
              let inv.eq:
                invariant src dest initialTape stageN =
                  (stageN.head = (next.src i hh) ∧ stageN.tape = initialTape)
              :=
                by conv => lhs unfold invariant rw [stageN.eq.state] rfl
              
              inv.eq ▸ stageN.eq.tape ▸ stageN.eq.head ▸ And.intro rfl rfl
        | State.goToDest0 i =>
            let invPred:
              stageNPred.head = i
                ∧ stageNPred.tape = initialTape
                ∧ initialTape src.address = Two.zero
            :=
              let invPred.eq:
                invariant src dest initialTape stageNPred =
                  (stageNPred.head = i
                    ∧ stageNPred.tape = initialTape
                    ∧ initialTape src.address = Two.zero)
              :=
                by conv => lhs unfold invariant rw [h] rfl
              invPred.eq ▸ ih
            
            let stageNPred.eq:
              stageNPred = ⟨State.goToDest0 i, initialTape, i⟩
            :=
              HamkinsMachine.Configuration.eq
                h (invPred.right.left) (invPred.left)
            
            let move := hmSD.getMove (State.goToDest0 i) (initialTape i)
            
            if hh: i = dest.address then
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state := State.halt
                symbol := Two.zero
                dir := Dir.none
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := i
              }
              let stepObj.tapeEq:
                stepObj.tape = finalTape src dest initialTape
              :=
                funext fun n =>
                  if hhh: n = i then
                    let nEq: n = dest.address := hhh.trans hh
                    let finEq:
                      finalTape src dest initialTape dest.address
                        = initialTape src.address
                    :=
                      by unfold finalTape exact congr rfl (if_pos rfl)
                    (if_pos hhh).trans
                      (nEq ▸ (invPred.right.right.symm.trans finEq.symm))
                  else
                    let nNeq: n ≠ dest.address :=
                      fun eq => hhh (eq.trans hh.symm)
                    (if_neg hhh).trans (by
                      unfold finalTape;
                      exact congr rfl (if_neg nNeq).symm)
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.dest0Eq src dest i hh
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToDest0 i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  i
                  rfl
              
              let stageN.eq.state: stageN.state = State.halt :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape:
                stageN.tape = finalTape src dest initialTape
              :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let inv.eq:
                invariant src dest initialTape stageN =
                  (stageN.tape = finalTape src dest initialTape)
              :=
                by conv => lhs unfold invariant rw [stageN.eq.state] rfl
              
              inv.eq ▸ stageN.eq.tape
            else
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state := State.goToDest0 (next.destAddr i)
                symbol := initialTape i
                dir := next.destDir i dest.address
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := next.destAddr i
              }
              let stepObj.tapeEq: stepObj.tape = initialTape :=
                funext fun n =>
                  if h: n = i then
                    (if_pos h).trans (h ▸ rfl)
                  else
                    if_neg h
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.dest0Lt src dest i hh (initialTape i)
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToDest0 i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  (next.destAddr i)
                  (match h: moveObj.dir with
                    | Dir.left =>
                        let iPos := next.destDir.leftIPos i dest.address h
                        let iGt := next.destDir.leftIGtAddr i dest.address h
                        let iNLt: i.val ≮ dest.address :=
                          fun iLt => Nat.ltAntisymm iLt iGt
                        
                        match hh: i with
                        | ⟨0, _⟩ =>
                            let iValEq: i.val = 0 := congr rfl hh
                            False.elim (Nat.lt_irrefl 0 (iValEq ▸ iPos))
                        | ⟨ii+1, prop⟩ =>
                            show (next.destAddr ⟨ii+1, prop⟩).val = some ii
                            from congr rfl (congr rfl (dif_neg (hh ▸ iNLt)))
                    | Dir.right =>
                        let iLt := next.destDir.riteILtAddr i dest.address h
                        show some (next.destAddr i).val = some (i.val + 1) from
                            congr rfl (congr rfl (dif_pos iLt))
                    | Dir.none =>
                        let iEqDestAddr :=
                          next.destDir.noneEq i dest.address h
                        False.elim (hh iEqDestAddr))
              
              let stageN.eq.state:
                stageN.state = State.goToDest0 (next.destAddr i)
              :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape: stageN.tape = initialTape :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let stageN.eq.head: stageN.head = (next.destAddr i) :=
                stageN.eq.head.trans (congr rfl stepEq)
              
              let inv.eq:
                invariant src dest initialTape stageN =
                  (stageN.head = (next.destAddr i)
                    ∧ stageN.tape = initialTape
                    ∧ initialTape src.address = Two.zero)
              :=
                by conv => lhs unfold invariant rw [stageN.eq.state] rfl
              
              inv.eq ▸ stageN.eq.head ▸ And.intro
                rfl (And.intro (stageN.eq.tape ▸ rfl) invPred.right.right)
        | State.goToDest1 i =>
            let invPred:
              stageNPred.head = i
                ∧ stageNPred.tape = initialTape
                ∧ initialTape src.address = Two.one
            :=
              let invPred.eq:
                invariant src dest initialTape stageNPred =
                  (stageNPred.head = i
                    ∧ stageNPred.tape = initialTape
                    ∧ initialTape src.address = Two.one)
              :=
                by conv => lhs unfold invariant rw [h] rfl
              invPred.eq ▸ ih
            
            let stageNPred.eq:
              stageNPred = ⟨State.goToDest1 i, initialTape, i⟩
            :=
              HamkinsMachine.Configuration.eq
                h (invPred.right.left) (invPred.left)
            
            let move := hmSD.getMove (State.goToDest1 i) (initialTape i)
            
            if hh: i = dest.address then
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state := State.halt
                symbol := Two.one
                dir := Dir.none
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := i
              }
              let stepObj.tapeEq:
                stepObj.tape = finalTape src dest initialTape
              :=
                funext fun n =>
                  if hhh: n = i then
                    let nEq: n = dest.address := hhh.trans hh
                    let finEq:
                      finalTape src dest initialTape dest.address
                        = initialTape src.address
                    :=
                      by unfold finalTape exact congr rfl (if_pos rfl)
                    (if_pos hhh).trans
                      (nEq ▸ (invPred.right.right.symm.trans finEq.symm))
                  else
                    let nNeq: n ≠ dest.address :=
                      fun eq => hhh (eq.trans hh.symm)
                    (if_neg hhh).trans (by
                      unfold finalTape;
                      exact congr rfl (if_neg nNeq).symm)
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.dest1Eq src dest i hh
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToDest1 i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  i
                  rfl
              
              let stageN.eq.state: stageN.state = State.halt :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape:
                stageN.tape = finalTape src dest initialTape
              :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let inv.eq:
                invariant src dest initialTape stageN =
                  (stageN.tape = finalTape src dest initialTape)
              :=
                by conv => lhs unfold invariant rw [stageN.eq.state] rfl
              
              inv.eq ▸ stageN.eq.tape
            else
              let moveObj: HamkinsMachine.Move hmSD.State := {
                state := State.goToDest1 (next.destAddr i)
                symbol := initialTape i
                dir := next.destDir i dest.address
              }
              
              let stepObj: HamkinsMachine.Configuration (hmSD) := {
                state := moveObj.state
                tape := fun n =>
                  if n = i then moveObj.symbol else initialTape n
                head := next.destAddr i
              }
              let stepObj.tapeEq: stepObj.tape = initialTape :=
                funext fun n =>
                  if h: n = i then
                    (if_pos h).trans (h ▸ rfl)
                  else
                    if_neg h
              
              let move.eq: move = moveObj :=
                hm.getMove.eq.dest1Lt src dest i hh (initialTape i)
              
              let stepEq: hmSD.step stageNPred = stepObj :=
                stageNPred.eq ▸ HamkinsMachine.step.eq.some
                  hmSD
                  ⟨State.goToDest1 i, initialTape, i⟩
                  moveObj
                  move.eq.symm
                  (next.destAddr i)
                  (match h: moveObj.dir with
                    | Dir.left =>
                        let iPos := next.destDir.leftIPos i dest.address h
                        let iGt := next.destDir.leftIGtAddr i dest.address h
                        let iNLt: i.val ≮ dest.address :=
                          fun iLt => Nat.ltAntisymm iLt iGt
                        
                        match hh: i with
                        | ⟨0, _⟩ =>
                            let iValEq: i.val = 0 := congr rfl hh
                            False.elim (Nat.lt_irrefl 0 (iValEq ▸ iPos))
                        | ⟨ii+1, prop⟩ =>
                            show (next.destAddr ⟨ii+1, prop⟩).val = some ii
                            from congr rfl (congr rfl (dif_neg (hh ▸ iNLt)))
                    | Dir.right =>
                        let iLt := next.destDir.riteILtAddr i dest.address h
                        show some (next.destAddr i).val = some (i.val + 1) from
                            congr rfl (congr rfl (dif_pos iLt))
                    | Dir.none =>
                        let iEqDestAddr :=
                          next.destDir.noneEq i dest.address h
                        False.elim (hh iEqDestAddr))
              
              let stageN.eq.state:
                stageN.state = State.goToDest1 (next.destAddr i)
              :=
                stageN.eq.state.trans (congr rfl stepEq)
              
              let stageN.eq.tape: stageN.tape = initialTape :=
                stageN.eq.tape.trans (stepObj.tapeEq ▸ congr rfl stepEq)
              
              let stageN.eq.head: stageN.head = (next.destAddr i) :=
                stageN.eq.head.trans (congr rfl stepEq)
              
              let inv.eq:
                invariant src dest initialTape stageN =
                  (stageN.head = (next.destAddr i)
                    ∧ stageN.tape = initialTape
                    ∧ initialTape src.address = Two.one)
              :=
                by conv => lhs unfold invariant rw [stageN.eq.state] rfl
              
              inv.eq ▸ stageN.eq.head ▸ And.intro
                rfl (And.intro (stageN.eq.tape ▸ rfl) invPred.right.right)
        | State.halt =>
            let invPred:
              stageNPred.tape = finalTape src dest initialTape
            :=
              let invPred.eq:
                invariant src dest initialTape stageNPred =
                  (stageNPred.tape = finalTape src dest initialTape)
              :=
                by conv => lhs unfold invariant rw [h] rfl
              invPred.eq ▸ ih
            
            let eq := HamkinsMachine.step.halt hmSD stageNPred h
            
            let stageN.eqPred: stageN = stageNPred := stageN.eq.trans eq
            
            let stageN.eq.state: stageN.state = State.halt :=
              stageN.eqPred ▸ h
            
            let stageN.eq.tape:
              stageN.tape = finalTape src dest initialTape
            :=
              stageN.eqPred ▸ invPred
            
            let inv.eq:
              invariant src dest initialTape stageN =
                (stageN.tape = finalTape src dest initialTape)
            :=
              by conv => lhs unfold invariant rw [stageN.eq.state] rfl
            
            inv.eq ▸ stageN.eq.tape
    termination_by invariantHolds.fin src dest initialTape n nFin => n
    
    structure TerminatesLow
      {l: Layout}
      (src dest: l.Location)
      (input: Nat2)
    where
      n: Ordinal
      isFinite: n.isFinite
      haltsAtN: HamkinsMachine.stage.haltsAt (hm src dest) input n
    
    noncomputable def hm.terminatesLow
      {l: Layout}
      {src dest: l.Location}
      {input: Nat2}
      
      (n: Ordinal)
      (nFin: n.isFinite)
      
      (state: State src.address dest.address)
      (stateAt: ((hm src dest).stage input n).state = state)
      
    :
      TerminatesLow src dest input
    :=
      if h: state = (hm src dest).haltState then
        {
          n := n
          isFinite := nFin
          haltsAtN :=
            by unfold HamkinsMachine.stage.haltsAt exact h ▸ stateAt
        }
      else
        let stageN := (hm src dest).stage input n
        
        let nextState :=
          ((hm src dest).step ((hm src dest).stage input n)).state
        
        have: State.wfRel nextState state :=
          match state with
          | State.goToSrc i =>
              let inv: stageN.head = i ∧ stageN.tape = input :=
                let inv.eq:
                  invariant src dest input stageN =
                    (stageN.head = i ∧ stageN.tape = input)
                :=
                  by conv => lhs unfold invariant rw [stateAt] rfl
                inv.eq ▸ invariantHolds.fin src dest input n nFin
              
              
              
              sorry
          | State.goToDest0 i => sorry
          | State.goToDest1 i => sorry
          | State.halt => False.elim (h rfl)
        
        hm.terminatesLow
          n.succ
          (Ordinal.isFinite.succ nFin)
          nextState
          (congr rfl (HamkinsMachine.stage.eq.step.succ (hm src dest) input n))
    
    termination_by hm.terminatesLow n nFin state stateAt => state
    
    def hm.terminates {l: Layout} (src dest: l.Location) (input: Nat2):
      (hm src dest).halts input
    :=
      sorry
    
    def invariantHolds
      {layout: Layout}
      (src dest: layout.Location)
      (initialTape: Nat2)
      (n: Ordinal)
    :
      invariant src dest initialTape ((hm src dest).stage initialTape n)
    :=
      sorry
    
  end Assign
end Program
