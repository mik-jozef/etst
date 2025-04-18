/-
  The functions `minimal_of_well_founded` and
  `least_of_well_founded_total` return the minimal
  and least elements of a set, respectively, given
  a well-founded (and total) relation on the type.
  
  Parts of this file are adapted from
  `Mathlib/Order/OrderIsoNat.lean`.
-/

import Mathlib.Order.OrderIsoNat
import Utils.Chain

set_option linter.unusedVariables false


namespace well_founded_of_least
  def every_nonempty_has_least
    (ord: PartialOrder T)
  :=
    ∀ (s: Set T)
      {t: T}
      (not_empty: t ∈ s),
    ∃ t,
      iIsLeast ord.le s t
  
  def ex_lt_not_acc
    (ord: PartialOrder T)
  :
    ∀ x: { a // ¬Acc ord.lt a },
    ∃ y: { a // ¬Acc ord.lt a },
      ord.lt y x
  :=
    fun ⟨x, hx⟩ =>
      let ⟨y, ⟨not_acc, lt⟩⟩ :=
        RelEmbedding.exists_not_acc_lt_of_not_acc hx
      ⟨⟨y, not_acc⟩, lt⟩
  
  noncomputable def f
    (ord: PartialOrder T)
    (x: { a // ¬Acc ord.lt a })
  :
    { a // ¬Acc ord.lt a }
  :=
    (ex_lt_not_acc ord x).unwrap
  
  noncomputable def dec_seq
    (ord: PartialOrder T)
    (t: T)
    (not_acc: ¬Acc ord.lt t)
  :
    Nat → { a // ¬Acc ord.lt a }
  
  | Nat.zero => ⟨t, not_acc⟩
  | Nat.succ nPred => f ord (dec_seq ord t not_acc nPred)
  
  def dec_seq_0_eq_t: dec_seq ord t not_acc 0 = ⟨t, not_acc⟩ :=
    rfl
  
  def f_x_lt
    (ord: PartialOrder T)
    (x: { a // ¬Acc ord.lt a })
  :
    f ord x < x
  :=
    (ex_lt_not_acc ord x).unwrap.property
  
  def acc_of_no_decreasing_seq
    {ord: PartialOrder T}
    (nonempty_has_least: every_nonempty_has_least ord)
    (t: T)
  :
    Acc ord.lt t
  :=
    -- This should work:
    -- let ex_lt_not_acc:
    --   ∀ x: { a // ¬Acc ord.lt a },
    --   ∃ y: { a // ¬Acc ord.lt a },
    --     ord.lt y x
    -- :=
    --   fun ⟨x, hx⟩ =>
    --     let ⟨y, ⟨not_acc, lt⟩⟩ :=
    --       exists_not_acc_lt_of_not_acc hx
    --     ⟨⟨y, not_acc⟩, lt⟩
    -- 
    -- let f (x: { a // ¬Acc ord.lt a }): { a // ¬Acc ord.lt a } :=
    --   (ex_lt_not_acc x).unwrap
    -- 
    -- let f_x_lt (x: { a // ¬Acc ord.lt a }): ord.lt (f x) x :=
    --   (ex_lt_not_acc x).unwrap.property
    
    byContradiction fun not_acc =>
      -- let rec dec_seq: Nat → { a // ¬Acc ord.lt a }
      -- | Nat.zero => ⟨t, not_acc⟩
      -- | Nat.succ nPred => f (dec_seq nPred)
      -- 
      -- This should work
      -- let dec_seq_0_eq_t: dec_seq 0 = ⟨t, not_acc⟩ :=
      --   rfl
      
      let seq_elements: Set T :=
        { x | ∃ n, dec_seq ord t not_acc n = x }
      
      let least_seq_element :=
        (nonempty_has_least seq_elements ⟨Nat.zero, rfl⟩).unwrap
      
      let index := least_seq_element.property.isMember.unwrap
      
      let atIndex := dec_seq ord t not_acc index
      let atIndexSucc := dec_seq ord t not_acc index.val.succ
      
      let f_succ_index_lt: atIndexSucc.val < atIndex :=
        f_x_lt ord (dec_seq ord t not_acc index)
      
      let f_succ_index_ge: atIndex.val ≤ atIndexSucc :=
        index.property ▸
        least_seq_element.property.isLeMember
          ⟨index.val.succ, rfl⟩
      
      ord.leLtAntisymm f_succ_index_ge f_succ_index_lt
end well_founded_of_least

def well_founded_of_least
  (ord: PartialOrder T)
  (n_has_l: well_founded_of_least.every_nonempty_has_least ord)
:
  WellFounded ord.lt
:= ⟨
  well_founded_of_least.acc_of_no_decreasing_seq n_has_l
⟩

noncomputable def minimal_of_well_founded.acc
  {rel: T → T → Prop}
  (acc_t: Acc rel t)
  (s: Set T)
  (nonempty: t ∈ s)
:
  { t // IsMinimal rel s t }
:=
  let either:
    PSum
      { t // IsMinimal rel s t }
      (t ∉ s)
  :=
    acc_t.rec
      fun x lt_acc ih =>
        if h: ∃ tt, tt ∈ s ∧ rel tt x then
          let ⟨tt, tt_in_s, tt_lt_x⟩ := h.unwrap
          
          match ih tt tt_lt_x with
          | PSum.inl isMin => PSum.inl isMin
          | PSum.inr nin => False.elim (nin tt_in_s)
        else if hIn: x ∈ s then
          PSum.inl ⟨
            x,
            {
              isMember := hIn,
              isLeMember :=
                fun tt in_s is_lt => h ⟨tt, And.intro in_s is_lt⟩
            }
          ⟩
        else
          PSum.inr hIn
  
  match either with
  | PSum.inl isMin => isMin
  | PSum.inr nin => False.elim (nin nonempty)

noncomputable def minimal_of_well_founded
  {lt: T → T → Prop}
  (wf: WellFounded lt)
  (s: Set T)
  (nonempty: t ∈ s)
:
  { t // IsMinimal lt s t }
:=
  minimal_of_well_founded.acc (wf.1 t) s nonempty

noncomputable def least_of_well_founded_total
  {lt: T → T → Prop}
  (wf: WellFounded lt)
  (s: Set T)
  (nonempty: t ∈ s)
  (is_connected: IsConnected lt)
:
  { t // iIsLeast (fun a b => lt a b ∨ a = b) s t }
:=
  let ⟨t, isMinimal⟩ := minimal_of_well_founded wf s nonempty
  
  ⟨
    t,
    {
      isMember := isMinimal.isMember,
      isLeMember :=
        fun t_other in_s =>
          match is_connected t t_other with
          | IsComparable.IsLt t_lt => Or.inl t_lt
          | IsComparable.IsGt t_gt =>
            False.elim (isMinimal.isLeMember in_s t_gt)
          | IsComparable.IsEq t_eq =>
            Or.inr t_eq
    }
  ⟩
