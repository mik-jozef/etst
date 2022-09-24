-- Things that I've written, now don't need, but want to keep
-- just in case.

instance: ParOrdLT (Set D) where
  irefl (s: Set D): ¬(s < s) := fun (ss: s < s) =>
    let sns: s ≠ s := ss.right;
    sns rfl
  
  antisymm (a b: Set D) := fun (ab: a < b) (ba: b < a) =>
    PartialOrder.antisymm a b ab.left ba.left
  
  trans (a b c: Set D) := fun (ab: a < b) (bc: b < c) =>
    And.intro
      (PartialOrder.trans a b c ab.left bc.left)
      fun acEq: a = c =>
        let ba: b < a := acEq ▸ bc; -- I do not know how "▸" works, but it works wonders!
        let abEq: a = b := PartialOrder.antisymm a b ab.left ba.left;
        ab.right abEq
