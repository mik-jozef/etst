
inductive Truth3 where
| false
| true
| undetermined

structure Trisets where
  Set3: Type
  isIn: Set3 → Set3 → Truth3
  -- isExtensional: ∀ a b z: Set, (isIn z a ↔ isIn z b)
