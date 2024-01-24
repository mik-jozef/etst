import Lake
open Lake DSL

-- Boolean Set Theory
package Bst {}

lean_lib Logic.FO {}

lean_lib HM.Assign {}
lean_lib HM.Compile {}
lean_lib HM.Hamkins {}
lean_lib HM.Uhm {}

lean_lib Arities {}
lean_lib Bst {} -- TODO rename to Etst
lean_lib Chain {}
lean_lib Setun {}
lean_lib Fixpoint {} -- TODO delete
lean_lib Interpretation {}
lean_lib ITTM {}
lean_lib Lfp {}
lean_lib Operators {}
lean_lib Ordinal {}
lean_lib OrdMap {}
lean_lib PartialOrder {}
lean_lib Pointwise {}
lean_lib Set {}
lean_lib Set3 {}
lean_lib Tuple {}
lean_lib Valuation {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
