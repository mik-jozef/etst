import Lake
open Lake DSL

-- (I forgot what it stands for.)
package Etst {}

lean_lib Logic.FO {}

lean_lib HM.Assign {}
lean_lib HM.Compile {}
lean_lib HM.Hamkins {}
lean_lib HM.Uhm {}

lean_lib Arities {}
lean_lib Chain {}
lean_lib EqSwappedUnusedVar {}
lean_lib ExampleWFCs {}
lean_lib ExprRulesOfInference {}
lean_lib PairFreeVars {}
lean_lib Interpretation {}
lean_lib ITTM {}
lean_lib LeN35 {}
lean_lib Lfp {}
lean_lib Operators {}
lean_lib Ordinal {}
lean_lib OrdMap {}
lean_lib Pair {}
lean_lib PairDepthDictOrder {}
lean_lib PairDictOrder {}
lean_lib PairDictOrderInstance {}
lean_lib PairExpr {}
lean_lib PartialOrder {}
lean_lib Pointwise {}
lean_lib Set3 {}
lean_lib Tuple {}
lean_lib UniDefList {}
lean_lib UniSet3 {}
lean_lib Utils {}
lean_lib Valuation {}
lean_lib Wfm {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
