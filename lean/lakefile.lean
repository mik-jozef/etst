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
lean_lib DefListDefEq {}
lean_lib ExampleWFCs {}
lean_lib ExprRulesOfInference {}
lean_lib PairFreeVars {}
lean_lib Interpretation {}
lean_lib ITTM {}
lean_lib LeN37 {}
lean_lib Lfp {}
lean_lib ExprIsFreeVar {}
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
lean_lib UniSet3.Append {}
lean_lib UniSet3.DefEncoding {}
lean_lib UniSet3.DefListToEncoding {}
lean_lib UniSet3.Defs {}
lean_lib UniSet3.ExprEncoding {}
lean_lib UniSet3.IncrVarsExpr {}
lean_lib UniSet3.Nat {}
lean_lib UniSet3.NextDef {}
lean_lib UniSet3.NthDefList {}
lean_lib UniSet3.PairDictLt {}
lean_lib UniSet3.PairLt {}
lean_lib UniSet3.PairOfDepth {}
lean_lib UniSet3.ShiftDefEncoding {}
lean_lib UniSet3.TheDefList {}
lean_lib UniSet3.TheSet3 {}
lean_lib UniSet3.UniDefList {}
lean_lib UniSet3.UniSet3 {}
lean_lib Utils {}
lean_lib Valuation {}
lean_lib WellFoundedOfLeast {}
lean_lib Wfm {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
