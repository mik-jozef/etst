import Lake
open Lake DSL

-- (I forgot what it stands for.)
package Etst {}

lean_lib HM.Assign {}
lean_lib HM.Compile {}
lean_lib HM.Hamkins {}
lean_lib HM.Uhm {}

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

lean_lib Utils.BasicUtils {}
lean_lib Utils.Chain {}
lean_lib Utils.DefListDefEq {}
lean_lib Utils.ExprIsFreeVar {}
lean_lib Utils.LeN37 {}
lean_lib Utils.Lfp {}
lean_lib Utils.Ordinal {}
lean_lib Utils.Pair {}
lean_lib Utils.PairDepthDictOrder {}
lean_lib Utils.PairDictOrder {}
lean_lib Utils.PairFreeVars {}
lean_lib Utils.PartialOrder {}
lean_lib Utils.Pointwise {}
lean_lib Utils.Set3 {}
lean_lib Utils.WellFoundedOfLeast {}

lean_lib Arities {}
lean_lib ExampleWFCs {}
lean_lib Expr {}
lean_lib ExprRulesOfInference {}
lean_lib Interpretation {}
lean_lib Operators {}
lean_lib Pair {}
lean_lib PairExpr {}
lean_lib Set3 {}
lean_lib Tuple {}
lean_lib Valuation {}
lean_lib Wfm {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
