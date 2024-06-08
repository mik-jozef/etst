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
lean_lib Utils.Interpretation {}
lean_lib Utils.LeN37 {}
lean_lib Utils.Lfp {}
lean_lib Utils.Operators {}
lean_lib Utils.Ordinal {}
lean_lib Utils.Pair {}
lean_lib Utils.PairDepthDictOrder {}
lean_lib Utils.PairDictOrder {}
lean_lib Utils.PairExpr {}
lean_lib Utils.PairFreeVars {}
lean_lib Utils.PartialOrder {}
lean_lib Utils.Pointwise {}
lean_lib Utils.Set3 {}
lean_lib Utils.Tuple {}
lean_lib Utils.Valuation {}
lean_lib Utils.WellFoundedOfLeast {}

lean_lib WFC.Ch0_Set3 {}
lean_lib WFC.Ch1_Expr {}
lean_lib WFC.Ch2_Valuation {}
lean_lib WFC.Ch3_Interpretation {}
lean_lib WFC.Ch4_Operators {}
lean_lib WFC.Appx0_ExprRulesOfInference {}
lean_lib WFC.ExampleWFCs {}
lean_lib WFC.Pair {}
lean_lib WFC.Wfm {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
