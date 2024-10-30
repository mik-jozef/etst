import Lake
open Lake DSL

-- (I forgot what it stands for. (Extensional triset theory?))
package Etst {}

lean_lib HM.Assign {}
lean_lib HM.Compile {}
lean_lib HM.Hamkins {}
lean_lib HM.Uhm {}

lean_lib Trisets.Trisets {}

lean_lib UniSet3.Ch7_UniDefList {}
lean_lib UniSet3.Ch8_S00_Defs {}
lean_lib UniSet3.Ch8_S01_Nat {}
lean_lib UniSet3.Ch8_S02_DefEncoding {}
lean_lib UniSet3.Ch8_S03_PairDictLt {}
lean_lib UniSet3.Ch8_S04_PairOfDepth {}
lean_lib UniSet3.Ch8_S05_PairLt {}
lean_lib UniSet3.Ch8_S06_NthDefList {}
lean_lib UniSet3.Ch8_S07_IncrVarsExpr {}
lean_lib UniSet3.Ch8_S08_ShiftDefEncoding {}
lean_lib UniSet3.Ch8_S09_Append {}
lean_lib UniSet3.Ch8_S10_TheDefList {}
lean_lib UniSet3.Ch8_S11_GetBound {}
lean_lib UniSet3.Ch8_S12_DefListToEncoding {}
lean_lib UniSet3.Ch8_S13_TheInternalDefList {}
lean_lib UniSet3.Ch9_TheSet3 {}
lean_lib UniSet3.Ch10_S01_InternalExternalEquivalence {}

lean_lib Utils.AProofSystem {}
lean_lib Utils.BasicUtils {}
lean_lib Utils.CauseSatisfiesBoundVars {}
lean_lib Utils.Chain {}
lean_lib Utils.DefListDefEq {}
lean_lib Utils.ElimExternal {}
lean_lib Utils.ExprIsFreeVar {}
lean_lib Utils.InsInterp {}
lean_lib Utils.Interpretation {}
lean_lib Utils.IsStrongCause {}
lean_lib Utils.IsWeakCause {}
lean_lib Utils.LeN37 {}
lean_lib Utils.Lfp {}
lean_lib Utils.NopeInterp {}
lean_lib Utils.Operators {}
lean_lib Utils.Ordinal {}
lean_lib Utils.OutIntro4 {}
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
lean_lib WFC.Ch5_PairSalgebra {}
lean_lib WFC.Ch6_S0_AProofSystem {}
lean_lib WFC.Ch6_S1_AProofSystem {}
lean_lib WFC.Appx0_ExprRulesOfInference {}
lean_lib WFC.Appx1_SimplerSemantics {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
