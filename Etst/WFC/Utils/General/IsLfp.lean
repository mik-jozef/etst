import Mathlib.Order.FixedPoints


def IsLfp (Le: T → T → Prop) (f: T → T) :=
  let _: LE T := ⟨Le⟩
  IsLeast (Function.fixedPoints f)
