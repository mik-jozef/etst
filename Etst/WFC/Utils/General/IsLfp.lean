module
public import Mathlib.Order.FixedPoints


@[expose] public def IsLfp {T} (Le: T → T → Prop) (f: T → T) :=
  let _: LE T := ⟨Le⟩
  IsLeast (Function.fixedPoints f)
