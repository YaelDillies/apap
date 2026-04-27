module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Complex

namespace Circle

@[simp] lemma arg_eq_zero {z : Circle} : arg z = 0 ↔ z = 1 := by simpa using arg_eq_arg (w := 1)

end Circle
