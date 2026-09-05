module

public import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Basic.NNReal.Defs

public section

open scoped Pointwise Indicator

variable {α : Type*}

namespace NNReal

@[simp, norm_cast] lemma coe_indicator_one (s : Set α) (x : α) : ↑(𝟭_[s, ℝ≥0] x) = 𝟭_[s, ℝ] x :=
  Set.map_indicator_one NNReal.toRealHom ..

@[simp] lemma coe_comp_indicator_one (s : Set α) : (↑) ∘ 𝟭_[s, ℝ≥0] = 𝟭_[s, ℝ] := by
  ext; exact coe_indicator_one ..

end NNReal
