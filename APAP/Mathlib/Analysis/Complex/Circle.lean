module

public import Mathlib.Analysis.Complex.Circle

public section

open Real

namespace Circle

lemma cos_eq_cos_of_exp_eq_exp {x y : ℝ} (h : exp x = exp y) : cos x = cos y := by
  simpa using congr(($h : ℂ).re)

lemma sin_eq_sin_of_exp_eq_exp {x y : ℝ} (h : exp x = exp y) : sin x = sin y := by
  simpa using congr(($h : ℂ).im)

end Circle
