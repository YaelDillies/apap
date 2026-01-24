import LeanAPAP.Prereqs.Function.Indicator.Defs
import LeanAPAP.Prereqs.LpNorm.Discrete.Defs
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Star.Conjneg

/-!
# Lp norms
-/

open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal translate mu

namespace MeasureTheory
variable {ι G 𝕜 E R : Type*} [Finite ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-! ### Indicator -/

section Indicator
variable [RCLike R] [DecidableEq ι] {s : Finset ι} {p : ℝ≥0}

lemma dLpNorm_rpow_indicate (hp : p ≠ 0) (s : Finset ι) : ‖𝟭_[R] s‖_[p] ^ (p : ℝ) = #s := by
  cases nonempty_fintype ι
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [dLpNorm_rpow_eq_sum_nnnorm, hp, indicate_apply, apply_ite nnnorm, -sum_const,
    card_eq_sum_ones]

lemma dLpNorm_indicate (hp : p ≠ 0) (s : Finset ι) : ‖𝟭_[R] s‖_[p] = #s ^ (p⁻¹ : ℝ) := by
  refine (NNReal.eq_rpow_inv_iff ?_).2 (dLpNorm_rpow_indicate ?_ _) <;> positivity

lemma dLpNorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[R] s‖_[p] ^ (p : ℝ) = #s := by
  simpa using dLpNorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

lemma dL2Norm_sq_indicate (s : Finset ι) : ‖𝟭_[R] s‖_[2] ^ 2 = #s := by
  simpa using dLpNorm_pow_indicate two_ne_zero s

@[simp] lemma dL2Norm_indicate (s : Finset ι) : ‖𝟭_[R] s‖_[2] = NNReal.sqrt #s := by
  rw [eq_comm, NNReal.sqrt_eq_iff_eq_sq, dL2Norm_sq_indicate]

@[simp] lemma dL1Norm_indicate (s : Finset ι) : ‖𝟭_[R] s‖_[1] = #s := by
  simpa using dLpNorm_pow_indicate one_ne_zero s

lemma dLpNorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) : ‖μ_[R] s‖_[p] = #s ^ ((p : ℝ)⁻¹ - 1) := by
  rw [mu, dLpNorm_const_smul ((#s)⁻¹ : R) (𝟭_[R] s), dLpNorm_indicate, nnnorm_inv,
    RCLike.nnnorm_natCast, inv_mul_eq_div, ← NNReal.rpow_sub_one] <;> positivity

lemma dLpNorm_mu_le (hp : 1 ≤ p) : ‖μ_[R] s‖_[p] ≤ #s ^ (p⁻¹ - 1 : ℝ) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · exact (dLpNorm_mu hp hs).le

@[simp] lemma dL1Norm_mu (hs : s.Nonempty) : ‖μ_[R] s‖_[1] = 1 := by
  simpa using dLpNorm_mu le_rfl hs

lemma dL1Norm_mu_le_one : ‖μ_[R] s‖_[1] ≤ 1 := by simpa using dLpNorm_mu_le le_rfl

@[simp] lemma dL2Norm_mu (hs : s.Nonempty) : ‖μ_[R] s‖_[2] = #s ^ (-2⁻¹ : ℝ) := by
  have : (2⁻¹ - 1 : ℝ) = -2⁻¹ := by norm_num
  simpa [sqrt_eq_rpow, this] using dLpNorm_mu one_le_two (R := R) hs

end Indicator

/-! ### Translation -/

section dLpNorm
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}

@[simp]
lemma dLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) : ‖τ a f‖_[p] = ‖f‖_[p] := by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_nnnorm, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_nnnorm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] lemma dLpNorm_conjneg [RCLike E] (f : G → E) : ‖conjneg f‖_[p] = ‖f‖_[p] := by
  cases nonempty_fintype G
  simp only [conjneg, dLpNorm_conj]
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_nnnorm, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_nnnorm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

lemma dLpNorm_translate_sum_sub_le [NormedAddCommGroup E] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : G → E) : ‖τ (∑ i ∈ s, a i) f - f‖_[p] ≤ ∑ i ∈ s, ‖τ (a i) f - f‖_[p] := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s ih hs =>
  calc
    _ = ‖τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)‖_[p] := by
      rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ∑ j ∈ s, ‖(τ (a j) f - f)‖_[p] := by
      grw [dLpNorm_add_le hp, hs]
    _ = _ := by rw [dLpNorm_translate, sum_cons]

end dLpNorm
end MeasureTheory
