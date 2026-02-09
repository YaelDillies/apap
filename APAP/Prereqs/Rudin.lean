import APAP.Prereqs.FourierTransform.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Additive.Randomisation

/-!
# Rudin's inequality
-/

open Finset hiding card
open Fintype (card)
open Function Real MeasureTheory
open Complex (I re im)
open scoped BigOperators Nat NNReal ENNReal ComplexConjugate ComplexOrder

variable {G : Type*} [Fintype G] [AddCommGroup G] {p : ℕ}

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- **Rudin's inequality**, exponential form. -/
lemma rudin_exp_ineq (f : G → ℂ) (hf : AddDissociated <| support <| cft f) :
    𝔼 a, exp (f a).re ≤ exp (‖f‖ₙ_[2] ^ 2 / 2) := by
  have (z : ℂ) : exp (re z) ≤ cosh ‖z‖ + re (z / ‖z‖) * sinh ‖z‖ :=
    calc
      _ = _ := by obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh (by simpa using z.abs_re_div_norm_le_one) _
  choose c hc hcf using fun ψ ↦ Complex.exists_norm_mul_eq_self (cft f ψ)
  have hc₀ (ψ) : c ψ ≠ 0 := fun h ↦ by simpa [h] using hc ψ
  have (a : G) :
    exp (f a).re ≤ ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * sinh ‖cft f ψ‖ * ψ a).re) :=
    calc
      _ = ∏ ψ, exp ((cft f ψ * ψ a).re) := by simp_rw [← exp_sum, ← Complex.re_sum, cft_inversion]
      _ ≤ _ := prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ this _
      _ = ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * (cft f ψ * ψ a)
            / (c ψ * ↑‖cft f ψ‖)).re * sinh ‖cft f ψ‖) := by
          simp_rw [norm_mul, AddChar.norm_apply, mul_one, mul_div_mul_left _ _ (hc₀ _)]
      _ = _ := by
          congr with ψ
          obtain hψ | hψ := eq_or_ne (cft f ψ) 0
          · simp [hψ]
          · simp only [hcf, mul_left_comm (c _), mul_div_cancel_left₀ _ hψ, ← Complex.re_mul_ofReal,
              mul_right_comm]
  calc
    _ ≤ 𝔼 a, ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * sinh ‖cft f ψ‖ * ψ a).re) :=
        expect_le_expect fun _ _ ↦ this _
    _ = ∏ ψ, cosh ‖cft f ψ‖ :=
        AddDissociated.randomisation _ _ <| by simpa [-Complex.ofReal_sinh, hc₀]
    _ ≤ ∏ ψ, exp (‖cft f ψ‖ ^ 2 / 2) :=
        prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ cosh_le_exp_half_sq _
    _ = _ := by simp_rw [← exp_sum, ← sum_div, ← dL2Norm_cft, dL2Norm_sq_eq_sum_norm]

/-- **Rudin's inequality**, exponential form with absolute values. -/
lemma rudin_exp_abs_ineq (f : G → ℂ) (hf : AddDissociated <| support <| cft f) :
    𝔼 a, exp |(f a).re| ≤ 2 * exp (‖f‖ₙ_[2] ^ 2 / 2) := by
  calc
    _ ≤ 𝔼 a, (exp (f a).re + exp (-f a).re) := expect_le_expect fun _ _ ↦ exp_abs_le _
    _ = 𝔼 a, exp (f a).re + 𝔼 a, exp ((-f) a).re := by simp [expect_add_distrib]
    _ ≤ exp (‖f‖ₙ_[2] ^ 2 / 2) + exp (‖-f‖ₙ_[2] ^ 2 / 2) :=
        add_le_add (rudin_exp_ineq f hf) (rudin_exp_ineq (-f) <| by simpa using hf)
    _ = _ := by simp [two_mul]

private lemma rudin_ineq_aux (hp : 2 ≤ p) (f : G → ℂ) (hf : AddDissociated <| support <| cft f) :
    ‖re ∘ f‖ₙ_[p] ≤ 2 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
  wlog hfp : ‖f‖ₙ_[2] = sqrt p with H
  · obtain rfl | hf := eq_or_ne f 0
    · simp
    specialize H hp ((sqrt p / ‖f‖ₙ_[2]) • f) ?_
    · rwa [cft_smul, support_const_smul_of_ne_zero]
      positivity
    have : 0 < ‖f‖ₙ_[2] := (cLpNorm_pos two_ne_zero).2 hf
    have : 0 < √ p := by positivity
    simp_rw [Function.comp_def, Pi.smul_apply, Complex.smul_re, ← Pi.smul_def] at H
    simpa [cLpNorm_const_smul, sqrt_pos.2, ← mul_div_right_comm, mul_comm √_,
      div_le_iff₀, mul_right_comm, abs_of_nonneg, *] using H
  have hp₀ : p ≠ 0 := by positivity
  have : (‖re ∘ f‖ₙ_[↑p] / p) ^ p ≤ (2 * exp 2⁻¹) ^ p := by
    calc
      _ = 𝔼 a, |(f a).re| ^ p / p ^ p := by
          simp [div_pow, cLpNorm_pow_eq_expect_norm hp₀, expect_div]
      _ ≤ 𝔼 a, |(f a).re| ^ p / p ! := by gcongr; norm_cast; exact p.factorial_le_pow
      _ ≤ 𝔼 a, exp |(f a).re| := by gcongr; exact pow_div_factorial_le_exp _ (abs_nonneg _) _
      _ ≤ _ := rudin_exp_abs_ineq f hf
      _ ≤ 2 ^ p * exp (‖f‖ₙ_[2] ^ 2 / 2) := by gcongr; exact le_self_pow₀ one_le_two hp₀
      _ = (2 * exp 2⁻¹) ^ p := by
          rw [hfp, sq_sqrt, mul_pow, ← exp_nsmul, nsmul_eq_mul, div_eq_mul_inv]; positivity
  refine le_of_pow_le_pow_left₀ hp₀ (by positivity) ?_
  rwa [hfp, mul_assoc, mul_self_sqrt, mul_pow, ← div_le_iff₀, ← div_pow]
  all_goals positivity

/-- **Rudin's inequality**, usual form. -/
lemma rudin_ineq (hp : 2 ≤ p) (f : G → ℂ) (hf : AddDissociated <| support <| cft f) :
    ‖f‖ₙ_[p] ≤ 4 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
  have hp₁ : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp
  calc
    (‖f‖ₙ_[p] : ℝ) = ‖(fun a ↦ ((f a).re : ℂ)) + I • (fun a ↦ ((f a).im : ℂ))‖ₙ_[p]
      := by congr with a; simp [mul_comm I]
    _ ≤ ‖fun a ↦ ((f a).re : ℂ)‖ₙ_[p] + ‖I • (fun a ↦ ((f a).im : ℂ))‖ₙ_[p]
      := cLpNorm_add_le hp₁
    _ = ‖re ∘ f‖ₙ_[p] + ‖re ∘ ((-I) • f)‖ₙ_[p] := by
        rw [cLpNorm_const_smul, Complex.norm_I, one_mul, ← Complex.cLpNorm_coe_comp,
          ← Complex.cLpNorm_coe_comp]
        congr
        ext a : 1
        simp
    _ ≤ 2 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] + 2 * exp 2⁻¹ * sqrt p * ‖(-I) • f‖ₙ_[2]
      := add_le_add (rudin_ineq_aux hp _ hf) <| rudin_ineq_aux hp _ <| by
        rwa [cft_smul, support_const_smul_of_ne_zero]; simp
    _ = 4 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
        rw [cLpNorm_const_smul, norm_neg, Complex.norm_I, one_mul]; ring
