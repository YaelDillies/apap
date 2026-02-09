import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import LeanAPAP.Prereqs.Convolution.Compact
import LeanAPAP.Prereqs.Function.Indicator.Defs
import LeanAPAP.Prereqs.Inner.Hoelder.Compact
import LeanAPAP.Prereqs.Inner.Hoelder.Discrete
import LeanAPAP.Prereqs.FourierTransform.Compact

open AddChar Finset Function MeasureTheory
open Fintype (card)
open scoped BigOperators ComplexConjugate ComplexOrder

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [MeasurableSpace G]
  [DiscreteMeasurableSpace G] {ψ : AddChar G ℂ} {n : ℕ}

lemma cLpNorm_cconv_le_cLpNorm_cdconv (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℂ) :
    ‖f ∗ₙ f‖ₙ_[n] ≤ ‖f ○ₙ f‖ₙ_[n] := by
  refine le_of_pow_le_pow_left₀ hn₀ (by positivity) ?_
  obtain ⟨k, rfl⟩ := hn.two_dvd
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hn₀
  refine Complex.le_of_eq_sum_of_eq_sum_norm (fun ψ : (Fin k → AddChar G ℂ) × (Fin k → AddChar G ℂ)
    ↦ conj (∏ i, cft f (ψ.1 i) ^ 2) * (∏ i, cft f (ψ.2 i) ^ 2) * 𝔼 x, (∑ i, ψ.2 i - ∑ i, ψ.1 i) x)
    univ (by norm_cast; positivity) ?_ ?_
  · push_cast
    rw [← cft_inversion' (f ∗ₙ f), cLpNorm_two_mul_sum_pow hn₀]
    simp_rw [cft_cconv_apply, ← sq, Fintype.sum_prod_type, mul_expect, AddChar.sub_apply]
    simp [mul_mul_mul_comm, mul_comm, map_neg_eq_conj, prod_mul_distrib]
  · push_cast
    rw [← cft_inversion' (f ○ₙ f), cLpNorm_two_mul_sum_pow hn₀]
    simp_rw [cft_cdconv_apply, Complex.mul_conj', Fintype.sum_prod_type, mul_expect]
    congr 1 with ψ
    congr 1 with φ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, Complex.conj_ofReal, prod_mul_distrib,
      mul_mul_mul_comm, ← mul_expect, map_prod, sub_apply, AddChar.coe_sum, Finset.prod_apply,
      norm_mul, norm_prod, norm_pow, RCLike.norm_conj, Complex.ofReal_mul, Complex.ofReal_prod,
      Complex.ofReal_pow]
    congr 1
    calc
      𝔼 x, (∏ i, conj (ψ i x)) * ∏ i, φ i x = 𝔼 x, (∑ i, φ i - ∑ i, ψ i) x := by
        simp [map_neg_eq_conj, mul_comm, AddChar.sub_apply]
      _ = ‖𝔼 x, (∑ i, φ i - ∑ i, ψ i) x‖ := by simp [expect_eq_ite, apply_ite]
      _ = ‖𝔼 x, (∏ i, φ i x) * ∏ i, (ψ i) (-x)‖ := by simp [map_neg_eq_conj, AddChar.sub_apply]

lemma dLpNorm_conv_le_dLpNorm_dconv (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℂ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := sorry

-- TODO: Can we unify with `cLpNorm_cconv_le_cLpNorm_cdconv`?
lemma cLpNorm_cconv_le_cLpNorm_cdconv' (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℝ) :
    ‖f ∗ₙ f‖ₙ_[n] ≤ ‖f ○ₙ f‖ₙ_[n] := by
  simpa only [← Complex.ofReal_comp_cconv, ← Complex.ofReal_comp_cdconv, Complex.cLpNorm_coe_comp]
    using cLpNorm_cconv_le_cLpNorm_cdconv hn₀ hn ((↑) ∘ f)

-- TODO: Can we unify with `dLpNorm_conv_le_dLpNorm_dconv`?
lemma dLpNorm_conv_le_dLpNorm_dconv' (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℝ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  simpa only [← Complex.ofReal_comp_conv, ← Complex.ofReal_comp_dconv, Complex.dLpNorm_coe_comp]
    using dLpNorm_conv_le_dLpNorm_dconv hn₀ hn ((↑) ∘ f)
