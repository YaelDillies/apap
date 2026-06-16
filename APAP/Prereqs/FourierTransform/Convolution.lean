module

public import APAP.Prereqs.Convolution.Compact
public import APAP.Prereqs.LpNorm.Discrete.Basic

import APAP.Prereqs.FourierTransform.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

open AddChar Finset Function MeasureTheory
open Fintype (card)
open scoped BigOperators ComplexConjugate ComplexOrder

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [MeasurableSpace G]
  [DiscreteMeasurableSpace G] {ψ : AddChar G ℂ} {n : ℕ}

lemma cLpNorm_conv_le_cLpNorm_dconv (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℂ) :
    ‖f ∗ f‖ₙ_[n] ≤ ‖f ○ f‖ₙ_[n] := by
  refine le_of_pow_le_pow_left₀ hn₀ (by positivity) ?_
  obtain ⟨k, rfl⟩ := hn.two_dvd
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hn₀
  refine Complex.le_of_eq_sum_of_eq_sum_norm (fun ψ : (Fin k → AddChar G ℂ) × (Fin k → AddChar G ℂ)
    ↦ conj (∏ i, cft f (ψ.1 i) ^ 2) * (∏ i, cft f (ψ.2 i) ^ 2) * 𝔼 x, (∑ i, ψ.2 i - ∑ i, ψ.1 i) x)
    univ (by norm_cast; positivity) ?_ ?_
  · push_cast
    rw [← cft_inversion' (f ∗ f), cLpNorm_two_mul_sum_pow hn₀]
    simp_rw [cft_conv_apply, ← sq, Fintype.sum_prod_type, mul_expect, AddChar.sub_apply]
    simp [mul_mul_mul_comm, mul_comm, map_neg_eq_conj, prod_mul_distrib]
  · push_cast
    rw [← cft_inversion' (f ○ f), cLpNorm_two_mul_sum_pow hn₀]
    simp_rw [cft_dconv_apply, Complex.mul_conj', Fintype.sum_prod_type, mul_expect]
    congr 1 with ψ
    congr 1 with φ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, Complex.conj_ofReal, prod_mul_distrib,
      mul_mul_mul_comm, ← mul_expect, map_prod, AddChar.sub_apply, AddChar.coe_sum,
      Finset.prod_apply, norm_mul, norm_prod, norm_pow, RCLike.norm_conj, Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_pow]
    congr 1
    calc
      𝔼 x, (∏ i, conj (ψ i x)) * ∏ i, φ i x = 𝔼 x, (∑ i, φ i - ∑ i, ψ i) x := by
        simp [map_neg_eq_conj, mul_comm, AddChar.sub_apply]
      _ = ‖𝔼 x, (∑ i, φ i - ∑ i, ψ i) x‖ := by simp [expect_eq_ite, apply_ite]
      _ = ‖𝔼 x, (∏ i, φ i x) * ∏ i, (ψ i) (-x)‖ := by simp [map_neg_eq_conj, AddChar.sub_apply]

lemma dLpNorm_ddconv_le_dLpNorm_dddconv (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℂ) :
    ‖f ∗ᵈ f‖_[n] ≤ ‖f ○ᵈ f‖_[n] := by
  refine le_of_pow_le_pow_left₀ hn₀ (by positivity) ?_
  have h := pow_le_pow_left₀ (by positivity) (cLpNorm_conv_le_cLpNorm_dconv hn₀ hn f) n
  rw [conv_eq_smul_ddconv, dconv_eq_smul_dddconv] at h
  have h' : (Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ)⁻¹ ^ n * ‖f ∗ᵈ f‖_[n] ^ n ≤
      (Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ)⁻¹ ^ n * ‖f ○ᵈ f‖_[n] ^ n := by
    simpa [cLpNorm_pow_eq_card_inv_mul_dLpNorm_pow hn₀, dLpNorm_nnqsmul, mul_pow,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hpos : 0 < (Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ)⁻¹ ^ n := by positivity
  nlinarith

-- TODO: Can we unify with `cLpNorm_conv_le_cLpNorm_dconv`?
lemma cLpNorm_conv_le_cLpNorm_dconv' (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℝ) :
    ‖f ∗ f‖ₙ_[n] ≤ ‖f ○ f‖ₙ_[n] := by
  simpa only [← Complex.ofReal_comp_conv, ← Complex.ofReal_comp_dconv, Complex.cLpNorm_coe_comp]
    using cLpNorm_conv_le_cLpNorm_dconv hn₀ hn ((↑) ∘ f)

-- TODO: Can we unify with `dLpNorm_ddconv_le_dLpNorm_dddconv`?
lemma dLpNorm_ddconv_le_dLpNorm_dddconv' (hn₀ : n ≠ 0) (hn : Even n) (f : G → ℝ) :
    ‖f ∗ᵈ f‖_[n] ≤ ‖f ○ᵈ f‖_[n] := by
  simpa only [← Complex.ofReal_comp_ddconv, ← Complex.ofReal_comp_dddconv, Complex.dLpNorm_coe_comp]
    using dLpNorm_ddconv_le_dLpNorm_dddconv hn₀ hn ((↑) ∘ f)
