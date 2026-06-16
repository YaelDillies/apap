module

public import APAP.Prereqs.Convolution.Compact
public import APAP.Prereqs.FourierTransform.Discrete

import APAP.Prereqs.Inner.Hoelder.Compact
import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Compact Fourier transform

This file defines the compact Fourier transform for finite groups and shows the
Parseval-Plancherel identity and Fourier inversion formula for it.
-/

@[expose] public section

noncomputable section

open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped ComplexConjugate ComplexOrder Indicator

variable {G γ : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {ψ : AddChar G ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def cft (f : G → ℂ) : AddChar G ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫ₙ_[ℂ]

lemma cft_apply (f : G → ℂ) (ψ : AddChar G ℂ) : cft f ψ = ⟪ψ, f⟫ₙ_[ℂ] := rfl

@[simp] lemma cft_zero : cft (0 : G → ℂ) = 0 := by ext; simp [cft_apply]

@[simp] lemma cft_add (f g : G → ℂ) : cft (f + g) = cft f + cft g := by
  ext; simp [wInner_add_right, cft_apply]

@[simp] lemma cft_neg (f : G → ℂ) : cft (-f) = - cft f := by ext; simp [cft_apply]

@[simp] lemma cft_sub (f g : G → ℂ) : cft (f - g) = cft f - cft g := by
  ext; simp [wInner_sub_right, cft_apply]

@[simp] lemma cft_const (a : ℂ) (hψ : ψ ≠ 0) : cft (const G a) ψ = 0 := by
  simp only [cft_apply, wInner_cWeight_eq_expect, inner_apply', const_apply, ← expect_mul,
    ← map_expect, expect_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp] lemma cft_smul {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 ℂ] [StarModule 𝕝 ℂ]
    [IsScalarTower 𝕝 ℂ ℂ] (c : 𝕝) (f : G → ℂ) :  cft (c • f) = c • cft f := by
  ext; simp [wInner_smul_right, cft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma wInner_one_cft (f g : G → ℂ) : ⟪cft f, cft g⟫_[ℂ] = ⟪f, g⟫ₙ_[ℂ] := by
  classical
  unfold cft
  simp_rw [wInner_one_eq_sum, wInner_cWeight_eq_expect, inner_apply', map_expect, map_mul,
    starRingEnd_self_apply, expect_mul, mul_expect, ← expect_sum_comm,
    mul_mul_mul_comm _ (conj <| f _), ← sum_mul, ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv,
    ← map_add_eq_mul, AddChar.sum_apply_eq_ite]
  simp [add_neg_eq_zero, card_univ, Fintype.card_ne_zero, NNRat.smul_def]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma dL2Norm_cft [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ) :
    ‖cft f‖_[2] = ‖f‖ₙ_[2] := by
  refine (sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1 <| Complex.ofReal_injective ?_
  push_cast
  simpa [cLpNorm, dLpNorm, RCLike.wInner_cWeight_self, wInner_one_self] using wInner_one_cft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma cft_inversion (f : G → ℂ) (a : G) : ∑ ψ, cft f ψ * ψ a = f a := by
  classical
  simp_rw [cft, wInner_cWeight_eq_expect, inner_apply', expect_mul, ← expect_sum_comm,
    mul_right_comm _ (f _), ← sum_mul, ← AddChar.inv_apply_eq_conj, inv_mul_eq_div,
    ← map_sub_eq_div, AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul,
    Fintype.expect_ite_eq]
  simp [NNRat.smul_def (K := ℂ), Fintype.card_ne_zero]

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma cft_inversion' (f : G → ℂ) : ∑ ψ, cft f ψ • ⇑ψ = f := by ext; simpa using cft_inversion _ _

lemma dft_cft_doubleDualEmb (f : G → ℂ) (a : G) : dft (cft f) (doubleDualEmb a) = f (-a) := by
  simp [← cft_inversion f (-a), dft_apply, wInner_one_eq_sum, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj]

lemma cft_dft_doubleDualEmb (f : G → ℂ) (a : G) : cft (dft f) (doubleDualEmb a) = f (-a) := by
  simp [← dft_inversion f (-a), cft_apply, wInner_cWeight_eq_expect, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj]

lemma dft_cft (f : G → ℂ) : dft (cft f) = f ∘ doubleDualEquiv.symm ∘ Neg.neg := by
  ext; simp [← dft_cft_doubleDualEmb]

lemma cft_dft (f : G → ℂ) : cft (dft f) = f ∘ doubleDualEquiv.symm ∘ Neg.neg := by
  ext; simp [← cft_dft_doubleDualEmb]

lemma cft_injective : Injective (cft : (G → ℂ) → AddChar G ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (cft_inversion _ _).symm.trans <| by rw [h, cft_inversion]

lemma cft_inv (ψ : AddChar G ℂ) (hf : IsSelfAdjoint f) : cft f ψ⁻¹ = conj (cft f ψ) := by
  simp_rw [cft_apply, wInner_cWeight_eq_expect, inner_apply, map_expect, AddChar.inv_apply',
    map_mul, AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma cft_conj (f : G → ℂ) (ψ : AddChar G ℂ) : cft (conj f) ψ = conj (cft f ψ⁻¹) := by
  simp only [cft_apply, wInner_cWeight_eq_expect, inner_apply, map_expect, map_mul, ← inv_apply',
    ← inv_apply_eq_conj, inv_inv, Pi.conj_apply]

lemma cft_conjneg_apply (f : G → ℂ) (ψ : AddChar G ℂ) : cft (conjneg f) ψ = conj (cft f ψ) := by
  simp only [cft_apply, wInner_cWeight_eq_expect, inner_apply, conjneg_apply, map_expect, map_mul,
    RCLike.conj_conj]
  refine Fintype.expect_equiv (Equiv.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
lemma cft_conjneg (f : G → ℂ) : cft (conjneg f) = conj (cft f) := funext <| cft_conjneg_apply _

@[simp] lemma cft_balance (f : G → ℂ) (hψ : ψ ≠ 0) : cft (balance f) ψ = cft f ψ := by
  simp only [balance, Pi.sub_apply, cft_sub, cft_const _ hψ, sub_zero]

@[simp] lemma cft_trivNChar [DecidableEq G] : cft (trivNChar : G → ℂ) = 1 := by
  ext; simp [cft_apply, wInner_cWeight_eq_expect, NNRat.smul_def]

@[simp] lemma cft_one : cft (1 : G → ℂ) = trivChar :=
  dft_injective <| by classical rw [dft_trivChar, dft_cft, Pi.one_comp]

@[simp] lemma cft_indicator_one_zero (s : Finset G) : cft 𝟭_[(s : Set G)] 0 = s.dens := by
  simp [cft_apply, wInner_cWeight_eq_expect, inner_apply, expect_indicator_one, ← Pi.one_def,
    map_one, dens, div_eq_inv_mul]

variable [DecidableEq G]

lemma cft_conv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) : cft (f ∗ g) ψ = cft f ψ * cft g ψ := by
  simp_rw [cft, wInner_cWeight_eq_expect, inner_apply, conv_eq_expect_sub', mul_expect, expect_mul,
    ← expect_product', univ_product_univ]
  refine Fintype.expect_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma cft_dconv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) :
    cft (f ○ g) ψ = cft f ψ * conj (cft g ψ) := by
  rw [← conv_conjneg, cft_conv_apply, cft_conjneg_apply]

@[simp] lemma cft_conv (f g : G → ℂ) : cft (f ∗ g) = cft f * cft g :=
  funext <| cft_conv_apply _ _

@[simp]
lemma cft_dconv (f g : G → ℂ) : cft (f ○ g) = cft f * conj (cft g) :=
  funext <| cft_dconv_apply _ _

@[simp] lemma cft_iterCConv (f : G → ℂ) : ∀ n, cft (f ∗^ₙ n) = cft f ^ n
  | 0 => cft_trivNChar
  | n + 1 => by simp [iterCConv_succ, pow_succ, cft_iterCConv]

@[simp] lemma cft_iterCConv_apply (f : G → ℂ) (n : ℕ) (ψ : AddChar G ℂ) :
    cft (f ∗^ₙ n) ψ = cft f ψ ^ n := congr_fun (cft_iterCConv _ _) _

-- lemma dL2Norm_iterCConv (f : G → ℂ) (n : ℕ) : ‖f ∗^ₙ n‖ₙ_[2] = ‖f ^ n‖_[2] := by
--   rw [← dL2Norm_cft, cft_iterCConv, ← ENNReal.coe_two, dLpNorm_pow]
--   norm_cast
--   refine (sq_eq_sq₀ (by positivity) <| by positivity).1 ?_
--   rw [← ENNReal.coe_two, dLpNorm_pow, ← pow_mul', ← Complex.ofReal_inj]
--   push_cast
--   simp_rw [pow_mul, ← Complex.mul_conj', conj_iterConv_apply, mul_pow]
