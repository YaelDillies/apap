module

public import APAP.Prereqs.Convolution.Discrete.Defs
public import APAP.Prereqs.LpNorm.Compact
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.MeasureTheory.Constructions.AddChar

import AddCombi.Mathlib.Algebra.BigOperators.Ring.Finset
import APAP.Prereqs.Inner.Hoelder.Compact
import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

@[expose] public section

open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal Indicator NNReal translate

variable {G : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {ψ : AddChar G ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
noncomputable def dft (f : G → ℂ) : AddChar G ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : G → ℂ) (ψ : AddChar G ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

/-- A special case of the **Hausdorff-Young inequality** for the discrete Fourier transform. -/
lemma norm_dft_le_dL1Norm [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ)
    (ψ : AddChar G ℂ) : ‖dft f ψ‖ ≤ ‖f‖_[1] := by
  grw [dft_apply, norm_wInner_one_le_dLpNorm_mul_dLpNorm ∞ 1, dLinftyNorm_eq_iSup_norm]
  simp [AddChar.norm_apply]

/-- A special case of the **Hausdorff-Young inequality** for the discrete Fourier transform. -/
lemma cLinftyNorm_dft_le_dL1Norm [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ) :
    ‖dft f‖ₙ_[∞] ≤ ‖f‖_[1] := by
  rw [cLpNorm_exponent_top_eq_essSup]; exact ciSup_le fun ψ ↦ norm_dft_le_dL1Norm f ψ

@[simp] lemma dft_zero : dft (0 : G → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : G → ℂ) : dft (f + g) = dft f + dft g := by
  ext; simp [wInner_add_right, dft_apply]

@[simp] lemma dft_neg (f : G → ℂ) : dft (-f) = - dft f := by ext; simp [dft_apply]

@[simp] lemma dft_sub (f g : G → ℂ) : dft (f - g) = dft f - dft g := by
  ext; simp [wInner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const G a) ψ = 0 := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply', const_apply, ← sum_mul, ← map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp]
lemma dft_smul {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 ℂ] [StarModule 𝕝 ℂ]
    [IsScalarTower 𝕝 ℂ ℂ] (c : 𝕝) (f : G → ℂ) : dft (c • f) = c • dft f := by
  ext; simp [wInner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma wInner_cWeight_dft (f g : G → ℂ) : ⟪dft f, dft g⟫ₙ_[ℂ] = ⟪f, g⟫_[ℂ] := by
  classical
  unfold dft
  simp_rw [wInner_one_eq_sum, wInner_cWeight_eq_expect, inner_apply', map_sum, map_mul,
    starRingEnd_self_apply, sum_mul, mul_sum, expect_sum_comm, mul_mul_mul_comm _ (conj <| f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
    AddChar.expect_apply_eq_ite, add_neg_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma cL2Norm_dft [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ) :
    ‖dft f‖ₙ_[2] = ‖f‖_[2] := by
  refine (sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1 <| Complex.ofReal_injective ?_
  push_cast
  simpa [cLpNorm, dLpNorm, RCLike.wInner_cWeight_self, wInner_one_self] using wInner_cWeight_dft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : G → ℂ) (a : G) : 𝔼 ψ, dft f ψ * ψ a = f a := by
  classical
  simp_rw [dft, wInner_one_eq_sum, inner_apply', sum_mul, expect_sum_comm, mul_right_comm _ (f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.expect_apply_eq_ite, sub_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion' (f : G → ℂ) : 𝔼 ψ, dft f ψ • ⇑ψ = f := by ext; simpa using dft_inversion f _

lemma dft_dft_doubleDualEmb (f : G → ℂ) (a : G) :
    dft (dft f) (doubleDualEmb a) = card G * f (-a) := by
  simp only [← dft_inversion f (-a), dft_apply, wInner_one_eq_sum, inner_apply,
    map_neg_eq_inv, AddChar.inv_apply_eq_conj, doubleDualEmb_apply, ← Fintype.card_mul_expect,
    AddChar.card_eq]

lemma dft_dft (f : G → ℂ) : dft (dft f) = card G * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.natCast_apply, ← dft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma dft_injective : Injective (dft : (G → ℂ) → AddChar G ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (dft_inversion _ _).symm.trans <| by rw [h, dft_inversion]

lemma dft_inv (ψ : AddChar G ℂ) (hf : IsSelfAdjoint f) : dft f ψ⁻¹ = conj (dft f ψ) := by
  simp_rw [dft_apply, wInner_one_eq_sum, inner_apply, map_sum, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma dft_conj (f : G → ℂ) (ψ : AddChar G ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, map_sum, map_mul, ← inv_apply',
    ← inv_apply_eq_conj, inv_inv, Pi.conj_apply]

lemma dft_conjneg_apply (f : G → ℂ) (ψ : AddChar G ℂ) : dft (conjneg f) ψ = conj (dft f ψ) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, conjneg_apply, map_sum, map_mul,
    RCLike.conj_conj]
  refine Fintype.sum_equiv (Equiv.neg G) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
lemma dft_conjneg (f : G → ℂ) : dft (conjneg f) = conj (dft f) := funext <| dft_conjneg_apply _

lemma dft_comp_neg_apply (f : G → ℂ) (ψ : AddChar G ℂ) :
    dft (fun x ↦ f (-x)) ψ = dft f (-ψ) := by
  rw [dft, dft, wInner_one_eq_sum, wInner_one_eq_sum]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (by simp)

@[simp] lemma dft_balance (f : G → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

@[simp] lemma dft_trivChar [DecidableEq G] : dft (trivChar : G → ℂ) = 1 := by
  ext; simp [trivChar_apply, dft_apply, wInner_one_eq_sum]

@[simp] lemma dft_one : dft (1 : G → ℂ) = card G • trivChar :=
  dft_injective <| by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

@[simp] lemma dft_indicator_one_zero (A : Finset G) : dft 𝟭_[(A : Set G)] 0 = #A := by
  simp [dft_apply, wInner_one_eq_sum]

variable [DecidableEq G]

lemma dft_ddconv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) : dft (f ∗ᵈ g) ψ = dft f ψ * dft g ψ := by
  simp_rw [dft, wInner_one_eq_sum, inner_apply, ddconv_eq_sum_sub', mul_sum, sum_mul,
    ← sum_product', univ_product_univ]
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma dft_dddconv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) :
    dft (f ○ᵈ g) ψ = dft f ψ * conj (dft g ψ) := by
  rw [← ddconv_conjneg, dft_ddconv_apply, dft_conjneg_apply]

@[simp]
lemma dft_ddconv (f g : G → ℂ) : dft (f ∗ᵈ g) = dft f * dft g := funext <| dft_ddconv_apply _ _

@[simp]
lemma dft_dddconv (f g : G → ℂ) : dft (f ○ᵈ g) = dft f * conj (dft g) :=
  funext <| dft_dddconv_apply _ _

@[simp] lemma dft_iterConv (f : G → ℂ) : ∀ n, dft (f ∗ᵈ^ n) = dft f ^ n
  | 0 => dft_trivChar
  | n + 1 => by simp [iterConv_succ, pow_succ, dft_iterConv]

@[simp] lemma dft_iterConv_apply (f : G → ℂ) (n : ℕ) (ψ : AddChar G ℂ) :
    dft (f ∗ᵈ^ n) ψ = dft f ψ ^ n := congr_fun (dft_iterConv _ _) _
