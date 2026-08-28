/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Probability.IdentDistrib

import APAP.Prereqs.Symmetrize
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Positivity.Finset

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality.

The Marcinkiewicz-Zygmund inequality states that, if `X₁, ... Xₐ ∈ L^p` are independent random
variables of mean zero valued in some inner product space, then the `L^p`-norm of `X₁ + ... + Xₐ` is
at most `Cₚ` times the `L^(p/2)`-norm of `|X₁|² + ... + |Xₐ|²`, where `Cₚ` is a constant depending
on `p` alone.

## Notation

Throughout this file, `A ^^ n` denotes `A × ... × A` (with `n` factors). Formally, this is
`Fintype.piFinset fun _ : Fin n ↦ A`.

## TODO

We currently only prove the inequality for `p = 2 * m` an even natural number. The general `p` case
can be obtained from this specific one by nesting of Lp norms.
-/

public section

open Finset Fintype Function Nat MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

variable {ι Ω E : Type*} {A : Finset ι} {m n : ℕ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : ι → Ω → E}

local notation:70 A:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ A

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for symmetric random variables.
-/
noncomputable def marcinkiewiczZygmundSymmConst (p : ℝ≥0) : ℝ := (p / 2) ^ (p / 2 : ℝ)

private lemma prod_pow_card_filter_eq [DecidableEq ι] (g : ι → ℝ) {I : Fin m → ι × ι}
    (hI : I ∈ A ×ˢ A ^^ m) :
    ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) =
      ∏ k, g (I k).1 * g (I k).2 := by
  simp only [mem_piFinset, mem_product, forall_and] at hI
  simp_rw [pow_add, prod_mul_distrib, ← prod_const]
  rw [prod_fiberwise_of_maps_to' (fun x _ ↦ hI.2 x),
    prod_fiberwise_of_maps_to' (fun x _ ↦ hI.1 x), ← prod_mul_distrib]

private lemma sum_prod_pow_weight [DecidableEq ι] (g : ι → ℝ) :
    ∑ I ∈ A ×ˢ A ^^ m, ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) =
      ∑ w ∈ piAntidiag A (2 * m), multinomial A w * ∏ i ∈ A, g i ^ w i := by
  rw [sum_congr rfl fun I hI ↦ prod_pow_card_filter_eq g hI,
    ← sum_pow' (A ×ˢ A) (fun p ↦ g p.1 * g p.2) m,
    sum_product, ← Finset.sum_mul_sum, ← sq, ← pow_mul, sum_pow_eq_sum_piAntidiag]

lemma sum_pow_neg_one_one (v : ℕ) :
    ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ v = if Even v then 2 else 0 := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  split_ifs with h_even
  · simp [sum_pair hne, h_even, one_add_one_eq_two]
  · simp [sum_pair hne, not_even_iff_odd.mp h_even]

private lemma sum_signs_prod_pow [DecidableEq ι] (v : ι → ℕ) :
    ∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ), ∏ i : ↥A, ε i ^ v ↑i =
      2 ^ #A * if ∀ i ∈ A, Even (v i) then 1 else 0 := by
  rw [sum_prod_piFinset ({-1, 1} : Finset ℝ) (fun (i : ↥A) (j : ℝ) ↦ j ^ v ↑i)]
  simp_rw [sum_pow_neg_one_one]
  rw [Fintype.prod_ite_zero]
  simp [Subtype.forall]

lemma prod_mul_ite_mem_pow [DecidableEq ι] (g : ι → ℝ) (ε : ↥A → ℝ) (v : ι → ℕ) :
    ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^ v i =
      (∏ i : ↥A, ε i ^ v ↑i) * ∏ i ∈ A, g i ^ v i := by
  simp_rw [mul_pow, prod_mul_distrib]
  congr 1
  rw [univ_eq_attach, ← prod_attach]
  simp

lemma sum_signs_prod_pow_eq [DecidableEq ι] (g : ι → ℝ) (v : ι → ℕ) :
    ((2 : ℝ) ^ #A * if ∀ i ∈ A, Even (v i) then (1 : ℝ) else 0) * ∏ i ∈ A, g i ^ v i =
      ∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ),
        ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^ v i := by
  rw [← sum_signs_prod_pow, sum_mul]
  refine sum_congr rfl fun ε _ ↦ ?_
  exact (prod_mul_ite_mem_pow g ε v).symm

lemma sum_signs_multinomial_prod_pow [DecidableEq ι] (g : ι → ℝ) (w : ι → ℕ) :
    ∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ),
      (multinomial A w : ℝ) * ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^ w i =
    (2 ^ #A * if ∀ i ∈ A, Even (w i) then (1 : ℝ) else 0) *
      (multinomial A w * ∏ i ∈ A, g i ^ w i) := by
  simp_rw [prod_mul_ite_mem_pow g _ _, mul_left_comm (multinomial A w : ℝ),
    ← sum_mul, sum_signs_prod_pow]

private lemma sum_even_prod_pow_eq_sum_signs [DecidableEq ι] (g : ι → ℝ) :
    (2 : ℝ) ^ #A *
        ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
          ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) =
      ∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ), ∑ I ∈ A ×ˢ A ^^ m,
        ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^
          (#{k | (I k).1 = i} + #{k | (I k).2 = i}) := by
  rw [mul_sum, sum_filter]
  have h_eq (I : Fin m → ι × ι) :
      (if ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}) then
        (2 : ℝ) ^ #A * ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) else 0) =
      ((2 : ℝ) ^ #A *
        ite (∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i})) 1 0) *
        ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) := by simp
  simp_rw [h_eq, sum_signs_prod_pow_eq g]
  exact sum_comm

private lemma sum_signs_sum_prod_pow_eq_even_multinomial [DecidableEq ι] (g : ι → ℝ) :
    (∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ), ∑ I ∈ A ×ˢ A ^^ m,
      ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^
        (#{k | (I k).1 = i} + #{k | (I k).2 = i})) =
      2 ^ #A * ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
        multinomial A w * ∏ i ∈ A, g i ^ w i := by
  simp_rw [sum_prod_pow_weight _]
  rw [sum_comm]
  have h_eq : (∑ w ∈ piAntidiag A (2 * m), ∑ ε ∈ piFinset fun _ : ↥A ↦ ({-1, 1} : Finset ℝ),
        multinomial A w * ∏ i ∈ A, ((if h : i ∈ A then ε ⟨i, h⟩ else 1) * g i) ^ w i) =
      ∑ w ∈ piAntidiag A (2 * m), (2 ^ #A * if ∀ i ∈ A, Even (w i) then (1 : ℝ) else 0) *
        (multinomial A w * ∏ i ∈ A, g i ^ w i) :=
    sum_congr rfl fun w _ ↦ sum_signs_multinomial_prod_pow g w
  rw [h_eq, mul_sum, sum_filter]
  grind

private lemma sum_filter_even_prod_pow_weight [DecidableEq ι] (g : ι → ℝ) :
    ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∏ i ∈ A, g i ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) =
      ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
        multinomial A w * ∏ i ∈ A, g i ^ w i := by
  have hne : (2 : ℝ) ^ #A ≠ 0 := by positivity
  refine mul_left_cancel₀ hne ?_
  rw [sum_even_prod_pow_eq_sum_signs, sum_signs_sum_prod_pow_eq_even_multinomial]

omit [IsFiniteMeasure μ] [MeasurableSpace E] [InnerProductSpace ℝ E] in
lemma integrable_prod_norm {I : Fin m → ι × ι} (hi : I ∈ A ×ˢ A ^^ m) (hm : m ≠ 0)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    Integrable (fun ω ↦ ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖) μ := by
  have hi_mem (k : Fin m) : (I k).1 ∈ A ∧ (I k).2 ∈ A := by simp_all
  simp_rw [prod_mul_distrib]
  rw [← memLp_one_iff_integrable]
  have h_two : (∑ _k : Fin m, (2 * (m : ℝ≥0∞))⁻¹)⁻¹ = 2 := by
    simp only [sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.mul_inv]
    · rw [inv_inv, mul_comm, mul_assoc, ENNReal.mul_inv_cancel]
      · simp
      · simp_all
      · simp
    · simp_all
    · simp
  refine .mul' (p := 2) (q := 2) ?_ ?_
  · rw [← h_two]
    exact .prod' fun k _ ↦ (memLp_X _ (hi_mem k).2).norm
  · rw [← h_two]
    exact .prod' fun k _ ↦ (memLp_X _ (hi_mem k).1).norm

omit [IsFiniteMeasure μ] [MeasurableSpace E] in
lemma integrable_prod_inner {I : Fin m → ι × ι} (hi : I ∈ A ×ˢ A ^^ m) (hm : m ≠ 0)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    Integrable (fun ω ↦ ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)) μ := by
  have hi_mem (k : Fin m) : (I k).1 ∈ A ∧ (I k).2 ∈ A := by simp_all
  refine (integrable_prod_norm hi hm memLp_X).mono' ?_ ?_
  · exact aestronglyMeasurable_fun_prod _ fun k _ ↦
      ((memLp_X _ (hi_mem k).1).aestronglyMeasurable.inner
        (memLp_X _ (hi_mem k).2).aestronglyMeasurable)
  · filter_upwards with ω
    refine (Finset.norm_prod_le _ _).trans ?_
    exact prod_le_prod (fun k _ ↦ norm_nonneg _) fun k _ ↦ norm_inner_le_norm _ _

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] in
lemma iIndepFun.update_neg [DecidableEq ι] [SecondCountableTopology E] [BorelSpace E]
    (hX : iIndepFun X μ) (i : ι) :
    iIndepFun (update X i (-X i)) μ := by
  have : update X i (-X i) = fun j ↦ (if j = i then (Neg.neg : E → E) else id) ∘ X j := by
    funext j ω
    split_ifs with hj
    · simp_all
    · simp [update_of_ne hj]
  rw [this]
  refine hX.comp (fun j ↦ if j = i then (Neg.neg : E → E) else id) fun j ↦ ?_
  split_ifs with hj
  · exact measurable_neg
  · exact measurable_id

omit [IsFiniteMeasure μ] in
lemma integral_prod_inner_eq_update [DecidableEq ι] [SecondCountableTopology E] [BorelSpace E]
    (h_indep : iIndepFun X μ)
    (h_ident_neg : ∀ k, IdentDistrib (X k) (-X k) μ μ)
    {I : Fin m → ι × ι} (hi : I ∈ A ×ˢ A ^^ m) (i : ι) :
    ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ =
      ∫ ω, ∏ k, inner ℝ (update X i (-X i) (I k).1 ω) (update X i (-X i) (I k).2 ω) ∂μ := by
  let Y := update X i (-X i)
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hi_mem (k : Fin m) : (I k).1 ∈ A ∧ (I k).2 ∈ A := mem_product.mp (mem_piFinset.mp hi k)
  have hφ : Measurable fun w : ↥A → E ↦
      ∏ k, inner ℝ (w ⟨(I k).1, (hi_mem k).1⟩) (w ⟨(I k).2, (hi_mem k).2⟩) := by
    refine measurable_prod _ fun k _ ↦ ?_
    exact continuous_inner.measurable.comp
      ((measurable_pi_apply (⟨(I k).1, (hi_mem k).1⟩ : ↥A)).prodMk
        (measurable_pi_apply (⟨(I k).2, (hi_mem k).2⟩ : ↥A)))
  have h_ident : IdentDistrib (fun ω (j : ↥A) ↦ X j ω) (fun ω (j : ↥A) ↦ Y j ω) μ μ :=
    have h_id (j : ↥A) : IdentDistrib (X j) (Y j) μ μ := by
      obtain rfl | hji := eq_or_ne (j : ι) i
      · grind
      · simpa [Y, hji] using .refl (h_ident_neg j).aemeasurable_fst
    IdentDistrib.pi h_id (h_indep.restrict A)
      ((iIndepFun.update_neg h_indep i).restrict A)
  exact (h_ident.comp hφ).integral_eq

omit [IsFiniteMeasure μ] [MeasurableSpace E] in
lemma sum_inner_prod_pow (hm : m ≠ 0) (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ =
      ∑ I ∈ A ×ˢ A ^^ m, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
  have h_int_prod_inner I (hi : I ∈ A ×ˢ A ^^ m) :
      Integrable (fun ω ↦ ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)) μ :=
    integrable_prod_inner hi hm h_lp
  simp_rw [pow_mul, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum, ← sum_product',
    sum_pow', integral_finsetSum _ h_int_prod_inner]

omit [IsFiniteMeasure μ] in
lemma sum_inner_prod_pow_eq_even [DecidableEq ι] [SecondCountableTopology E] [BorelSpace E]
    (h_indep : iIndepFun X μ) (h_ident_neg : ∀ i, IdentDistrib (X i) (-X i) μ μ) :
    ∑ I ∈ A ×ˢ A ^^ m, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ =
      ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
  rw [sum_filter_of_ne]
  rintro I h_mem h_even_index i hi
  contrapose! h_even_index
  replace h_even_index : Odd (#{k | (I k).1 = i} + #{k | (I k).2 = i}) := by grind
  rw [← neg_eq_self, ← integral_neg, eq_comm]
  calc
    ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ
    _ = ∫ ω, ∏ k, inner ℝ (update X i (-X i) (I k).1 ω) (update X i (-X i) (I k).2 ω) ∂μ :=
      integral_prod_inner_eq_update h_indep h_ident_neg h_mem i
    _ = ∫ ω, -∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
      congr 1 with ω
      have h_eq k : inner ℝ (update X i (- X i) (I k).1 ω) (update X i (- X i) (I k).2 ω) =
          ((if (I k).1 = i then -1 else 1) * (if (I k).2 = i then -1 else 1)) *
            inner ℝ (X (I k).1 ω) (X (I k).2 ω) := by
        split_ifs <;> simp [update_self, update_of_ne, *]
      simp_rw [h_eq]
      rw [prod_mul_distrib, prod_mul_distrib]
      simp [prod_ite, ← pow_add, h_even_index.neg_one_pow]

omit [IsFiniteMeasure μ] [MeasurableSpace E] [InnerProductSpace ℝ E] in
lemma integrable_prod_norm_pow [DecidableEq ι] (hm : m ≠ 0)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) {w : ι → ℕ} (hw : w ∈ piAntidiag A (2 * m)) :
    Integrable (fun ω ↦ ∏ i ∈ A, ‖X i ω‖ ^ w i) μ := by
  obtain ⟨hwsum, -⟩ := mem_piAntidiag.mp hw
  have h_sum : (∑ i ∈ A, ((2 * m : ℝ≥0∞) / (w i : ℝ≥0∞))⁻¹)⁻¹ = 1 := by
    have h_top : (2 * m : ℝ≥0∞) ≠ ∞ := by finiteness
    have h_nz : (2 * m : ℝ≥0∞) ≠ 0 := by simp_all
    have h_inv (i) : ((2 * m : ℝ≥0∞) / (w i : ℝ≥0∞))⁻¹ = (w i : ℝ≥0∞) * (2 * m : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.inv_div (Or.inr h_top) (Or.inr h_nz), div_eq_mul_inv]
    rw [sum_congr rfl fun i _ ↦ h_inv i, ← sum_mul, ← Nat.cast_sum, hwsum]
    push_cast
    rw [ENNReal.mul_inv_cancel h_nz h_top, inv_one]
  rw [← memLp_one_iff_integrable, ← h_sum]
  refine .prod' fun i hi ↦ ?_
  simpa [← rpow_natCast] using (h_lp i hi).norm_rpow_div (w i)

omit [IsFiniteMeasure μ] [MeasurableSpace E] [InnerProductSpace ℝ E] in
lemma sum_norm_pow_eq_sum_multinomial [DecidableEq ι] (hm : m ≠ 0)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    (∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ) =
      ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
        multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
  have h_int_card I (hI : I ∈ A ×ˢ A ^^ m) :
      Integrable (fun ω ↦ ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i})) μ := by
    refine (integrable_prod_norm hI hm h_lp).congr ?_
    exact ae_of_all _ fun ω ↦ (prod_pow_card_filter_eq (fun i ↦ ‖X i ω‖) hI).symm
  calc
    ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ
      = ∫ ω, ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
          ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ :=
        (integral_finsetSum _ fun I hi ↦ h_int_card I (mem_filter.1 hi).1).symm
    _ = ∫ ω, ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
          multinomial A w * ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
        congr with ω
        exact sum_filter_even_prod_pow_weight fun i ↦ ‖X i ω‖
    _ = ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
          multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
        rw [integral_finsetSum _ fun w hw ↦
          (integrable_prod_norm_pow hm h_lp (mem_filter.1 hw).1).const_mul _]
        exact sum_congr rfl fun w _ ↦ integral_const_mul ..

omit [IsFiniteMeasure μ] in
lemma sum_inner_prod_pow_le_sum_prod_norm [DecidableEq ι] [SecondCountableTopology E] [BorelSpace E]
    (h_indep : iIndepFun X μ)
    (h_ident_neg : ∀ i, IdentDistrib (X i) (-X i) μ μ)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) (hm : m ≠ 0) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖ ∂μ := by
  rw [sum_inner_prod_pow hm h_lp, sum_inner_prod_pow_eq_even h_indep h_ident_neg]
  refine ((le_abs_self _).trans (abs_sum_le_sum_abs ..)).trans (sum_le_sum fun I hi ↦ ?_)
  refine abs_integral_le_integral_abs.trans ?_
  simp_rw [abs_prod]
  refine integral_mono ?_ (integrable_prod_norm (filter_subset _ _ hi) hm h_lp) fun ω ↦ ?_
  · exact (integrable_prod_inner (filter_subset _ _ hi) hm h_lp).abs.congr
      (ae_of_all _ fun ω ↦ abs_prod _ _)
  · exact prod_le_prod (fun k _ ↦ abs_nonneg _) fun k _ ↦ abs_real_inner_le_norm ..

omit [IsFiniteMeasure μ] in
/-- The **Marcinkiewicz-Zygmund inequality** for symmetric random variables, with a slightly better
constant than `marcinkiewicz_zygmund`. -/
theorem marcinkiewicz_zygmund_symmetric [SecondCountableTopology E] [BorelSpace E]
    (h_indep : iIndepFun X μ)
    (h_ident_neg : ∀ i, IdentDistrib (X i) (-X i) μ μ)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  obtain rfl | hm := eq_or_ne m 0
  · simp [marcinkiewiczZygmundSymmConst]
  have : DecidableEq ι := Classical.decEq _
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  refine (sum_inner_prod_pow_le_sum_prod_norm h_indep h_ident_neg h_lp hm).trans ?_
  have h_rw : (∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖ ∂μ) =
      ∑ I ∈ A ×ˢ A ^^ m with ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i}),
        ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ := by
    congr! with I hi ω
    simp only [mem_filter, mem_piFinset, mem_product, forall_and] at hi
    simp_rw [pow_add, prod_mul_distrib, ← prod_const]
    rw [prod_fiberwise_of_maps_to' (fun x _ ↦ hi.1.2 x),
      prod_fiberwise_of_maps_to' (fun x _ ↦ hi.1.1 x)]
  refine h_rw.trans_le ?_
  refine (sum_norm_pow_eq_sum_multinomial hm h_lp).trans_le ?_
  rw [← map_nsmul_piAntidiag _ _ two_ne_zero]
  simp only [sum_map, Function.Embedding.coeFn_mk]
  calc
    (∑ w ∈ piAntidiag A m, multinomial A (2 • w) * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ)
    _ ≤ ∑ w ∈ piAntidiag A m, marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w *
          ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ := by
        refine sum_le_sum fun w hw ↦ ?_
        gcongr
        calc
          (multinomial A (2 • w) : ℝ)
          _ ≤ ((∑ i ∈ A, w i) ^ ∑ i ∈ A, w i) * multinomial A w :=
            mod_cast multinomial_two_mul_le_mul_multinomial
          _ = marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w := by
            simp [(mem_piAntidiag.1 hw).1, marcinkiewiczZygmundSymmConst]
    _ = marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
        simp_rw [sum_pow_eq_sum_piAntidiag, ← pow_mul, ← integral_const_mul, mul_sum, ← mul_assoc]
        rw [integral_finsetSum]
        rintro w hw
        refine Integrable.const_mul ?_ _
        obtain ⟨hwsum, _⟩ := mem_piAntidiag.mp hw
        have h_sum : (∑ i ∈ A, ((2 * m : ℝ≥0∞) / (2 * (w i : ℝ≥0∞)))⁻¹)⁻¹ = 1 := by
          have h_top : (2 * m : ℝ≥0∞) ≠ ∞ := by finiteness
          have h_nz : (2 * m : ℝ≥0∞) ≠ 0 := by simp_all
          have h_inv (i) : ((2 * m : ℝ≥0∞) / (2 * (w i : ℝ≥0∞)))⁻¹ =
              2 * (w i : ℝ≥0∞) * (2 * m : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.inv_div (Or.inr h_top) (Or.inr h_nz), div_eq_mul_inv]
          rw [sum_congr rfl fun i _ ↦ h_inv i, ← sum_mul, ← mul_sum, ← Nat.cast_sum, hwsum]
          rw [ENNReal.mul_inv_cancel h_nz h_top, inv_one]
        rw [← memLp_one_iff_integrable, ← h_sum]
        exact .prod' fun i hi ↦
          by simpa [← Real.rpow_natCast] using (h_lp i hi).norm_rpow_div (2 * w i)

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] in
private lemma iIndepFun.ite_mem [DecidableEq ι] (h : iIndepFun X μ) :
    iIndepFun (fun i ↦ if i ∈ A then X i else 0) μ := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  by_cases h_zero : ∀ i ∈ S, i ∉ A → (0 : E) ∈ sets i
  · have hpre (i : ι) (hi : i ∈ S) :
        (if i ∈ A then X i else 0) ⁻¹' sets i = if i ∈ A then X i ⁻¹' sets i else Set.univ := by
      split_ifs with hiA
      · simp
      · simpa [Set.eq_univ_iff_forall] using fun _ ↦ h_zero i hi hiA
    have h_in : ∏ i ∈ S with i ∈ A, μ ((if i ∈ A then X i else 0) ⁻¹' sets i)
        = ∏ i ∈ S with i ∈ A, μ (X i ⁻¹' sets i) :=
      prod_congr rfl fun i hi ↦ congrArg μ
        ((hpre i (mem_filter.1 hi).1).trans (if_pos (mem_filter.1 hi).2))
    have h_out : ∏ i ∈ S with i ∉ A, μ ((if i ∈ A then X i else 0) ⁻¹' sets i) = 1 :=
      prod_eq_one fun i hi ↦ (congrArg μ
        ((hpre i (mem_filter.1 hi).1).trans (if_neg (mem_filter.1 hi).2))).trans measure_univ
    calc
      μ (⋂ i ∈ S, (if i ∈ A then X i else 0) ⁻¹' sets i)
        = μ (⋂ i ∈ S.filter (· ∈ A), X i ⁻¹' sets i) := by
          congr 1
          rw [Set.iInter₂_congr hpre]
          ext ω
          simp [mem_filter]
      _ = ∏ i ∈ S with i ∈ A, μ (X i ⁻¹' sets i) :=
          h (S.filter (· ∈ A)) (fun i hi ↦ hsets i (mem_filter.1 hi).1)
      _ = ∏ i ∈ S, μ ((if i ∈ A then X i else 0) ⁻¹' sets i) := by
          rw [← prod_filter_mul_prod_filter_not S (· ∈ A), h_in, h_out, mul_one]
  · push Not at h_zero
    obtain ⟨i₀, hi₀S, hi₀A, hi₀⟩ := h_zero
    have h_empty : (if i₀ ∈ A then X i₀ else 0) ⁻¹' sets i₀ = ∅ := by
      rw [if_neg hi₀A]
      simpa [Set.eq_empty_iff_forall_notMem] using fun _ ↦ hi₀
    have h_measure_inter_zero : μ (⋂ i ∈ S, (if i ∈ A then X i else 0) ⁻¹' sets i) = 0 := by
      rw [← le_zero_iff]
      refine (measure_mono (Set.biInter_subset_of_mem hi₀S)).trans ?_
      simp [h_empty]
    have h_prod_zero : ∏ i ∈ S, μ ((if i ∈ A then X i else 0) ⁻¹' sets i) = 0 := by
      refine prod_eq_zero hi₀S ?_
      simp [h_empty]
    simp_all

omit [IsFiniteMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private lemma iIndepFun.map_pair_prod_pi {κ : Type*} [Fintype κ] {Z : κ → Ω → E}
    (hZ : iIndepFun Z μ) (hZ_meas : ∀ i, Measurable (Z i)) :
    Measure.map (fun ω i ↦ (Z i ω.1, Z i ω.2)) (μ.prod μ) =
      Measure.pi fun i ↦ (μ.map (Z i)).prod (μ.map (Z i)) := by
  have : IsProbabilityMeasure μ := hZ.isProbabilityMeasure
  have (i : κ) : SigmaFinite ((μ.map (Z i)).prod (μ.map (Z i))) := inferInstance
  refine (Measure.pi_eq fun B hB ↦ ?_).symm
  have h_step1_2 : Measure.map (fun ω i ↦ (Z i ω.1, Z i ω.2)) (μ.prod μ) (Set.univ.pi B) =
      ∫⁻ ω₁, μ (⋂ i, Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) ∂μ := by
    have h_pair (i : κ) : Measurable (fun ω : Ω × Ω ↦ (Z i ω.1, Z i ω.2)) :=
      ((hZ_meas i).comp measurable_fst).prodMk ((hZ_meas i).comp measurable_snd)
    rw [Measure.map_apply (measurable_pi_lambda _ h_pair) (.univ_pi hB)]
    have h_eq : (fun ω i ↦ (Z i ω.1, Z i ω.2)) ⁻¹' Set.univ.pi B =
        ⋂ i, (fun ω : Ω × Ω ↦ (Z i ω.1, Z i ω.2)) ⁻¹' B i := by
      ext ω
      simp
    rw [h_eq, Measure.prod_apply (.iInter fun i ↦ (h_pair i) (hB i))]
    congr 1 with ω₁
    congr 1
    ext ω₂
    simp
  have h_step3 (ω₁ : Ω) : μ (⋂ i, Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) =
      ∏ i, μ (Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) := by
    have := hZ.measure_inter_preimage_eq_mul univ
      (sets := fun i ↦ Prod.mk (Z i ω₁) ⁻¹' B i)
      fun i _ ↦ measurable_prodMk_left (hB i)
    simpa using this
  have h_step4 : ∫⁻ ω₁, ∏ i, μ (Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) ∂μ =
      ∏ i, ∫⁻ ω₁, μ (Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) ∂μ := by
    have h_F (i : κ) : Measurable (fun x ↦ μ (Z i ⁻¹' (Prod.mk x ⁻¹' B i))) :=
      measurable_measure_prodMk_left ((measurable_id.prodMap (hZ_meas i)) (hB i))
    simpa using lintegral_prod_eq_prod_lintegral_of_indepFun univ
      (fun i ω₁ ↦ μ (Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)))
      (hZ.comp _ h_F) fun i ↦ (h_F i).comp (hZ_meas i)
  have h_step5 (i : κ) : ∫⁻ ω₁, μ (Z i ⁻¹' (Prod.mk (Z i ω₁) ⁻¹' B i)) ∂μ =
      ((μ.map (Z i)).prod (μ.map (Z i))) (B i) := by
    have h_F : Measurable (fun x ↦ μ (Z i ⁻¹' (Prod.mk x ⁻¹' B i))) :=
      measurable_measure_prodMk_left ((measurable_id.prodMap (hZ_meas i)) (hB i))
    rw [Measure.prod_apply (hB i)]
    have h_eq : ∫⁻ x, (μ.map (Z i)) (Prod.mk x ⁻¹' B i) ∂(μ.map (Z i)) =
        ∫⁻ x, μ (Z i ⁻¹' (Prod.mk x ⁻¹' B i)) ∂(μ.map (Z i)) := by
      congr 1 with x
      rw [Measure.map_apply (hZ_meas i) (measurable_prodMk_left (hB i))]
    rw [h_eq, lintegral_map h_F (hZ_meas i)]
  simp_all

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] in
private lemma sigmaFinite_map_sub_prod [IsProbabilityMeasure μ] [SecondCountableTopology E]
    [BorelSpace E] {Y : Ω → E} (hYm : Measurable Y) :
    SigmaFinite (((μ.map Y).prod (μ.map Y)).map fun q : E × E ↦ q.1 - q.2) :=
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  have : IsProbabilityMeasure (((μ.map Y).prod (μ.map Y)).map fun q : E × E ↦ q.1 - q.2) :=
    Measure.isProbabilityMeasure_map (measurable_fst.sub measurable_snd).aemeasurable
  inferInstance

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] in
private lemma iIndepFun.sub_prod [SecondCountableTopology E] [BorelSpace E]
    (h : iIndepFun X μ) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun (fun i ↦ X i ∘ Prod.fst - X i ∘ Prod.snd) (μ.prod μ) := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  set Y : ι → Ω → E := fun i ↦ (hX_meas i).mk (X i)
  have h_Ym i : Measurable (Y i) := (hX_meas i).measurable_mk
  have h_indep : iIndepFun Y μ := (iIndepFun_congr (fun i ↦ (hX_meas i).ae_eq_mk)).1 h
  have h_ae i : (X i ∘ Prod.fst - X i ∘ Prod.snd) =ᵐ[μ.prod μ] (Y i ∘ Prod.fst - Y i ∘ Prod.snd) :=
    (measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp ((hX_meas i).ae_eq_mk)).sub
      (measurePreserving_snd.quasiMeasurePreserving.ae_eq_comp ((hX_meas i).ae_eq_mk))
  rw [iIndepFun_congr h_ae]
  rw [iIndepFun_iff_finset]
  intro s
  change iIndepFun (fun (i : ↥s) (ω : Ω × Ω) ↦ Y ↑i ω.1 - Y ↑i ω.2) (μ.prod μ)
  have : ∀ i : ↥s, SigmaFinite
      (((μ.map (Y ↑i)).prod (μ.map (Y ↑i))).map fun q : E × E ↦ q.1 - q.2) :=
    fun i ↦ sigmaFinite_map_sub_prod (h_Ym ↑i)
  have h_meas (i : ↥s) : Measurable (fun ω : Ω × Ω ↦ Y ↑i ω.1 - Y ↑i ω.2) :=
    ((h_Ym ↑i).comp measurable_fst).sub ((h_Ym ↑i).comp measurable_snd)
  have h_step2 : (μ.prod μ).map (fun (ω : Ω × Ω) (i : ↥s) ↦ Y ↑i ω.1 - Y ↑i ω.2) =
      ((μ.prod μ).map fun ω (i : ↥s) ↦ (Y ↑i ω.1, Y ↑i ω.2)).map
        fun v (i : ↥s) ↦ (v i).1 - (v i).2 := by
    rw [Measure.map_map]
    · rfl
    · exact measurable_pi_lambda (X := fun _ : ↥s ↦ E) _ fun (i : ↥s) ↦
        ((measurable_pi_apply i).fst).sub ((measurable_pi_apply i).snd)
    · exact measurable_pi_lambda (X := fun _ : ↥s ↦ E × E) _ fun (i : ↥s) ↦
        ((h_Ym ↑i).comp measurable_fst).prodMk ((h_Ym ↑i).comp measurable_snd)
  have h_step3_4 : ((μ.prod μ).map fun ω (i : ↥s) ↦ (Y ↑i ω.1, Y ↑i ω.2)).map
        (fun v (i : ↥s) ↦ (v i).1 - (v i).2) =
      Measure.pi fun i : ↥s ↦
        ((μ.map (Y ↑i)).prod (μ.map (Y ↑i))).map fun q : E × E ↦ q.1 - q.2 := by
    have h_sub : Measurable fun q : E × E ↦ q.1 - q.2 := measurable_fst.sub measurable_snd
    rw [iIndepFun.map_pair_prod_pi (Z := fun i : ↥s ↦ Y ↑i) (h_indep.restrict s)
      fun i : ↥s ↦ h_Ym ↑i, Measure.pi_map_pi fun i ↦ h_sub.aemeasurable]
  have h_step5_sub : (Measure.pi fun i : ↥s ↦
        ((μ.map (Y ↑i)).prod (μ.map (Y ↑i))).map fun q : E × E ↦ q.1 - q.2) =
      Measure.pi fun i : ↥s ↦ (μ.prod μ).map fun ω : Ω × Ω ↦ Y ↑i ω.1 - Y ↑i ω.2 := by
    have h_sub : Measurable fun q : E × E ↦ q.1 - q.2 := measurable_fst.sub measurable_snd
    refine congrArg Measure.pi (funext fun i ↦ ?_)
    rw [Measure.map_prod_map _ _ (h_Ym ↑i) (h_Ym ↑i),
      Measure.map_map h_sub ((h_Ym ↑i).prodMap (h_Ym ↑i))]
    rfl
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (h_meas i).aemeasurable,
    h_step2, h_step3_4, h_step5_sub]

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for random variables with zero
mean. -/
noncomputable def marcinkiewiczZygmundConst (p : ℝ≥0) : ℝ :=
  4 ^ (p / 2 : ℝ) * marcinkiewiczZygmundSymmConst p

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] [MeasurableSpace E] in
private lemma integrable_norm_pow_sum (hm : m ≠ 0) (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    Integrable (fun ω ↦ (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m) μ := by
  have h_mem : MemLp (fun ω ↦ ∑ i ∈ A, ‖X i ω‖ ^ 2) m μ := by
    refine memLp_finsetSum A fun i hi ↦ ?_
    have := (h_lp i hi).norm_rpow_div 2
    rw [ENNReal.toReal_ofNat, mul_comm (2 : ℝ≥0∞),
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)] at this
    simp_all
  refine (h_mem.integrable_norm_pow hm).congr ?_
  exact ae_of_all _ fun ω ↦
    congrArg (· ^ m) (Real.norm_of_nonneg (sum_nonneg fun i _ ↦ sq_nonneg _))

/-- The **Marcinkiewicz-Zygmund inequality** for random variables with zero mean.

For symmetric random variables, `marcinkiewicz_zygmund` provides a slightly better constant. -/
theorem marcinkiewicz_zygmund [SecondCountableTopology E] [BorelSpace E] [CompleteSpace E]
    (h_indep : iIndepFun X μ)
    (h_int : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  obtain rfl | hm := eq_or_ne m 0
  · unfold marcinkiewiczZygmundConst marcinkiewiczZygmundSymmConst
    simp
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have : DecidableEq ι := Classical.decEq _
  refine (symmetrize_inequality h_indep h_int h_lp hm).trans ?_
  let Z i := symmetrize (if i ∈ A then X i else 0)
  have h_ae_meas (i : ι) : AEMeasurable (Z i) (μ.prod μ) := by
    simp only [symmetrize, Z]
    have h_meas_ite : AEMeasurable (if i ∈ A then X i else 0) μ := by
      split_ifs with hi
      · exact (h_lp i hi).aestronglyMeasurable.aemeasurable
      · exact aemeasurable_const
    exact (h_meas_ite.comp_quasiMeasurePreserving
      measurePreserving_fst.quasiMeasurePreserving).sub
      (h_meas_ite.comp_quasiMeasurePreserving
      measurePreserving_snd.quasiMeasurePreserving)
  have h_ident_neg (i : ι) :
      IdentDistrib (Z i) (-Z i) (μ.prod μ) (μ.prod μ) := by
    refine ⟨h_ae_meas i, (h_ae_meas i).neg, ?_⟩
    have h_swap : -Z i = Z i ∘ Prod.swap := by
      ext ω
      simp [symmetrize, Z]
    have h_swap_meas : AEMeasurable (Z i) (Measure.map Prod.swap (μ.prod μ)) := by
      rw [Measure.prod_swap]
      exact h_ae_meas i
    calc
      Measure.map (Z i) (μ.prod μ)
      _ = Measure.map (Z i) (Measure.map Prod.swap (μ.prod μ)) := by
          rw [Measure.prod_swap]
      _ = Measure.map (Z i ∘ Prod.swap) (μ.prod μ) :=
          AEMeasurable.map_map_of_aemeasurable h_swap_meas measurable_swap.aemeasurable
      _ = Measure.map (-Z i) (μ.prod μ) := by simp_all
  have h_indep_symm : iIndepFun Z (μ.prod μ) := by
    have h_ite_mem : iIndepFun (fun i ↦ if i ∈ A then X i else 0) μ :=
      iIndepFun.ite_mem h_indep
    have h_ae_meas i : AEMeasurable (if i ∈ A then X i else (0 : Ω → E)) μ := by
      split_ifs with hi
      · exact (h_lp i hi).aestronglyMeasurable.aemeasurable
      · exact aemeasurable_const
    have h_x_eq : Z = fun i ↦ (if i ∈ A then X i else 0) ∘ Prod.fst -
        (if i ∈ A then X i else 0) ∘ Prod.snd := by
      ext i ω
      simp [symmetrize, Z]
    rw [h_x_eq]
    exact iIndepFun.sub_prod h_ite_mem h_ae_meas
  have h_sum_eq (ω : Ω × Ω) :
      ∑ i ∈ A, symmetrize (X i) ω = ∑ i ∈ A, Z i ω :=
    sum_congr rfl fun i hi ↦ by simp [Z, hi]
  have h_sum_eq' (ω : Ω × Ω) :
      (∑ i ∈ A, ‖Z i ω‖ ^ 2) ^ m =
        (∑ i ∈ A, ‖symmetrize (X i) ω‖ ^ 2) ^ m := by
    congr 1
    exact sum_congr rfl fun i hi ↦ by simp [Z, hi]
  simp_rw [h_sum_eq]
  refine (marcinkiewicz_zygmund_symmetric h_indep_symm
    h_ident_neg (fun i hi ↦ ?_)).trans ?_
  · have : (if i ∈ A then X i else 0) = X i := if_pos hi
    rw [show Z i = symmetrize (if i ∈ A then X i else 0) by rfl, this]
    exact memLp_symmetrize (h_lp i hi)
  simp_rw [h_sum_eq']
  have h_symm₀ : 0 ≤ marcinkiewiczZygmundSymmConst (2 * m) := by
    unfold marcinkiewiczZygmundSymmConst
    positivity
  have h_int_s_pow : Integrable (fun ω ↦ (∑ i ∈ A, ‖symmetrize (X i) ω‖ ^ 2) ^ m) (μ.prod μ) := by
    have h_mem : MemLp (fun ω ↦ ∑ i ∈ A, ‖symmetrize (X i) ω‖ ^ 2) m (μ.prod μ) := by
      refine memLp_finsetSum A fun i hi ↦ ?_
      have := (memLp_symmetrize (h_lp i hi)).norm_rpow_div 2
      rw [ENNReal.toReal_ofNat, mul_comm (2 : ℝ≥0∞),
        ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)] at this
      simp_all
    refine (h_mem.integrable_norm_pow hm).congr ?_
    exact ae_of_all _ fun ω ↦
      congrArg (· ^ m) (Real.norm_of_nonneg (sum_nonneg fun i _ ↦ sq_nonneg _))
  have h_int_s_pow_le : Integrable (fun x : Ω × Ω ↦ 2 ^ (2 * m - 1) *
      ((∑ i ∈ A, ‖X i x.1‖ ^ 2) ^ m + (∑ i ∈ A, ‖X i x.2‖ ^ 2) ^ m)) (μ.prod μ) := by
    have h_int_fst : Integrable (fun ω : Ω × Ω ↦ (∑ i ∈ A, ‖X i ω.1‖ ^ 2) ^ m) (μ.prod μ) :=
      (integrable_norm_pow_sum hm h_lp).comp_fst μ
    have h_int_snd : Integrable (fun ω : Ω × Ω ↦ (∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m) (μ.prod μ) :=
      (integrable_norm_pow_sum hm h_lp).comp_snd μ
    exact Integrable.const_mul (h_int_fst.add h_int_snd) _
  refine (mul_le_mul_of_nonneg_left (integral_mono
    h_int_s_pow h_int_s_pow_le symmetrize_le_norm_pow) h_symm₀).trans_eq ?_
  have h_int_fst := (integrable_norm_pow_sum hm h_lp).comp_fst μ
  have h_int_snd := (integrable_norm_pow_sum hm h_lp).comp_snd μ
  have h_pow : (2 : ℝ) ^ (2 * m - 1) * 2 = 4 ^ m := by
    have : 2 * m - 1 + 1 = 2 * m := by lia
    rw [← pow_succ, this, pow_mul]
    norm_num
  have h_const : marcinkiewiczZygmundConst (2 * m) =
      4 ^ m * marcinkiewiczZygmundSymmConst (2 * m) := by
    rw [marcinkiewiczZygmundConst]
    simp
  have h_int_fst_eq : ∫ ω : Ω × Ω, (∑ i ∈ A, ‖X i ω.1‖ ^ 2) ^ m ∂μ.prod μ =
      ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
    have h_map_fst : Measure.map Prod.fst (μ.prod μ) = μ := measurePreserving_fst.map_eq
    conv_rhs => rw [← h_map_fst]
    refine (integral_map measurable_fst.aemeasurable
      (f := fun ω ↦ (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m) ?_).symm
    exact h_map_fst.symm ▸ (integrable_norm_pow_sum hm h_lp).aestronglyMeasurable
  have h_int_snd_eq : ∫ ω : Ω × Ω, (∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m ∂μ.prod μ =
      ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
    have h_map_snd : Measure.map Prod.snd (μ.prod μ) = μ := measurePreserving_snd.map_eq
    conv_rhs => rw [← h_map_snd]
    refine (integral_map measurable_snd.aemeasurable
      (f := fun ω ↦ (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m) ?_).symm
    exact h_map_snd.symm ▸ (integrable_norm_pow_sum hm h_lp).aestronglyMeasurable
  rw [integral_const_mul, integral_add h_int_fst h_int_snd,
    h_int_fst_eq, h_int_snd_eq, h_const, ← h_pow]
  ring
