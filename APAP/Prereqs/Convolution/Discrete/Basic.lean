module

public import APAP.Mathlib.Algebra.Star.Conjneg
public import APAP.Prereqs.Mu
public import APAP.Prereqs.Convolution.Discrete.Defs

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Analysis.Complex.Order

/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `ddconv`: Discrete convolution of two functions
* `dddconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

## Notation

* `f ∗ᵈ g`: Convolution
* `f ○ᵈ g`: Difference convolution
* `f ∗ᵈ^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

@[expose] public section

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator mu

variable {G R γ : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ᵈ g` and difference convolution `f ○ᵈ g` of functions
`f g : G → R`, and show how they interact.
-/

section CommSemiring
variable [CommSemiring R] {f g : G → R}

lemma indicator_one_ddconv_indicator_one_eq_sum (s t : Finset G) (a : G) :
    (𝟭_[s, R] ∗ᵈ 𝟭_[t]) a = #{x ∈ s ×ˢ t | x.1 + x.2 = a} := by
  simp only [ddconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole]
  simp_rw [mem_coe, ← mem_product, filter_univ_mem]

lemma indicator_one_ddconv (s : Finset G) (f : G → R) : 𝟭_[s] ∗ᵈ f = ∑ a ∈ s, τ a f := by
  ext; simp [ddconv_eq_sum_sub', Set.indicator_apply]

lemma ddconv_indicator_one (f : G → R) (s : Finset G) : f ∗ᵈ 𝟭_[s] = ∑ a ∈ s, τ a f := by
  ext; simp [ddconv_eq_sum_sub, Set.indicator_apply]

lemma indicator_one_ddconv_indicator_one_eq_card_vadd_inter_neg (s t : Finset G) (a : G) :
    (𝟭_[s, R] ∗ᵈ 𝟭_[t]) a = #((-a +ᵥ s) ∩ -t) := by
  rw [← card_neg, neg_inter]
  simp [ddconv_indicator_one, Set.indicator_apply, inter_comm, ← filter_mem_eq_inter,
    ← neg_vadd_mem_iff, ← sub_eq_add_neg]

variable [StarRing R]

lemma indicator_one_dddconv_Set.indicator_apply (s t : Finset G) (a : G) :
    (𝟭_[s, R] ○ᵈ 𝟭_[t]) a = #{x ∈ s ×ˢ t | x.1 - x.2 = a} := by
  simp only [dddconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero, Pi.conj_apply]
  simp_rw [mem_coe, ← mem_product, filter_univ_mem]

lemma indicator_one_dddconv (s : Finset G) (f : G → R) : 𝟭_[s] ○ᵈ f = ∑ a ∈ s, τ a (conjneg f) := by
  ext; simp [dddconv_eq_sum_sub', Set.indicator_apply]

lemma dddconv_indicator_one_eq_sum (f : G → R) (s : Finset G) :
    f ○ᵈ 𝟭_[s] = ∑ a ∈ s, τ (-a) f := by
  ext; simp [dddconv_eq_sum_add, Set.indicator_apply]

lemma dddconv_indicator_one (f : G → R) (s : Finset G) : f ○ᵈ 𝟭_[s] = f ∗ᵈ 𝟭_[-s] := by
  rw [← ddconv_conjneg]
  simp

end CommSemiring

section Semifield
variable [Semifield R]

@[simp] lemma mu_univ_ddconv_mu_univ : μ_[R] (univ : Finset G) ∗ᵈ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, ddconv_eq_sum_add, card_univ, *]

lemma mu_ddconv (s : Finset G) (f : G → R) : μ s ∗ᵈ f = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, indicator_one_ddconv, smul_ddconv]

lemma ddconv_mu (f : G → R) (s : Finset G) : f ∗ᵈ μ s = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, ddconv_indicator_one, ddconv_smul]

variable [StarRing R]

@[simp] lemma mu_univ_dddconv_mu_univ : μ_[R] (univ : Finset G) ○ᵈ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, dddconv_eq_sum_add, card_univ, *]

lemma mu_dddconv (s : Finset G) (f : G → R) :
    μ s ○ᵈ f = (#s : R)⁻¹ • ∑ a ∈ s, τ a (conjneg f) := by
  simp [mu, indicator_one_dddconv, smul_dddconv]

lemma dddconv_mu (f : G → R) (s : Finset G) : f ○ᵈ μ s = (#s : R)⁻¹ • ∑ a ∈ s, τ (-a) f := by
  simp [mu, dddconv_indicator_one_eq_sum, dddconv_smul]

end Semifield

section Semifield
variable [Semifield R] [CharZero R]

lemma expect_ddconv (f g : G → R) : 𝔼 a, (f ∗ᵈ g) a = (∑ a, f a) * 𝔼 a, g a := by
  simp_rw [expect, sum_ddconv, mul_smul_comm]

lemma expect_ddconv' (f g : G → R) : 𝔼 a, (f ∗ᵈ g) a = (𝔼 a, f a) * ∑ a, g a := by
  simp_rw [expect, sum_ddconv, smul_mul_assoc]

variable [StarRing R]

lemma expect_dddconv (f g : G → R) : 𝔼 a, (f ○ᵈ g) a = (∑ a, f a) * 𝔼 a, conj (g a) := by
  simp_rw [expect, sum_dddconv, mul_smul_comm]

lemma expect_dddconv' (f g : G → R) : 𝔼 a, (f ○ᵈ g) a = (𝔼 a, f a) * ∑ a, conj (g a) := by
  simp_rw [expect, sum_dddconv, smul_mul_assoc]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_ddconv (f g : G → R) : balance (f ∗ᵈ g) = balance f ∗ᵈ balance g := by
  simpa [balance, ddconv_sub, sub_ddconv, expect_ddconv]
    using! (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

variable [StarRing R]

@[simp] lemma balance_dddconv (f g : G → R) : balance (f ○ᵈ g) = balance f ○ᵈ balance g := by
  simpa [balance, dddconv_sub, sub_dddconv, expect_dddconv, map_expect]
    using! (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

end Field

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

lemma indicator_one_iterConv_apply (s : Finset G) :
    ∀ (n : ℕ) (a : G), (𝟭_[s, R] ∗ᵈ^ n) a = #{x ∈ s ^^ n | ∑ i, x i = a}
  | 0, a => by simp [apply_ite card, eq_comm]
  | n + 1, a => by
    simp_rw [iterConv_succ', ddconv_eq_sum_sub', indicator_one_iterConv_apply, Set.indicator_apply,
      boole_mul, sum_ite, mem_coe, filter_univ_mem, sum_const_zero, add_zero, ← Nat.cast_sum,
      ← Finset.card_sigma]
    congr 1
    refine card_equiv ((Equiv.sigmaEquivProd ..).trans <| Fin.consEquiv fun _ ↦ G) ?_
    aesop (add simp [Fin.sum_cons, Fin.forall_fin_succ])

lemma indicator_one_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    𝟭_[s] ∗ᵈ^ n ∗ᵈ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [ddconv_eq_sum_sub', indicator_one_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul, ← sum_const, Finset.sum_fiberwise']

lemma ddconv_indicator_one_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ∗ᵈ 𝟭_[s] ∗ᵈ^ n = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [ddconv_eq_sum_sub, indicator_one_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul', ← sum_const, Finset.sum_fiberwise']

variable [StarRing R]

lemma indicator_one_iterConv_dddconv (s : Finset G) (n : ℕ) (f : G → R) :
    𝟭_[s] ∗ᵈ^ n ○ᵈ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) (conjneg f) := by
  rw [← ddconv_conjneg, indicator_one_iterConv_ddconv]

lemma dddconv_indicator_one_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ○ᵈ 𝟭_[s] ∗ᵈ^ n = ∑ a ∈ s ^^ n, τ (-∑ i, a i) f := by
  simp [← ddconv_conjneg, conjneg_iterConv, ← coe_neg, ddconv_indicator_one_iterConv, piFinset_neg]

end CommSemiring

section Semifield
variable [Semifield R] [CharZero R]

lemma mu_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    μ s ∗ᵈ^ n ∗ᵈ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  simp only [mu, smul_iterConv, inv_pow, smul_ddconv, indicator_one_iterConv_ddconv, expect,
    card_piFinset_const, Nat.cast_pow]
  rw [← NNRat.cast_smul_eq_nnqsmul R]
  push_cast
  rfl

lemma ddconv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ∗ᵈ μ s ∗ᵈ^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  rw [ddconv_comm, mu_iterConv_ddconv]

lemma Finset.dens_addSubgroup_preimage_vadd_eq_indicator_one_ddconv_mu (a : G) (B : Finset G)
    {S : Type*} [SetLike S G] [AddSubgroupClass S G] (V : S) [Fintype V] :
    ((-a +ᵥ B).preimage (↑) Set.injOn_subtype_val : Finset V).dens =
      (𝟭_[B, R] ∗ᵈ μ (V : Set G).toFinset) a := by
  rw [mu, ddconv_smul, Pi.smul_apply, indicator_one_ddconv_indicator_one_eq_card_vadd_inter_neg,
    nnratCast_dens, card_preimage, smul_eq_mul, inv_mul_eq_div]
  congr
  · congr 1 with x
    simp
  · simp

variable [StarRing R]

lemma mu_iterConv_dddconv (s : Finset G) (n : ℕ) (f : G → R) :
    μ s ∗ᵈ^ n ○ᵈ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) (conjneg f) := by
  rw [← ddconv_conjneg, mu_iterConv_ddconv]

lemma dddconv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ○ᵈ μ s ∗ᵈ^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (-∑ i, a i) f := by
  simp_rw [← ddconv_conjneg, conjneg_iterConv, conjneg_mu, ddconv_mu_iterConv, piFinset_neg,
    expect_neg_index, Pi.neg_apply, sum_neg_distrib]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_iterConv (f : G → R) : ∀ {n}, n ≠ 0 → balance (f ∗ᵈ^ n) = balance f ∗ᵈ^ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterConv_succ _ (n + 1), balance_iterConv _ n.succ_ne_zero]

end Field
