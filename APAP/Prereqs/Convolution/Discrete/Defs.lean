module

public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.NNReal.Star
public import Mathlib.Basic.Complex.Basic

import Mathlib.Analysis.Complex.Basic

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

open Finset Fintype Function
open scoped ComplexConjugate NNReal Pointwise translate

variable {G H R S : Type*} [DecidableEq G] [AddCommGroup G]

/-! ### Trivial character -/

section CommSemiring
variable [CommSemiring R]

/-- The trivial character. -/
def trivChar : G → R := fun a ↦ if a = 0 then 1 else 0

@[simp] lemma trivChar_apply (a : G) : (trivChar a : R) = if a = 0 then 1 else 0 := rfl

variable [StarRing R]

@[simp] lemma conj_trivChar : conj (trivChar : G → R) = trivChar := by ext; simp
@[simp] lemma conjneg_trivChar : conjneg (trivChar : G → R) = trivChar := by ext; simp

@[simp] lemma isSelfAdjoint_trivChar : IsSelfAdjoint (trivChar : G → R) := conj_trivChar

end CommSemiring

variable [Fintype G]

/-! ### Convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R}

/-- Convolution -/
def ddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 + x.2 = a , f x.1 * g x.2

infixl:71 " ∗ᵈ " => ddconv

lemma ddconv_apply (f g : G → R) (a : G) :
    (f ∗ᵈ g) a = ∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl

@[simp] lemma ddconv_zero (f : G → R) : f ∗ᵈ 0 = 0 := by ext; simp [ddconv_apply]
@[simp] lemma zero_ddconv (f : G → R) : 0 ∗ᵈ f = 0 := by ext; simp [ddconv_apply]

lemma ddconv_add (f g h : G → R) : f ∗ᵈ (g + h) = f ∗ᵈ g + f ∗ᵈ h := by
  ext; simp [ddconv_apply, mul_add, sum_add_distrib]

lemma add_ddconv (f g h : G → R) : (f + g) ∗ᵈ h = f ∗ᵈ h + g ∗ᵈ h := by
  ext; simp [ddconv_apply, add_mul, sum_add_distrib]

lemma smul_ddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ∗ᵈ g = c • (f ∗ᵈ g) := by ext a; simp [ddconv_apply, smul_sum, smul_mul_assoc]

lemma ddconv_smul [DistribSMul H R] [SMulCommClass H R R] (c : H) (f g : G → R) :
    f ∗ᵈ c • g = c • (f ∗ᵈ g) := by ext a; simp [ddconv_apply, smul_sum, mul_smul_comm]

alias smul_ddconv_assoc := smul_ddconv
alias smul_ddconv_left_comm := ddconv_smul

@[simp] lemma translate_ddconv (a : G) (f g : G → R) : τ a f ∗ᵈ g = τ a (f ∗ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma ddconv_translate (a : G) (f g : G → R) : f ∗ᵈ τ a g = τ a (f ∗ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

lemma ddconv_comm (f g : G → R) : f ∗ᵈ g = g ∗ᵈ f :=
  funext fun a ↦ sum_equiv (Equiv.prodComm _ _) (by simp [add_comm]) <| by simp [mul_comm]

lemma mul_smul_ddconv_comm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c d : H) (f g : G → R) : (c * d) • (f ∗ᵈ g) = c • f ∗ᵈ d • g := by
  rw [smul_ddconv, ddconv_smul, mul_smul]

lemma ddconv_assoc (f g h : G → R) : f ∗ᵈ g ∗ᵈ h = f ∗ᵈ (g ∗ᵈ h) := by
  ext a
  simp only [sum_mul, mul_sum, ddconv_apply, Finset.sum_sigma']
  apply sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
    (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

lemma ddconv_right_comm (f g h : G → R) : f ∗ᵈ g ∗ᵈ h = f ∗ᵈ h ∗ᵈ g := by
  rw [ddconv_assoc, ddconv_assoc, ddconv_comm g]

lemma ddconv_left_comm (f g h : G → R) : f ∗ᵈ (g ∗ᵈ h) = g ∗ᵈ (f ∗ᵈ h) := by
  rw [← ddconv_assoc, ← ddconv_assoc, ddconv_comm g]

lemma ddconv_rotate (f g h : G → R) : f ∗ᵈ g ∗ᵈ h = g ∗ᵈ h ∗ᵈ f := by rw [ddconv_assoc, ddconv_comm]
lemma ddconv_rotate' (f g h : G → R) : f ∗ᵈ (g ∗ᵈ h) = g ∗ᵈ (h ∗ᵈ f) := by
  rw [ddconv_comm, ← ddconv_assoc]

lemma ddconv_ddconv_ddconv_comm (f g h i : G → R) : f ∗ᵈ g ∗ᵈ (h ∗ᵈ i) = f ∗ᵈ h ∗ᵈ (g ∗ᵈ i) := by
  rw [ddconv_assoc, ddconv_assoc, ddconv_left_comm g]

lemma map_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) (a : G) :
    m ((f ∗ᵈ g) a) = (m ∘ f ∗ᵈ m ∘ g) a := by simp [ddconv_apply, map_sum, map_mul]

lemma comp_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) : m ∘ (f ∗ᵈ g) = m ∘ f ∗ᵈ m ∘ g :=
  funext <| map_ddconv _ _ _

lemma ddconv_eq_sum_sub (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f (a - t) * g t := by
  rw [ddconv_apply]; apply sum_nbij' Prod.snd (fun b ↦ (a - b, b)) <;> aesop

lemma ddconv_eq_sum_add (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f (a + t) * g (-t) :=
  (ddconv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma ddconv_eq_sum_sub' (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f t * g (a - t) := by
  rw [ddconv_comm, ddconv_eq_sum_sub]; simp_rw [mul_comm]

lemma ddconv_eq_sum_add' (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f (-t) * g (a + t) := by
  rw [ddconv_comm, ddconv_eq_sum_add]; simp_rw [mul_comm]

lemma ddconv_apply_add (f g : G → R) (a b : G) : (f ∗ᵈ g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
  (ddconv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc]

lemma sum_ddconv_mul (f g h : G → R) : ∑ a, (f ∗ᵈ g) a * h a = ∑ a, ∑ b, f a * g b * h (a + b) := by
  simp_rw [ddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma sum_ddconv (f g : G → R) : ∑ a, (f ∗ᵈ g) a = (∑ a, f a) * ∑ a, g a := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_ddconv_mul f g 1

@[simp] lemma ddconv_const (f : G → R) (b : R) : f ∗ᵈ const _ b = const _ ((∑ x, f x) * b) := by
  ext; simp [ddconv_eq_sum_sub', sum_mul]

@[simp] lemma const_ddconv (b : R) (f : G → R) : const _ b ∗ᵈ f = const _ (b * ∑ x, f x) := by
  ext; simp [ddconv_eq_sum_sub, mul_sum]

@[simp] lemma ddconv_trivChar (f : G → R) : f ∗ᵈ trivChar = f := by ext a; simp [ddconv_eq_sum_sub]
@[simp] lemma trivChar_ddconv (f : G → R) : trivChar ∗ᵈ f = f := by
  rw [ddconv_comm, ddconv_trivChar]

lemma support_ddconv_subset (f g : G → R) : support (f ∗ᵈ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_sum_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

/-! ### Difference convolution -/

variable [StarRing R]

/-- Difference convolution -/
def dddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

infixl:71 " ○ᵈ " => dddconv

lemma dddconv_apply (f g : G → R) (a : G) :
    (f ○ᵈ g) a = ∑ x : G × G with x.1 - x.2 = a , f x.1 * conj g x.2 := rfl

@[simp] lemma dddconv_zero (f : G → R) : f ○ᵈ 0 = 0 := by ext; simp [dddconv_apply]
@[simp] lemma zero_dddconv (f : G → R) : 0 ○ᵈ f = 0 := by ext; simp [dddconv_apply]
@[simp] lemma dddconv_fun_zero (f : G → R) : f ○ᵈ (fun _ ↦ 0) = 0 := by ext; simp [dddconv_apply]
@[simp] lemma fun_zero_dddconv (f : G → R) : (fun _ ↦ 0) ○ᵈ f = 0 := by ext; simp [dddconv_apply]

lemma dddconv_add (f g h : G → R) : f ○ᵈ (g + h) = f ○ᵈ g + f ○ᵈ h := by
  ext; simp [dddconv_apply, mul_add, sum_add_distrib]

lemma add_dddconv (f g h : G → R) : (f + g) ○ᵈ h = f ○ᵈ h + g ○ᵈ h := by
  ext; simp [dddconv_apply, add_mul, sum_add_distrib]

lemma smul_dddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ○ᵈ g = c • (f ○ᵈ g) := by ext; simp [dddconv_apply, smul_sum, smul_mul_assoc]

lemma dddconv_smul [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c : H)
    (f g : G → R) : f ○ᵈ c • g = star c • (f ○ᵈ g) := by
  ext; simp [dddconv_apply, smul_sum, mul_smul_comm, starRingEnd_apply, star_smul]

@[simp] lemma translate_dddconv (a : G) (f g : G → R) : τ a f ○ᵈ g = τ a (f ○ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma dddconv_translate (a : G) (f g : G → R) : f ○ᵈ τ a g = τ (-a) (f ○ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

@[simp] lemma ddconv_conjneg (f g : G → R) : f ∗ᵈ conjneg g = f ○ᵈ g :=
  funext fun a ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.neg _) (by simp) (by simp)

@[simp] lemma dddconv_conjneg (f g : G → R) : f ○ᵈ conjneg g = f ∗ᵈ g := by
  rw [← ddconv_conjneg, conjneg_conjneg]

@[simp]
lemma conj_ddconv_apply (f g : G → R) (a : G) : conj ((f ∗ᵈ g) a) = (conj f ∗ᵈ conj g) a := by
  simp only [Pi.conj_apply, ddconv_apply, map_sum, map_mul]

@[simp]
lemma conj_dddconv_apply (f g : G → R) (a : G) : conj ((f ○ᵈ g) a) = (conj f ○ᵈ conj g) a := by
  simp_rw [← ddconv_conjneg, conj_ddconv_apply, conjneg_conj]

@[simp] lemma conj_ddconv (f g : G → R) : conj (f ∗ᵈ g) = conj f ∗ᵈ conj g :=
  funext <| conj_ddconv_apply _ _

@[simp] lemma conj_dddconv (f g : G → R) : conj (f ○ᵈ g) = conj f ○ᵈ conj g :=
  funext <| conj_dddconv_apply _ _

lemma IsSelfAdjoint.ddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ᵈ g) :=
  (conj_ddconv _ _).trans <| congr_arg₂ _ hf hg

lemma IsSelfAdjoint.dddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (f ○ᵈ g) := (conj_dddconv _ _).trans <| congr_arg₂ _ hf hg

@[simp] lemma conjneg_ddconv (f g : G → R) : conjneg (f ∗ᵈ g) = conjneg f ∗ᵈ conjneg g := by
  funext a
  simp only [ddconv_apply, conjneg_apply, map_sum, map_mul]
  exact sum_equiv (Equiv.neg _) (by simp [← neg_eq_iff_eq_neg, add_comm]) (by simp)

@[simp] lemma conjneg_dddconv (f g : G → R) : conjneg (f ○ᵈ g) = g ○ᵈ f := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, conjneg_conjneg, ddconv_comm]
alias smul_dddconv_assoc := smul_dddconv
alias smul_dddconv_left_comm := dddconv_smul

lemma dddconv_right_comm (f g h : G → R) : f ○ᵈ g ○ᵈ h = f ○ᵈ h ○ᵈ g := by
  simp_rw [← ddconv_conjneg, ddconv_right_comm]

lemma ddconv_dddconv_assoc (f g h : G → R) : f ∗ᵈ g ○ᵈ h = f ∗ᵈ (g ○ᵈ h) := by
  simp_rw [← ddconv_conjneg, ddconv_assoc]

lemma ddconv_dddconv_left_comm (f g h : G → R) : f ∗ᵈ (g ○ᵈ h) = g ∗ᵈ (f ○ᵈ h) := by
  simp_rw [← ddconv_conjneg, ddconv_left_comm]

lemma ddconv_dddconv_right_comm (f g h : G → R) : f ∗ᵈ g ○ᵈ h = f ○ᵈ h ∗ᵈ g := by
  simp_rw [← ddconv_conjneg, ddconv_right_comm]

lemma ddconv_dddconv_ddconv_comm (f g h i : G → R) : f ∗ᵈ g ○ᵈ (h ∗ᵈ i) = f ○ᵈ h ∗ᵈ (g ○ᵈ i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]

lemma dddconv_ddconv_dddconv_comm (f g h i : G → R) : f ○ᵈ g ∗ᵈ (h ○ᵈ i) = f ∗ᵈ h ○ᵈ (g ∗ᵈ i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]

lemma dddconv_dddconv_dddconv_comm (f g h i : G → R) : f ○ᵈ g ○ᵈ (h ○ᵈ i) = f ○ᵈ h ○ᵈ (g ○ᵈ i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]

--TODO: Can we generalise to star ring homs?
lemma map_dddconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ᵈ g) a) : ℝ) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := by
  simp_rw [dddconv_apply, NNReal.coe_sum, NNReal.coe_mul, starRingEnd_apply, star_trivial,
    Function.comp_apply]

lemma comp_dddconv (f g : G → ℝ≥0) : ((↑) ∘ (f ○ᵈ g) : G → ℝ) = (↑) ∘ f ○ᵈ (↑) ∘ g :=
  funext <| map_dddconv _ _

lemma dddconv_eq_sum_sub (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f (a - t) * conj (g (-t)) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_sub]

lemma dddconv_eq_sum_add (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f (a + t) * conj (g t) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_add]

lemma dddconv_eq_sum_sub' (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f t * conj (g (t - a)) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_sub']

lemma dddconv_eq_sum_add' (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f (-t) * conj g (-(a + t)) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_add']

lemma dddconv_apply_neg (f g : G → R) (a : G) : (f ○ᵈ g) (-a) = conj ((g ○ᵈ f) a) := by
  rw [← conjneg_dddconv f, conjneg_apply, Complex.conj_conj]

lemma dddconv_apply_sub (f g : G → R) (a b : G) :
    (f ○ᵈ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) := by
  simp [← ddconv_conjneg, sub_eq_add_neg, ddconv_apply_add, add_comm]

lemma sum_dddconv_mul (f g h : G → R) :
    ∑ a, (f ○ᵈ g) a * h a = ∑ a, ∑ b, f a * conj (g b) * h (a - b) := by
  simp_rw [dddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact Fintype.sum_congr _ _ fun x ↦ Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma sum_dddconv (f g : G → R) : ∑ a, (f ○ᵈ g) a = (∑ a, f a) * ∑ a, conj (g a) := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_dddconv_mul f g 1

@[simp]
lemma dddconv_const (f : G → R) (b : R) : f ○ᵈ const _ b = const _ ((∑ x, f x) * conj b) := by
  ext; simp [dddconv_eq_sum_sub', sum_mul]

@[simp]
lemma const_dddconv (b : R) (f : G → R) : const _ b ○ᵈ f = const _ (b * ∑ x, conj (f x)) := by
  ext; simp [dddconv_eq_sum_add, mul_sum]

@[simp]
lemma dddconv_trivChar (f : G → R) : f ○ᵈ trivChar = f := by ext a; simp [dddconv_eq_sum_add]

@[simp] lemma trivChar_dddconv (f : G → R) : trivChar ○ᵈ f = conjneg f := by
  rw [← ddconv_conjneg, trivChar_ddconv]

lemma support_dddconv_subset (f g : G → R) : support (f ○ᵈ g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_ddconv_subset f (conjneg g)

end CommSemiring

section CommRing
variable [CommRing R]

@[simp] lemma ddconv_neg (f g : G → R) : f ∗ᵈ -g = -(f ∗ᵈ g) := by ext; simp [ddconv_apply]
@[simp] lemma neg_ddconv (f g : G → R) : -f ∗ᵈ g = -(f ∗ᵈ g) := by ext; simp [ddconv_apply]

lemma ddconv_sub (f g h : G → R) : f ∗ᵈ (g - h) = f ∗ᵈ g - f ∗ᵈ h := by
  simp only [sub_eq_add_neg, ddconv_add, ddconv_neg]

lemma sub_ddconv (f g h : G → R) : (f - g) ∗ᵈ h = f ∗ᵈ h - g ∗ᵈ h := by
  simp only [sub_eq_add_neg, add_ddconv, neg_ddconv]

variable [StarRing R]

@[simp] lemma dddconv_neg (f g : G → R) : f ○ᵈ -g = -(f ○ᵈ g) := by ext; simp [dddconv_apply]
@[simp] lemma neg_dddconv (f g : G → R) : -f ○ᵈ g = -(f ○ᵈ g) := by ext; simp [dddconv_apply]

lemma dddconv_sub (f g h : G → R) : f ○ᵈ (g - h) = f ○ᵈ g - f ○ᵈ h := by
  simp only [sub_eq_add_neg, dddconv_add, dddconv_neg]

lemma sub_dddconv (f g h : G → R) : (f - g) ○ᵈ h = f ○ᵈ h - g ○ᵈ h := by
  simp only [sub_eq_add_neg, add_dddconv, neg_dddconv]

end CommRing

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

@[simp, norm_cast]
lemma coe_ddconv : (↑((f ∗ᵈ g) a) : 𝕜) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a :=
  map_ddconv (algebraMap ℝ 𝕜) _ _ _

@[simp, norm_cast]
lemma coe_dddconv : (↑((f ○ᵈ g) a) : 𝕜) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := by simp [dddconv_apply]

@[simp]
lemma coe_comp_ddconv : ((↑) : ℝ → 𝕜) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g := funext <| coe_ddconv _ _

@[simp]
lemma coe_comp_dddconv : ((↑) : ℝ → 𝕜) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g := funext <| coe_dddconv _ _

end RCLike

namespace Complex
variable (f g : G → ℝ) (n : ℕ) (a : G)

@[simp, norm_cast]
lemma ofReal_ddconv : (↑((f ∗ᵈ g) a) : ℂ) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a := RCLike.coe_ddconv _ _ _

@[simp, norm_cast]
lemma ofReal_dddconv : (↑((f ○ᵈ g) a) : ℂ) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := RCLike.coe_dddconv _ _ _

@[simp] lemma ofReal_comp_ddconv : ((↑) : ℝ → ℂ) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g :=
  funext <| ofReal_ddconv _ _

@[simp] lemma ofReal_comp_dddconv : ((↑) : ℝ → ℂ) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g :=
  funext <| ofReal_dddconv _ _

end Complex

namespace NNReal
variable (f g : G → ℝ≥0) (a : G)

@[simp, norm_cast]
lemma coe_ddconv : (↑((f ∗ᵈ g) a) : ℝ) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a := map_ddconv NNReal.toRealHom _ _ _

@[simp, norm_cast]
lemma coe_dddconv : (↑((f ○ᵈ g) a) : ℝ) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := by simp [dddconv_apply, coe_sum]

@[simp] lemma coe_comp_ddconv : ((↑) : _ → ℝ) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g :=
  funext <| coe_ddconv _ _

@[simp] lemma coe_comp_dddconv : ((↑) : _ → ℝ) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g :=
  funext <| coe_dddconv _ _

end NNReal

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

/-- Iterated convolution. -/
def iterConv (f : G → R) : ℕ → G → R
  | 0 => trivChar
  | n + 1 => iterConv f n ∗ᵈ f

infixl:78 " ∗ᵈ^ " => iterConv

@[simp] lemma iterConv_zero (f : G → R) : f ∗ᵈ^ 0 = trivChar := rfl
@[simp] lemma iterConv_one (f : G → R) : f ∗ᵈ^ 1 = f := trivChar_ddconv _

lemma iterConv_succ (f : G → R) (n : ℕ) : f ∗ᵈ^ (n + 1) = f ∗ᵈ^ n ∗ᵈ f := rfl
lemma iterConv_succ' (f : G → R) (n : ℕ) : f ∗ᵈ^ (n + 1) = f ∗ᵈ f ∗ᵈ^ n := ddconv_comm _ _

lemma iterConv_add (f : G → R) (m : ℕ) : ∀ n, f ∗ᵈ^ (m + n) = f ∗ᵈ^ m ∗ᵈ f ∗ᵈ^ n
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterConv_succ', iterConv_add, ddconv_left_comm]

lemma iterConv_mul (f : G → R) (m : ℕ) : ∀ n : ℕ, f ∗ᵈ^ (m * n) = f ∗ᵈ^ m ∗ᵈ^ n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterConv_succ, iterConv_add, iterConv_mul]

lemma iterConv_mul' (f : G → R) (m n : ℕ) : f ∗ᵈ^ (m * n) = f ∗ᵈ^ n ∗ᵈ^ m := by
  rw [mul_comm, iterConv_mul]

lemma iterConv_ddconv_distrib (f g : G → R) : ∀ n, (f ∗ᵈ g) ∗ᵈ^ n = f ∗ᵈ^ n ∗ᵈ g ∗ᵈ^ n
  | 0 => (ddconv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_ddconv_distrib, ddconv_ddconv_ddconv_comm]

@[simp] lemma zero_iterConv : ∀ {n}, n ≠ 0 → (0 : G → R) ∗ᵈ^ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => ddconv_zero _

@[simp] lemma smul_iterConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c : H) (f : G → R) : ∀ n, (c • f) ∗ᵈ^ n = c ^ n • f ∗ᵈ^ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterConv_succ, smul_iterConv _ _ n, pow_succ, mul_smul_ddconv_comm]

lemma comp_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (f ∗ᵈ^ n) = m ∘ f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, comp_ddconv, comp_iterConv]

lemma map_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) (a : G) (n : ℕ) :
    m ((f ∗ᵈ^ n) a) = (m ∘ f ∗ᵈ^ n) a := congr_fun (comp_iterConv m _ _) _

lemma sum_iterConv (f : G → R) : ∀ n, ∑ a, (f ∗ᵈ^ n) a = (∑ a, f a) ^ n
  | 0 => by simp
  | n + 1 => by simp [iterConv_succ, sum_ddconv, sum_iterConv, pow_succ]

@[simp] lemma iterConv_trivChar : ∀ n, (trivChar : G → R) ∗ᵈ^ n = trivChar
  | 0 => rfl
  | _n + 1 => (ddconv_trivChar _).trans <| iterConv_trivChar _

lemma support_iterConv_subset (f : G → R) : ∀ n, support (f ∗ᵈ^ n) ⊆ n • support f
  | 0 => by simp
  | n + 1 =>
    (support_ddconv_subset _ _).trans <| Set.add_subset_add_right <| support_iterConv_subset _ _

variable [StarRing R]

lemma iterConv_dddconv_distrib (f g : G → R) : ∀ n, (f ○ᵈ g) ∗ᵈ^ n = f ∗ᵈ^ n ○ᵈ g ∗ᵈ^ n
  | 0 => (dddconv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_dddconv_distrib, ddconv_dddconv_ddconv_comm]

@[simp] lemma conj_iterConv (f : G → R) : ∀ n, conj (f ∗ᵈ^ n) = conj f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conj_iterConv]

@[simp] lemma conj_iterConv_apply (f : G → R) (n : ℕ) (a : G) :
    conj ((f ∗ᵈ^ n) a) = (conj f ∗ᵈ^ n) a := congr_fun (conj_iterConv _ _) _

lemma IsSelfAdjoint.iterConv (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (f ∗ᵈ^ n) :=
  (conj_iterConv _ _).trans <| congr_arg (· ∗ᵈ^ n) hf

@[simp]
lemma conjneg_iterConv (f : G → R) : ∀ n, conjneg (f ∗ᵈ^ n) = conjneg f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conjneg_iterConv]

end CommSemiring

namespace NNReal

@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ≥0) (n : ℕ) (a : G) : (↑((f ∗ᵈ^ n) a) : ℝ) = ((↑) ∘ f ∗ᵈ^ n) a :=
  map_iterConv NNReal.toRealHom _ _ _

end NNReal

namespace Complex

@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ) (n : ℕ) (a : G) : (↑((f ∗ᵈ^ n) a) : ℂ) = ((↑) ∘ f ∗ᵈ^ n) a :=
  map_iterConv ofRealHom _ _ _

end Complex
