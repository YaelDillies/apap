import APAP.Prereqs.Convolution.Discrete.Defs
import APAP.Prereqs.Function.Indicator.Defs
import Mathlib.Algebra.BigOperators.Balance

/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `cconv`: Discrete convolution of two functions in the compact normalisation
* `cdconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterCconv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ₙ g`: Convolution
* `f ○ₙ g`: Difference convolution
* `f ∗^ₙ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G H R S : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ₙ g` and difference convolution `f ○ₙ g` of functions
`f g : G → R`, and show how they interact.
-/

/-! ### Trivial character -/

section Semifield
variable [Semifield R]

/-- The trivial character. -/
def trivNChar : G → R := fun a ↦ if a = 0 then card G else 0

@[simp] lemma trivNChar_apply (a : G) : (trivNChar a : R) = if a = 0 then (card G : R) else 0 := rfl

variable [StarRing R]

@[simp] lemma conj_trivNChar : conj (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp

@[simp] lemma conjneg_trivNChar : conjneg (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp

@[simp] lemma isSelfAdjoint_trivNChar : IsSelfAdjoint (trivNChar : G → R) := conj_trivNChar

end Semifield

/-! ### Convolution -/

section Semifield
variable [Semifield R] [CharZero R] {f g : G → R}

/-- Convolution -/
def cconv (f g : G → R) : G → R := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a , f x.1 * g x.2

infixl:71 " ∗ₙ " => cconv

lemma cconv_apply (f g : G → R) (a : G) :
    (f ∗ₙ g) a = 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl

lemma cconv_apply_eq_smul_conv (f g : G → R) (a : G) :
    (f ∗ₙ g) a = (f ∗ g) a /ℚ Fintype.card G := by
  rw [cconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (b, a - b)) Prod.fst ?_ ?_ ?_ ?_ <;>
    simp [Set.LeftInvOn, Set.MapsTo, eq_sub_iff_add_eq', eq_comm]

lemma cconv_eq_smul_conv (f g : G → R) : f ∗ₙ g = (f ∗ g) /ℚ Fintype.card G :=
  funext <| cconv_apply_eq_smul_conv _ _

@[simp] lemma cconv_zero (f : G → R) : f ∗ₙ 0 = 0 := by ext; simp [cconv_apply]
@[simp] lemma zero_cconv (f : G → R) : 0 ∗ₙ f = 0 := by ext; simp [cconv_apply]

lemma cconv_add (f g h : G → R) : f ∗ₙ (g + h) = f ∗ₙ g + f ∗ₙ h := by
  ext; simp [cconv_apply, mul_add, expect_add_distrib]

lemma add_cconv (f g h : G → R) : (f + g) ∗ₙ h = f ∗ₙ h + g ∗ₙ h := by
  ext; simp [cconv_apply, add_mul, expect_add_distrib]

lemma smul_cconv [DistribSMul H R] [IsScalarTower H R R] [SMulCommClass H R R] (c : H)
    (f g : G → R) : c • f ∗ₙ g = c • (f ∗ₙ g) := by
  have := SMulCommClass.symm H R R
  ext a
  simp only [Pi.smul_apply, smul_expect, cconv_apply, smul_mul_assoc]

lemma cconv_smul [DistribSMul H R] [SMulCommClass H R R] (c : H)
    (f g : G → R) : f ∗ₙ c • g = c • (f ∗ₙ g) := by
  have := SMulCommClass.symm H R R
  ext a
  simp only [Pi.smul_apply, smul_expect, cconv_apply, mul_smul_comm]

alias smul_cconv_assoc := smul_cconv
alias smul_cconv_left_comm := cconv_smul

@[simp] lemma translate_cconv (a : G) (f g : G → R) : τ a f ∗ₙ g = τ a (f ∗ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma cconv_translate (a : G) (f g : G → R) : f ∗ₙ τ a g = τ a (f ∗ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

lemma cconv_comm (f g : G → R) : f ∗ₙ g = g ∗ₙ f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])

lemma mul_smul_cconv_comm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c d : H) (f g : G → R) : (c * d) • (f ∗ₙ g) = c • f ∗ₙ d • g := by
  rw [smul_cconv, cconv_smul, mul_smul]

lemma cconv_assoc (f g h : G → R) : f ∗ₙ g ∗ₙ h = f ∗ₙ (g ∗ₙ h) := by
  simp only [cconv_eq_smul_conv, smul_conv, conv_smul, conv_assoc]

lemma cconv_right_comm (f g h : G → R) : f ∗ₙ g ∗ₙ h = f ∗ₙ h ∗ₙ g := by
  rw [cconv_assoc, cconv_assoc, cconv_comm g]

lemma cconv_left_comm (f g h : G → R) : f ∗ₙ (g ∗ₙ h) = g ∗ₙ (f ∗ₙ h) := by
  rw [← cconv_assoc, ← cconv_assoc, cconv_comm g]

lemma cconv_cconv_cconv_comm (f g h i : G → R) : f ∗ₙ g ∗ₙ (h ∗ₙ i) = f ∗ₙ h ∗ₙ (g ∗ₙ i) := by
  rw [cconv_assoc, cconv_assoc, cconv_left_comm g]

lemma map_cconv [Semifield S] [CharZero S] (m : R →+* S) (f g : G → R) (a : G) : m
    ((f ∗ₙ g) a) = (m ∘ f ∗ₙ m ∘ g) a := by
  simp_rw [cconv_apply, map_expect, map_mul, Function.comp_apply]

lemma comp_cconv [Semifield S] [CharZero S] (m : R →+* S) (f g : G → R) :
    m ∘ (f ∗ₙ g) = m ∘ f ∗ₙ m ∘ g := funext <| map_cconv _ _ _

lemma cconv_eq_expect_sub (f g : G → R) (a : G) : (f ∗ₙ g) a = 𝔼 t, f (a - t) * g t := by
  rw [cconv_apply]
  refine expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
    ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop

lemma cconv_eq_expect_add (f g : G → R) (a : G) : (f ∗ₙ g) a = 𝔼 t, f (a + t) * g (-t) :=
  (cconv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma cconv_eq_expect_sub' (f g : G → R) (a : G) : (f ∗ₙ g) a = 𝔼 t, f t * g (a - t) := by
  rw [cconv_comm, cconv_eq_expect_sub]; simp_rw [mul_comm]

lemma cconv_eq_expect_add' (f g : G → R) (a : G) : (f ∗ₙ g) a = 𝔼 t, f (-t) * g (a + t) := by
  rw [cconv_comm, cconv_eq_expect_add]; simp_rw [mul_comm]

lemma cconv_apply_add (f g : G → R) (a b : G) : (f ∗ₙ g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (cconv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc]

lemma expect_cconv_mul (f g h : G → R) :
    𝔼 a, (f ∗ₙ g) a * h a = 𝔼 a, 𝔼 b, f a * g b * h (a + b) := by
  simp_rw [cconv_eq_expect_sub', expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma expect_cconv (f g : G → R) : 𝔼 a, (f ∗ₙ g) a = (𝔼 a, f a) * 𝔼 a, g a := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_cconv_mul f g 1

@[simp] lemma cconv_const (f : G → R) (b : R) : f ∗ₙ const _ b = const _ ((𝔼 x, f x) * b) := by
  ext; simp [cconv_eq_expect_sub', expect_mul]

@[simp] lemma const_cconv (b : R) (f : G → R) : const _ b ∗ₙ f = const _ (b * 𝔼 x, f x) := by
  ext; simp [cconv_eq_expect_sub, mul_expect]

@[simp] lemma cconv_trivNChar (f : G → R) : f ∗ₙ trivNChar = f := by
  ext a; simp [cconv_eq_expect_sub, card_univ, NNRat.smul_def, mul_comm]

@[simp] lemma trivNChar_cconv (f : G → R) : trivNChar ∗ₙ f = f := by
  rw [cconv_comm, cconv_trivNChar]

lemma support_cconv_subset (f g : G → R) : support (f ∗ₙ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_expect_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

variable [StarRing R]

/-- Difference convolution -/
def cdconv (f g : G → R) : G → R := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

infixl:71 " ○ₙ " => cdconv

lemma cdconv_apply (f g : G → R) (a : G) :
    (f ○ₙ g) a = 𝔼 x : G × G with x.1 - x.2 = a , f x.1 * conj g x.2 := rfl

lemma cdconv_apply_eq_smul_dconv (f g : G → R) (a : G) :
    (f ○ₙ g) a = (f ○ g) a /ℚ Fintype.card G := by
  rw [cdconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (a + b, b)) Prod.snd ?_ ?_ ?_ ?_ <;>
    simp [Set.MapsTo, Set.LeftInvOn, eq_sub_iff_add_eq, eq_comm]

lemma cdconv_eq_smul_dconv (f g : G → R) : (f ○ₙ g) = (f ○ g) /ℚ Fintype.card G :=
  funext <| cdconv_apply_eq_smul_dconv _ _

@[simp] lemma cconv_conjneg (f g : G → R) : f ∗ₙ conjneg g = f ○ₙ g :=
  funext fun a ↦ expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
    (fun x y _ _ h ↦ by simpa [Prod.ext_iff] using h) fun x hx ↦
      ⟨(x.1, -x.2), by simpa [sub_eq_add_neg] using hx, by simp⟩

@[simp] lemma cdconv_conjneg (f g : G → R) : f ○ₙ conjneg g = f ∗ₙ g := by
  rw [← cconv_conjneg, conjneg_conjneg]

@[simp] lemma translate_cdconv (a : G) (f g : G → R) : τ a f ○ₙ g = τ a (f ○ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma cdconv_translate (a : G) (f g : G → R) : f ○ₙ τ a g = τ (-a) (f ○ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

@[simp] lemma conj_cconv (f g : G → R) : conj (f ∗ₙ g) = conj f ∗ₙ conj g :=
  funext fun a ↦ by simp only [Pi.conj_apply, cconv_apply, map_expect, map_mul]

@[simp] lemma conj_cdconv (f g : G → R) : conj (f ○ₙ g) = conj f ○ₙ conj g := by
  simp_rw [← cconv_conjneg, conj_cconv, conjneg_conj]

lemma IsSelfAdjoint.cconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ₙ g) :=
  (conj_cconv _ _).trans <| congr_arg₂ _ hf hg

lemma IsSelfAdjoint.cdconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ○ₙ g) :=
  (conj_cdconv _ _).trans <| congr_arg₂ _ hf hg

@[simp] lemma conjneg_cconv (f g : G → R) : conjneg (f ∗ₙ g) = conjneg f ∗ₙ conjneg g := by
  funext a
  simp only [cconv_apply, conjneg_apply, map_expect, map_mul]
  exact Finset.expect_equiv (Equiv.neg (G × G)) (by simp [eq_comm, ← neg_eq_iff_eq_neg, add_comm])
    (by simp)

@[simp] lemma conjneg_cdconv (f g : G → R) : conjneg (f ○ₙ g) = g ○ₙ f := by
  simp_rw [← cconv_conjneg, conjneg_cconv, conjneg_conjneg, cconv_comm]

@[simp] lemma cdconv_zero (f : G → R) : f ○ₙ 0 = 0 := by simp [← cconv_conjneg]
@[simp] lemma zero_cdconv (f : G → R) : 0 ○ₙ f = 0 := by rw [← cconv_conjneg]; simp [-cconv_conjneg]

lemma cdconv_add (f g h : G → R) : f ○ₙ (g + h) = f ○ₙ g + f ○ₙ h := by
  simp_rw [← cconv_conjneg, conjneg_add, cconv_add]

lemma add_cdconv (f g h : G → R) : (f + g) ○ₙ h = f ○ₙ h + g ○ₙ h := by
  simp_rw [← cconv_conjneg, add_cconv]

lemma smul_cdconv [DistribSMul H R] [IsScalarTower H R R] [SMulCommClass H R R] (c : H)
    (f g : G → R) : c • f ○ₙ g = c • (f ○ₙ g) := by
  have := SMulCommClass.symm H R R
  ext a
  simp only [Pi.smul_apply, smul_expect, cdconv_apply, smul_mul_assoc]

lemma cdconv_smul [Star H] [DistribSMul H R] [SMulCommClass H R R]
    [StarModule H R] (c : H) (f g : G → R) : f ○ₙ c • g = star c • (f ○ₙ g) := by
  have := SMulCommClass.symm H R R
  ext a
  simp only [Pi.smul_apply, smul_expect, cdconv_apply, mul_smul_comm, starRingEnd_apply, star_smul]

alias smul_cdconv_assoc := smul_cdconv
alias smul_cdconv_left_comm := cdconv_smul

lemma cconv_cdconv_cconv_comm (f g h i : G → R) : f ∗ₙ g ○ₙ (h ∗ₙ i) = f ○ₙ h ∗ₙ (g ○ₙ i) := by
  simp_rw [← cconv_conjneg, conjneg_cconv, cconv_cconv_cconv_comm]

lemma cdconv_cconv_cdconv_comm (f g h i : G → R) : f ○ₙ g ∗ₙ (h ○ₙ i) = f ∗ₙ h ○ₙ (g ∗ₙ i) := by
  simp_rw [← cconv_conjneg, conjneg_cconv, cconv_cconv_cconv_comm]

lemma cdconv_cdconv_cdconv_comm (f g h i : G → R) : f ○ₙ g ○ₙ (h ○ₙ i) = f ○ₙ h ○ₙ (g ○ₙ i) := by
  simp_rw [← cconv_conjneg, conjneg_cconv, cconv_cconv_cconv_comm]

--TODO: Can we generalise to star ring homs?
-- lemma map_cdconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ₙ g) a) : ℝ) = ((↑) ∘ f ○ₙ (↑) ∘ g) a := by
--   simp_rw [cdconv_apply, NNReal.coe_expect, NNReal.coe_mul, starRingEnd_apply, star_trivial,
--     Function.comp_apply]

lemma cdconv_eq_expect_add (f g : G → R) (a : G) : (f ○ₙ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  simp [← cconv_conjneg, cconv_eq_expect_add]

lemma cdconv_eq_expect_sub (f g : G → R) (a : G) : (f ○ₙ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  simp [← cconv_conjneg, cconv_eq_expect_sub']

lemma cdconv_apply_neg (f g : G → R) (a : G) : (f ○ₙ g) (-a) = conj ((g ○ₙ f) a) := by
  rw [← conjneg_cdconv f, conjneg_apply, Complex.conj_conj]

lemma cdconv_apply_sub (f g : G → R) (a b : G) :
    (f ○ₙ g) (a - b) = 𝔼 t, f (a + t) * conj (g (b + t)) := by
  simp [← cconv_conjneg, sub_eq_add_neg, cconv_apply_add, add_comm]

lemma expect_cdconv_mul (f g h : G → R) :
    𝔼 a, (f ○ₙ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [cdconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma expect_cdconv (f g : G → R) : 𝔼 a, (f ○ₙ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_cdconv_mul f g 1

@[simp]
lemma cdconv_const (f : G → R) (b : R) : f ○ₙ const _ b = const _ ((𝔼 x, f x) * conj b) := by
  ext; simp [cdconv_eq_expect_sub, expect_mul]

@[simp]
lemma const_cdconv (b : R) (f : G → R) : const _ b ○ₙ f = const _ (b * 𝔼 x, conj (f x)) := by
  ext; simp [cdconv_eq_expect_add, mul_expect]

@[simp] lemma cdconv_trivNChar (f : G → R) : f ○ₙ trivNChar = f := by
  rw [← cconv_conjneg, conjneg_trivNChar, cconv_trivNChar]

@[simp] lemma trivNChar_cdconv (f : G → R) : trivNChar ○ₙ f = conjneg f := by
  rw [← cconv_conjneg, trivNChar_cconv]

lemma support_cdconv_subset (f g : G → R) : support (f ○ₙ g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_cconv_subset f (conjneg g)

-- lemma indicate_cconv_indicate_apply (s t : Finset G) (a : G) :
--     (𝟭_[R] s ∗ₙ 𝟭 t) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 + x.2 = a).card := by
--   simp only [cconv_apply, indicate_apply, ← ite_and, filter_comm, boole_mul, expect_boole]
--   simp_rw [← mem_product, filter_univ_mem]

-- lemma indicate_cdconv_indicate_apply (s t : Finset G) (a : G) :
--     (𝟭_[R] s ○ₙ 𝟭 t) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 - x.2 = a).card := by
--   simp only [cdconv_apply, indicate_apply, ← ite_and, filter_comm, boole_mul, expect_boole,
--     apply_ite conj, map_one, map_zero, Pi.conj_apply]
--   simp_rw [← mem_product, filter_univ_mem]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma cconv_neg (f g : G → R) : f ∗ₙ -g = -(f ∗ₙ g) := by ext; simp [cconv_apply]
@[simp] lemma neg_cconv (f g : G → R) : -f ∗ₙ g = -(f ∗ₙ g) := by ext; simp [cconv_apply]

lemma cconv_sub (f g h : G → R) : f ∗ₙ (g - h) = f ∗ₙ g - f ∗ₙ h := by
  simp only [sub_eq_add_neg, cconv_add, cconv_neg]

lemma sub_cconv (f g h : G → R) : (f - g) ∗ₙ h = f ∗ₙ h - g ∗ₙ h := by
  simp only [sub_eq_add_neg, add_cconv, neg_cconv]

variable [StarRing R]

@[simp] lemma cdconv_neg (f g : G → R) : f ○ₙ -g = -(f ○ₙ g) := by ext; simp [cdconv_apply]
@[simp] lemma neg_cdconv (f g : G → R) : -f ○ₙ g = -(f ○ₙ g) := by ext; simp [cdconv_apply]

lemma cdconv_sub (f g h : G → R) : f ○ₙ (g - h) = f ○ₙ g - f ○ₙ h := by
  simp only [sub_eq_add_neg, cdconv_add, cdconv_neg]

lemma sub_cdconv (f g h : G → R) : (f - g) ○ₙ h = f ○ₙ h - g ○ₙ h := by
  simp only [sub_eq_add_neg, add_cdconv, neg_cdconv]

end Field

section Semifield
variable [Semifield R] [CharZero R]

@[simp] lemma indicate_univ_cconv_indicate_univ : 𝟭_[R] (univ : Finset G) ∗ₙ 𝟭 univ = 𝟭 univ := by
  ext; simp [indicate_apply, cconv_eq_expect_add, *]

variable [StarRing R]

@[simp] lemma indicate_univ_cdconv_mu_univ : 𝟭_[R] (univ : Finset G) ○ₙ 𝟭 univ = 𝟭 univ := by
  ext; simp [indicate_apply, cdconv_eq_expect_add, *]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_cconv (f g : G → R) : balance (f ∗ₙ g) = balance f ∗ₙ balance g := by
  simp [balance, cconv_sub, sub_cconv, expect_cconv, expect_sub_distrib]

variable [StarRing R]

@[simp] lemma balance_cdconv (f g : G → R) : balance (f ○ₙ g) = balance f ○ₙ balance g := by
  simp [balance, cdconv_sub, sub_cdconv, expect_cdconv, map_expect, expect_sub_distrib]

end Field

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

@[simp, norm_cast] lemma coe_cconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : G → 𝕜) a :=
  map_cconv (algebraMap ℝ 𝕜) ..

@[simp, norm_cast] lemma coe_cdconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : G → 𝕜) a := by
  simp [cdconv_apply]

@[simp]
lemma coe_comp_cconv : ofReal ∘ (f ∗ₙ g) = ((↑) ∘ f ∗ₙ (↑) ∘ g : G → 𝕜) := funext <| coe_cconv _ _

@[simp]
lemma coe_comp_cdconv : ofReal ∘ (f ○ₙ g) = ((↑) ∘ f ○ₙ (↑) ∘ g : G → 𝕜) := funext <| coe_cdconv _ _

end RCLike

namespace Complex
variable (f g : G → ℝ) (a : G)

@[simp, norm_cast]
lemma coe_cconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : G → ℂ) a := RCLike.coe_cconv _ _ _

@[simp, norm_cast]
lemma coe_cdconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : G → ℂ) a := RCLike.coe_cdconv _ _ _

@[simp] lemma ofReal_comp_cconv : ofReal ∘ (f ∗ₙ g) = ((↑) ∘ f ∗ₙ (↑) ∘ g : G → ℂ) :=
  funext <| coe_cconv _ _

@[simp] lemma ofReal_comp_cdconv : ofReal ∘ (f ○ₙ g) = ((↑) ∘ f ○ₙ (↑) ∘ g : G → ℂ) :=
  funext <| coe_cdconv _ _

end Complex

namespace NNReal
variable (f g : G → ℝ≥0) (a : G)

@[simp, norm_cast]
lemma coe_cconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : G → ℝ) a := map_cconv NNReal.toRealHom _ _ _

@[simp, norm_cast]
lemma coe_cdconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : G → ℝ) a := by simp [cdconv_apply, coe_expect]

@[simp]
lemma coe_comp_cconv : ((↑) : _ → ℝ) ∘ (f ∗ₙ g) = (↑) ∘ f ∗ₙ (↑) ∘ g := funext <| coe_cconv _ _

@[simp]
lemma coe_comp_cdconv : ((↑) : _ → ℝ) ∘ (f ○ₙ g) = (↑) ∘ f ○ₙ (↑) ∘ g := funext <| coe_cdconv _ _

end NNReal

/-! ### Iterated convolution -/

section Semifield
variable [Semifield R] [CharZero R] {f g : G → R} {n : ℕ}

/-- Iterated convolution. -/
def iterCconv (f : G → R) : ℕ → G → R
  | 0 => trivNChar
  | n + 1 => iterCconv f n ∗ₙ f

infixl:78 " ∗^ₙ " => iterCconv

@[simp] lemma iterCconv_zero (f : G → R) : f ∗^ₙ 0 = trivNChar := rfl
@[simp] lemma iterCconv_one (f : G → R) : f ∗^ₙ 1 = f := trivNChar_cconv _

lemma iterCconv_succ (f : G → R) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗^ₙ n ∗ₙ f := rfl
lemma iterCconv_succ' (f : G → R) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗ₙ f ∗^ₙ n := cconv_comm _ _

lemma iterCconv_add (f : G → R) (m : ℕ) : ∀ n, f ∗^ₙ (m + n) = f ∗^ₙ m ∗ₙ f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterCconv_succ', iterCconv_add, cconv_left_comm]

lemma iterCconv_mul (f : G → R) (m : ℕ) : ∀ n, f ∗^ₙ (m * n) = f ∗^ₙ m ∗^ₙ n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterCconv_succ, iterCconv_add, iterCconv_mul]

lemma iterCconv_mul' (f : G → R) (m n : ℕ) : f ∗^ₙ (m * n) = f ∗^ₙ n ∗^ₙ m := by
  rw [mul_comm, iterCconv_mul]

lemma iterCconv_cconv_distrib (f g : G → R) : ∀ n, (f ∗ₙ g) ∗^ₙ n = f ∗^ₙ n ∗ₙ g ∗^ₙ n
  | 0 => (cconv_trivNChar _).symm
  | n + 1 => by simp_rw [iterCconv_succ, iterCconv_cconv_distrib, cconv_cconv_cconv_comm]

@[simp] lemma zero_iterCconv : ∀ {n}, n ≠ 0 → (0 : G → R) ∗^ₙ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => cconv_zero _

@[simp] lemma smul_iterCconv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c : H) (f : G → R) : ∀ n, (c • f) ∗^ₙ n = c ^ n • f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterCconv_succ, smul_iterCconv _ _ n, pow_succ, mul_smul_cconv_comm]

lemma comp_iterCconv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (f ∗^ₙ n) = m ∘ f ∗^ₙ n
  | 0 => by ext; simp; split_ifs <;> simp
  | n + 1 => by simp [iterCconv_succ, comp_cconv, comp_iterCconv]

lemma expect_iterCconv (f : G → R) : ∀ n, 𝔼 a, (f ∗^ₙ n) a = (𝔼 a, f a) ^ n
  | 0 => by simp [card_univ, NNRat.smul_def]
  | n + 1 => by simp only [iterCconv_succ, expect_cconv, expect_iterCconv, pow_succ]

@[simp] lemma iterCconv_trivNChar : ∀ n, (trivNChar : G → R) ∗^ₙ n = trivNChar
  | 0 => rfl
  | _n + 1 => (cconv_trivNChar _).trans <| iterCconv_trivNChar _

lemma support_iterCconv_subset (f : G → R) : ∀ n, support (f ∗^ₙ n) ⊆ n • support f
  | 0 => by
    simp only [iterCconv_zero, zero_smul, support_subset_iff, Ne, ite_eq_right_iff, exists_prop,
      not_forall, Set.mem_zero, and_imp, forall_eq, imp_true_iff, trivNChar_apply]
  | n + 1 =>
    (support_cconv_subset _ _).trans <| Set.add_subset_add_right <| support_iterCconv_subset _ _

lemma map_iterCconv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) (a : G)
    (n : ℕ) : m ((f ∗^ₙ n) a) = (m ∘ f ∗^ₙ n) a := congr_fun (comp_iterCconv m _ _) _

variable [StarRing R]

@[simp] lemma conj_iterCconv (f : G → R) : ∀ n, conj (f ∗^ₙ n) = conj f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterCconv_succ, conj_iterCconv]

@[simp] lemma conjneg_iterCconv (f : G → R) : ∀ n, conjneg (f ∗^ₙ n) = conjneg f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterCconv_succ, conjneg_iterCconv]

lemma iterCconv_cdconv_distrib (f g : G → R) : ∀ n, (f ○ₙ g) ∗^ₙ n = f ∗^ₙ n ○ₙ g ∗^ₙ n
  | 0 => (cdconv_trivNChar _).symm
  | n + 1 => by simp_rw [iterCconv_succ, iterCconv_cdconv_distrib, cconv_cdconv_cconv_comm]

-- lemma indicate_iterCconv_apply (s : Finset G) (n : ℕ) (a : G) :
--     (𝟭_[ℝ] s ∗^ₙ n) a = #{x ∈ piFinset fun _i ↦ s | ∑ i, x i = a} := by
--   induction' n with n ih generalizing a
--   · simp [apply_ite card, eq_comm]
--   simp_rw [iterCconv_succ, cconv_eq_expect_sub', ih, indicate_apply, boole_mul, expect_ite,
--     filter_univ_mem, expect_const_zero, add_zero, ← Nat.cast_expect, ← Finset.card_sigma,
--     Nat.cast_inj]
--   refine Finset.card_bij (fun f _ ↦ Fin.cons f.1 f.2) _ _ _
--   · simp only [Fin.expect_cons, eq_sub_iff_add_eq', mem_sigma, mem_filter, mem_piFinset, and_imp]
--     refine fun bf hb hf ha ↦ ⟨Fin.cases _ _, ha⟩
--     · exact hb
--     · simpa only [Fin.cons_succ]
--   · simp only [Sigma.ext_iff, Fin.cons_eq_cons, heq_iff_eq, imp_self, imp_true_iff, forall_const,
--       Sigma.forall]
--   · simp only [mem_filter, mem_piFinset, mem_sigma, exists_prop, Sigma.exists, and_imp,
--       eq_sub_iff_add_eq', and_assoc]
--     exact fun f hf ha ↦
--       ⟨f 0, Fin.tail f, hf _, fun _ ↦ hf _, (Fin.expect_univ_succ _).symm.trans ha,
--         Fin.cons_self_tail _⟩

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_iterCconv (f : G → R) : ∀ {n}, n ≠ 0 → balance (f ∗^ₙ n) = balance f ∗^ₙ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterCconv_succ _ (n + 1), balance_iterCconv _ n.succ_ne_zero]

end Field

namespace NNReal
variable {f : G → ℝ≥0}

@[simp, norm_cast]
lemma coe_iterCconv (f : G → ℝ≥0) (n : ℕ) (a : G) : (↑((f ∗^ₙ n) a) : ℝ) = ((↑) ∘ f ∗^ₙ n) a :=
  map_iterCconv NNReal.toRealHom _ _ _

end NNReal
