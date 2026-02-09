import APAP.Prereqs.Convolution.Discrete.Defs
import APAP.Prereqs.DummyPositivity
import Mathlib.Algebra.Order.Star.Conjneg

open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise

variable {G R : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

lemma conv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ∗ g) a := conv_nonneg hf hg _

variable [StarRing R] [StarOrderedRing R]

lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _

lemma dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a := dconv_nonneg hf hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g : G → R}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care
@[simp] lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g := by
  refine (support_conv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, conv_apply_add]
  exact ne_of_gt <| sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩

lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing R] [StarOrderedRing R]

@[simp]
lemma support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [← conv_conjneg]; exact conv_pos hf (conjneg_pos.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗^ n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => conv_nonneg (iterConv_nonneg hf) hf

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => conv_pos (iterConv_pos hf) hf

end StrictOrderedCommSemiring

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

private lemma conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  conv_nonneg hf.le hg

private lemma conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g :=
  conv_nonneg hf hg.le

variable [StarRing R] [StarOrderedRing R]

private lemma dconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  dconv_nonneg hf.le hg

private lemma dconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g :=
  dconv_nonneg hf hg.le

end

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ∗ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ _] def evalConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  let ra ← core zG pG a; let rb ← core zG pG b
  match ra, rb with
  | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
  | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
  | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
  | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
  | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
  | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
  | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
  | _, _ => pure .none

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ○ _] def evalDConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  let ra ← core zG pG a; let rb ← core zG pG b
  match ra, rb with
  | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
  | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
  | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
  | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
  | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
  | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
  | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
  | _, _ => pure .none

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗^ _] def evalIterConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  match ← core zG pG a with
  | .positive pa => return .positive q(dummy_pos_of_pos $pa)
  | .nonnegative pa => return .nonnegative q(dummy_nng_of_nng $pa)
  | .nonzero pa => return .nonzero q(dummy_nzr_of_nzr $pa)
  | _ => return .none

variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R}

example (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g := by positivity
example (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g := by positivity
example (hf : 0 < f) (n : ℕ) : 0 < f ∗^ n := by positivity
example (hf : 0 ≤ f) (n : ℕ) : 0 ≤ f ∗^ n := by positivity

end Mathlib.Meta.Positivity
