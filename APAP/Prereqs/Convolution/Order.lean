module

public import APAP.Prereqs.Convolution.Discrete.Defs

import APAP.Prereqs.DummyPositivity
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Analysis.Complex.Order

@[expose] public section

open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise

variable {G R : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

lemma ddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ᵈ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

lemma ddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ∗ᵈ g) a :=
  ddconv_nonneg hf hg _

variable [StarRing R] [StarOrderedRing R]

lemma dddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ᵈ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _

lemma dddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ᵈ g) a :=
  dddconv_nonneg hf hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g : G → R}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care
@[simp] lemma support_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) :
    support (f ∗ᵈ g) = support f + support g := by
  refine (support_ddconv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, ddconv_apply_add]
  exact ne_of_gt <| sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩

lemma ddconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ᵈ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨ddconv_nonneg hf hg, a + b, ?_⟩
  rw [ddconv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing R] [StarOrderedRing R]

@[simp]
lemma support_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ᵈ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_ddconv hf (conjneg_nonneg.2 hg)

lemma dddconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ᵈ g := by
  rw [← ddconv_conjneg]; exact ddconv_pos hf (conjneg_pos.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗ᵈ^ n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => ddconv_nonneg (iterConv_nonneg hf) hf

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗ᵈ^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => ddconv_pos (iterConv_pos hf) hf

end StrictOrderedCommSemiring

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

private lemma ddconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ᵈ g :=
  ddconv_nonneg hf.le hg

private lemma ddconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ᵈ g :=
  ddconv_nonneg hf hg.le

variable [StarRing R] [StarOrderedRing R]

private lemma dddconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ᵈ g :=
  dddconv_nonneg hf.le hg

private lemma dddconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ᵈ g :=
  dddconv_nonneg hf hg.le

end

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ∗ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ᵈ _] meta def evalConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    let rb ← core zG (some pα) b
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
/-- The `positivity` extension which identifies expressions of the form `f ○ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ○ᵈ _] meta def evalDConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    let rb ← core zG (some pα) b
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
/-- The `positivity` extension which identifies expressions of the form `f ○ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ᵈ^ _] meta def evalIterConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    match ra with
    | .positive pa => return .positive q(dummy_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(dummy_nng_of_nng $pa)
    | .nonzero pa => return .nonzero q(dummy_nzr_of_nzr $pa)
    | _ => return .none

variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R}

example (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ᵈ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ᵈ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ᵈ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ᵈ g := by positivity
example (hf : 0 < f) (hg : 0 < g) : 0 < f ○ᵈ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ᵈ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ᵈ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ᵈ g := by positivity
example (hf : 0 < f) (n : ℕ) : 0 < f ∗ᵈ^ n := by positivity
example (hf : 0 ≤ f) (n : ℕ) : 0 ≤ f ∗ᵈ^ n := by positivity

end Mathlib.Meta.Positivity
