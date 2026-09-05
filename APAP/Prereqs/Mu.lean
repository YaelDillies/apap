module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic

import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import AddCombi.Mathlib.Algebra.Star.Pi
import APAP.Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Normalised indicator
-/

open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate Indicator

public section

variable {K L α G : Type*}

section DivisionSemiring
variable [DivisionSemiring K] [DivisionSemiring L] {s : Finset α}

/-- The normalised indicator_one of a set. -/
@[expose] noncomputable def mu (s : Finset α) : α → K := (#s : K)⁻¹ • 𝟭_[s]

scoped[mu] notation "μ " => mu
scoped[mu] notation "μ_[" K "] " => @mu K _ _

open scoped mu

lemma mu_apply [DecidableEq α] (x : α) : μ s x = (#s : K)⁻¹ * ite (x ∈ s) 1 0 := by
  simp [mu, Set.indicator_apply]

@[simp] lemma mu_empty : (μ ∅ : α → K) = 0 := by ext; simp [mu]

lemma map_mu (f : K →+* L) (s : Finset α) (x : α) : f (μ s x) = μ s x := by
  simp_rw [mu, Pi.smul_apply, smul_eq_mul, map_mul, Set.map_indicator_one, map_inv₀, map_natCast]

lemma mu_univ_eq_const [Fintype α] : μ_[K] (univ : Finset α) = const _ (card α : K)⁻¹ := by
  ext; simp [mu]

section Nontrivial
variable [CharZero K] {a : α}

@[simp] lemma mu_apply_eq_zero : μ_[K] s a = 0 ↔ a ∉ s := by
  classical
  simp only [mu_apply, mul_boole, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
  refine imp_congr_right fun ha ↦ ?_
  simp only [ne_empty_of_mem ha]

lemma mu_apply_ne_zero : μ_[K] s a ≠ 0 ↔ a ∈ s := mu_apply_eq_zero.not_left

@[simp] lemma mu_eq_zero : μ_[K] s = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]

lemma mu_ne_zero : μ_[K] s ≠ 0 ↔ s.Nonempty := mu_eq_zero.not.trans nonempty_iff_ne_empty.symm

variable (K)

@[simp] lemma support_mu (s : Finset α) : support (μ_[K] s) = s := by ext; simp

end Nontrivial

variable (K)

lemma card_smul_mu [CharZero K] (s : Finset α) : #s • μ_[K] s = 𝟭_[s] := by
  classical
  ext x : 1
  simp only [Pi.smul_apply, mu_apply, mul_ite, mul_one, mul_zero, smul_ite, nsmul_eq_mul,
    Set.indicator_apply, SetLike.mem_coe]
  split_ifs with h
  · have : s.Nonempty := ⟨_, h⟩
    simp [this.ne_empty]
  · simp

lemma card_smul_mu_apply [CharZero K] (s : Finset α) (x : α) : #s • μ_[K] s x = 𝟭_[s] x :=
  congr_fun (card_smul_mu K _) _

@[simp] lemma sum_mu [CharZero K] [Fintype α] (hs : s.Nonempty) : ∑ x, μ_[K] s x = 1 := by
  classical
  simpa [mu_apply] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hs.card_pos.ne')

section Group
variable [Group G] [MulAction G α] [DecidableEq α]

@[to_additive (dont_translate := K) (attr := simp)]
lemma mu_smul (g : G) (s : Finset α) (a : α) : μ_[K] (g • s) a = μ s (g⁻¹ • a) := by
  simp [mu_apply, inv_smul_mem_iff]

end Group

section Group
variable [Group α] [DecidableEq α]

@[to_additive (dont_translate := K) (attr := simp)]
lemma mu_inv (s : Finset α) (a : α) : μ_[K] s⁻¹ a = μ s a⁻¹ := by simp [mu]

end Group

lemma translate_mu [AddCommGroup G] [DecidableEq G] (a : G) (s : Finset G) :
    τ a (μ_[K] s) = μ (a +ᵥ s) := by
  ext; simp [mu_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

end DivisionSemiring

open scoped mu

section Semifield
variable (K) [Semifield K] {s : Finset G}

lemma expect_mu [CharZero K] [Fintype G] (hs : s.Nonempty) : 𝔼 x, μ_[K] s x = (card G : K)⁻¹ := by
  rw [expect, card_univ, sum_mu _ hs, NNRat.smul_one_eq_cast, NNRat.cast_inv, NNRat.cast_natCast]

variable [StarRing K]

@[simp] lemma conjneg_mu [AddCommGroup G] [DecidableEq G] (s : Finset G) :
    conjneg (μ_[K] s) = μ (-s) := by ext; simp [mu_apply]; split_ifs <;> simp

end Semifield

open scoped mu

section Semifield
variable (K) [Semifield K] [StarRing K] {s : Finset α}

@[simp] lemma conj_mu_apply (s : Finset α) (a : α) : conj (μ_[K] s a) = μ s a := by simp [mu]

@[simp] lemma conj_mu (s : Finset α) : conj (μ_[K] s) = μ s := by ext; simp

end Semifield

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset α}

@[simp] lemma mu_nonneg : 0 ≤ μ_[K] s := fun a ↦ by classical rw [mu_apply]; split_ifs <;> simp
@[simp] lemma mu_pos : 0 < μ_[K] s ↔ s.Nonempty := mu_nonneg.lt_iff_ne'.trans mu_ne_zero

protected alias ⟨_, Finset.Nonempty.mu_pos⟩ := mu_pos

end LinearOrderedSemifield

namespace Complex
variable (s : Finset α) (a : α)

@[simp, norm_cast] lemma ofReal_mu : ↑(μ_[ℝ] s a) = μ_[ℂ] s a := map_mu (algebraMap ℝ ℂ) ..
@[simp] lemma ofReal_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[ℂ] s := funext <| ofReal_mu _

end Complex

namespace RCLike
variable {𝕜 : Type*} [RCLike 𝕜] (s : Finset α) (a : α)

@[simp, norm_cast] lemma coe_mu : ↑(μ_[ℝ] s a) = μ_[𝕜] s a := map_mu (algebraMap ℝ 𝕜) _ _
@[simp] lemma coe_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[𝕜] s := funext <| coe_mu _

end RCLike

namespace NNReal
open scoped NNReal

@[simp, norm_cast]
lemma coe_mu (s : Finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x := map_mu NNReal.toRealHom _ _

@[simp] lemma coe_comp_mu (s : Finset α) : (↑) ∘ μ_[ℝ≥0] s = μ_[ℝ] s := funext <| coe_mu _

end NNReal

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

-- private abbrev TypeFunction (α K : Type*) := α → K

-- private alias ⟨_, mu_pos_of_nonempty⟩ := mu_pos
-- #check indicator_one
-- /-- Extension for the `positivity` tactic: an indicator is nonnegative, and positive if its
-- support is nonempty. -/
-- @[positivity indicator_one _]
-- def evalindicator_one : PositivityExt where eval {u π} zπ pπ e := do
--   let u1 ← mkFreshLevelMVar
--   let u2 ← mkFreshLevelMVar
--   let _ : u =QL max u1 u2 := ⟨⟩
--   match π, e with
--   | ~q(TypeFunction.{u2, u1} $α $K), ~q(@indicator_one _ _ $instα $instβ $s) =>
--     let so : Option Q(Finset.Nonempty $s) ← do -- TODO: It doesn't complain if we make a typo?
--       try
--         let _fi ← synthInstanceQ q(Fintype $α)
--         let _no ← synthInstanceQ q(Nonempty $α)
--         match s with
--         | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $α)))
--         | _ => pure none
--       catch _ => do
--         let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
--         pure (some (.fvar fv))
--     assumeInstancesCommute
--     match so with
--     | .some (fi : Q(Finset.Nonempty $s)) =>
--       try
--         let instβnontriv ← synthInstanceQ q(Nontrivial $K)
--         assumeInstancesCommute
--         return .positive q(Finset.Nonempty.indicator_one_pos $fi)
--       catch _ => return .nonnegative q(indicator_one_nonneg.{u, u_1})

--     | none => return .nonnegative q(indicator_one_nonneg.{u, u_1})
--   | _ => throwError "not Finset.indicator_one"

-- TODO: Fix

-- /-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
-- multiplicands are. -/
-- @[positivity]
-- unsafe def positivity_indicator_one : expr → tactic strictness
--   | e@q(@indicator_one $(α) $(K) $(hα) $(hβ) $(s)) ↦
--     (do
--         let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_mapp `` indicator_one_pos_of_nonempty [α, K, none, none, none, none, p])
--       do
--       nonnegative <$> mk_mapp `` indicator_one_nonneg [α, K, none, none, s]
--   | e@q(@mu $(α) $(K) $(hβ) $(hα) $(s)) ↦
--     (do
--         let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_app `` mu_pos_of_nonempty [p]) $>
--       nonnegative <$> mk_mapp `` mu_nonneg [α, K, none, none, s]
--   | e ↦ pp e >>= fail ∘ format.bracket "The expression `"
--       "` isn't of the form `𝟭_[s, K]` or `μ_[K] s`"

-- variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset α}

-- example : 0 ≤ 𝟭_[s, K] := by positivity
-- example : 0 ≤ μ_[K] s := by positivity
-- example (hs : s.Nonempty) : 0 < 𝟭_[s, K] := by positivity
-- example (hs : s.Nonempty) : 0 < μ_[K] s := by positivity

end Mathlib.Meta.Positivity
