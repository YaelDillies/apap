module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import APAP.Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Positivity.Finset

/-!
# Lp norms
-/

@[expose] public section

open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {α 𝕜 R E : Type*} [MeasurableSpace α]

namespace MeasureTheory
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}

/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def dLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ := lpNorm f p .count

notation "‖" f "‖_[" p "]" => dLpNorm p f

@[simp] lemma dLpNorm_nonneg : 0 ≤ ‖f‖_[p] := by simp [dLpNorm]

@[simp] lemma dLpNorm_exponent_zero (f : α → E) : ‖f‖_[0] = 0 := by simp [dLpNorm]

@[simp] lemma dLpNorm_zero (p : ℝ≥0∞) : ‖(0 : α → E)‖_[p] = 0 := by simp [dLpNorm]
@[simp] lemma dLpNorm_zero' (p : ℝ≥0∞) : ‖(fun _ ↦ 0 : α → E)‖_[p] = 0 := by simp [dLpNorm]

@[simp] lemma dLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : ‖f‖_[p] = 0 := by
  simp [dLpNorm]

@[simp] lemma dLpNorm_neg (f : α → E) (p : ℝ≥0∞) : ‖-f‖_[p] = ‖f‖_[p] := by simp [dLpNorm]
@[simp] lemma dLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : ‖fun x ↦ -f x‖_[p] = ‖f‖_[p] := by
  simp [dLpNorm]

lemma dLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : ‖f - g‖_[p] = ‖g - f‖_[p] := by
  simp [dLpNorm, lpNorm_sub_comm]

@[simp]
lemma dLpNorm_norm (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖fun i ↦ ‖f i‖‖_[p] = ‖f‖_[p] :=
  lpNorm_norm hf.aestronglyMeasurable _

@[simp]
lemma dLpNorm_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖|f|‖_[p] = ‖f‖_[p] :=
  lpNorm_abs hf.aestronglyMeasurable _

@[simp]
lemma dLpNorm_fun_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    ‖fun i ↦ |f i|‖_[p] = ‖f‖_[p] :=
  lpNorm_fun_abs hf.aestronglyMeasurable _

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

lemma dLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] := by simp [dLpNorm, lpNorm_const_smul]

lemma dLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    ‖n • f‖_[p] = n • ‖f‖_[p] := by simp [dLpNorm, lpNorm_nsmul]

variable [NormedSpace ℝ 𝕜]

lemma dLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n : α → 𝕜) * f‖_[p] = n * ‖f‖_[p] :=
  lpNorm_natCast_mul ..

lemma dLpNorm_fun_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n * f ·)‖_[p] = n * ‖f‖_[p] :=
  lpNorm_fun_natCast_mul ..

lemma dLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖f * (n : α → 𝕜)‖_[p] = ‖f‖_[p] * n :=
  lpNorm_mul_natCast ..

lemma dLpNorm_fun_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖(f · * n)‖_[p] = ‖f‖_[p] * n :=
  lpNorm_fun_mul_natCast ..

lemma dLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖f / (n : α → 𝕜)‖_[p] = ‖f‖_[p] / n := lpNorm_div_natCast hn ..

lemma dLpNorm_fun_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖(f · / n)‖_[p] = ‖f‖_[p] / n := lpNorm_fun_div_natCast hn ..

end NormedField

lemma dLpNorm_nnqsmul (q : ℚ≥0) (f : α → ℂ) : ‖q • f‖_[p] = q * ‖f‖_[p] := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using dLpNorm_const_smul (q : ℂ) f

section RCLike
variable {p : ℝ≥0∞}

@[simp] lemma dLpNorm_conj [RCLike R] (f : α → R) : ‖conj f‖_[p] = ‖f‖_[p] := lpNorm_conj ..

end RCLike

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]

lemma dLpNorm_add_le (hp : 1 ≤ p) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  lpNorm_add_le .of_discrete hp

lemma dLpNorm_sub_le (hp : 1 ≤ p) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  lpNorm_sub_le .of_discrete hp

lemma dLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hp : 1 ≤ p) :
    ‖∑ i ∈ s, f i‖_[p] ≤ ∑ i ∈ s, ‖f i‖_[p] := lpNorm_sum_le (fun _ _ ↦ .of_discrete) hp

lemma dLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : ‖𝔼 i ∈ s, f i‖_[p] ≤ 𝔼 i ∈ s, ‖f i‖_[p] :=
  lpNorm_expect_le (fun _ _ ↦ .of_discrete) hp

lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub' (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖g‖_[p] + ‖f - g‖_[p] :=
  lpNorm_le_lpNorm_add_lpNorm_sub' .of_discrete hp

lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖g‖_[p] + ‖g - f‖_[p] :=
  lpNorm_le_lpNorm_add_lpNorm_sub .of_discrete hp

lemma dLpNorm_le_add_dLpNorm_add (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖f + g‖_[p] + ‖g‖_[p] :=
  lpNorm_le_add_lpNorm_add .of_discrete hp

lemma dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (hp : 1 ≤ p) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
  lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp

end DiscreteMeasurableSpace

variable [Fintype α]

@[simp]
lemma dLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]

@[simp]
lemma dLpNorm_const' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

@[simp] lemma dLpNorm_one [Nonempty α] (hp : p ≠ 0) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]

@[simp] lemma dLpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]

end NormedField

variable [DiscreteMeasurableSpace α]

lemma dLpNorm_eq_sum_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [dLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, integral_fintype]

lemma dLpNorm_toNNReal_eq_sum_norm {p : ℝ} (hp : 0 < p) (f : α → E) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [dLpNorm_eq_sum_norm'] <;> simp [hp.le, hp]

lemma dLpNorm_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  dLpNorm_eq_sum_norm' (by simpa using hp) (by simp) _

lemma dLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) := by
  rw [dLpNorm_eq_sum_norm hp, Real.rpow_inv_rpow (by positivity) (mod_cast hp)]

lemma dLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) : ‖f‖_[p] ^ p = ∑ i, ‖f i‖ ^ p := by
  simpa using dLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) f

lemma dL2Norm_sq_eq_sum_norm (f : α → E) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using dLpNorm_pow_eq_sum_norm two_ne_zero _

lemma dL2Norm_eq_sum_norm (f : α → E) : ‖f‖_[2] = (∑ i, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using dLpNorm_eq_sum_norm two_ne_zero _

lemma dL1Norm_eq_sum_norm (f : α → E) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [dLpNorm_eq_sum_norm']

omit [Fintype α]
variable [Finite α]

lemma dLinftyNorm_eq_iSup_norm (f : α → E) : ‖f‖_[∞] = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α <;> simp [dLpNorm, lpNorm_exponent_top_eq_essSup]

lemma norm_le_dLinftyNorm {i : α} : ‖f i‖ ≤ ‖f‖_[∞] := by
  rw [dLinftyNorm_eq_iSup_norm]; exact le_ciSup (f := fun i ↦ ‖f i‖) (Finite.bddAbove_range _) i

@[simp] lemma dLpNorm_eq_zero (hp : p ≠ 0) : ‖f‖_[p] = 0 ↔ f = 0 := by
  simp [dLpNorm, lpNorm_eq_zero .of_discrete hp, ae_eq_top.2]

@[simp] lemma dLpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖_[p] ↔ f ≠ 0 :=
  lpNorm_nonneg.lt_iff_ne'.trans (dLpNorm_eq_zero hp).not

lemma dLpNorm_mono_real {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : ‖f‖_[p] ≤ ‖g‖_[p] :=
  lpNorm_mono_real .of_discrete h

omit [Finite α]
variable [Fintype α]

lemma dLpNorm_two_mul_sum_pow {ι : Type*} {n : ℕ} (hn : n ≠ 0) (s : Finset ι) (f : ι → α → ℂ) :
    ‖∑ i ∈ s, f i‖_[2 * n] ^ (2 * n) =
      ∑ x ∈ s ^^ n, ∑ y ∈ s ^^ n, ∑ a, (∏ i, conj (f (x i) a)) * ∏ i, f (y i) a :=
  calc
    _ = ∑ a, (‖∑ i ∈ s, f i a‖ : ℂ) ^ (2 * n) := by
      norm_cast
      rw [← dLpNorm_pow_eq_sum_norm (by positivity)]
      simp_rw [← Finset.sum_apply]
    _ = ∑ a, (∑ i ∈ s, conj (f i a)) ^ n * (∑ j ∈ s, f j a) ^ n := by
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by simp_rw [sum_pow', sum_mul_sum, sum_comm (s := univ)]

end MeasureTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

alias ⟨_, dLpNorm_pos_of_ne_zero⟩ := dLpNorm_pos

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity ‖_‖_[_]] meta def evalDLpNorm : PositivityExt where eval {u} R _z _p e := do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@dLpNorm $α $E $instαmeas $instEnorm $p $f) =>
    assumeInstancesCommute
    try {
      let some pp := (← core q(inferInstance) q(inferInstance) p).toNonzero _ _ | failure
      try
        let _pE ← synthInstanceQ q(PartialOrder $E)
        let _ ← synthInstanceQ q(Finite $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        let some pf := (← core q(inferInstance) q(inferInstance) f).toNonzero _ _ | failure
        return .positive q(@dLpNorm_pos_of_ne_zero $α _ _ _ _ _ _ _ $pp $pf)
      catch _ =>
        assumeInstancesCommute
        let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
        let pf : Q($f ≠ 0) := .fvar pf
        let _ ← synthInstanceQ q(Fintype $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        return .positive q(dLpNorm_pos_of_ne_zero $pp $pf)
    } catch _ =>
      return .nonnegative q(dLpNorm_nonneg)
  | _ => throwError "not dLpNorm"

section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end NormedAddCommGroup

section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {f : α → ℂ}

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end Complex
end Examples
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma dLpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖_[p] = ‖f‖_[p * q] ^ (q : ℝ) := by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity)
    (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_mul (by positivity), ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    dLpNorm_rpow_eq_sum_norm hp, dLpNorm_rpow_eq_sum_norm (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), ← rpow_mul]

lemma dLpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    ‖f ^ q‖_[p] = ‖f‖_[p * q] ^ q := by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity)
    (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_natCast_mul (by positivity), ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ← NNReal.coe_natCast, ← NNReal.coe_mul, dLpNorm_rpow_eq_sum_norm hp,
    dLpNorm_rpow_eq_sum_norm (by positivity)]
  simp [← rpow_natCast_mul]

lemma dL1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖_[1] = ‖f‖_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_rpow one_ne_zero hq hf

lemma dL1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : ‖f ^ q‖_[1] = ‖f‖_[q] ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_pow one_ne_zero hq f

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

lemma dLpNorm_eq_dL1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] = ‖fun a ↦ ‖f a‖ ^ (p : ℝ)‖_[1] ^ (p⁻¹ : ℝ) := by
  cases nonempty_fintype α
  simp [dLpNorm_eq_sum_norm hp, dL1Norm_eq_sum_norm, abs_rpow_of_nonneg]

lemma dLpNorm_rpow' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hq : q ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] ^ (q : ℝ) = ‖(fun a ↦ ‖f a‖) ^ (q : ℝ)‖_[p / q] := by
  lift p to ℝ≥0 using hp
  simp only [ne_eq, ENNReal.coe_eq_zero] at hp₀
  rw [← ENNReal.coe_div hq, dLpNorm_rpow (div_ne_zero hp₀ hq) hq (fun _ ↦ norm_nonneg _),
    dLpNorm_norm .of_discrete, ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]

end Hoelder

section
variable {α : Type*} {mα : MeasurableSpace α}

@[simp]
lemma RCLike.dLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) : ‖((↑) : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [dLpNorm, lpNorm, comp_def]
  rw! (castMode := .all)
    [RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
  simp [eLpNorm, eLpNorm', eLpNormEssSup]

@[simp] lemma Complex.dLpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖_[p] = ‖f‖_[p] :=
  RCLike.dLpNorm_coe_comp ..

end
end MeasureTheory
