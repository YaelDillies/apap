module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

import APAP.Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

@[expose] public section

open AddChar Function
open scoped NNReal ENNReal Finset

/-- A *Bohr set* `B` on an additive group `G` is a finite set of characters of `G`, called the
*frequencies*, along with an extended non-negative real number for each frequency `ψ`, called the
*width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet (G : Type*) [AddCommGroup G] where
  frequencies : Finset (AddChar G ℂ)
  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
  ewidth : AddChar G ℂ → ℝ≥0∞
  mem_frequencies : ∀ ψ, ψ ∈ frequencies ↔ ewidth ψ < ⊤

namespace BohrSet
variable {G : Type*} [AddCommGroup G] {B : BohrSet G} {ψ : AddChar G ℂ} {x : G}

def width (B : BohrSet G) (ψ : AddChar G ℂ) : ℝ≥0 := (B.ewidth ψ).toNNReal
lemma width_def : B.width ψ = (B.ewidth ψ).toNNReal := rfl

lemma coe_width (hψ : ψ ∈ B.frequencies) : B.width ψ = B.ewidth ψ := by
  refine ENNReal.coe_toNNReal ?_
  rwa [←lt_top_iff_ne_top, ←B.mem_frequencies]

lemma ewidth_eq_top_iff : ψ ∉ B.frequencies ↔ B.ewidth ψ = ⊤ := by
  simp [B.mem_frequencies]

alias ⟨ewidth_eq_top_of_not_mem_frequencies, _⟩ := ewidth_eq_top_iff

lemma width_eq_zero_of_not_mem_frequencies (hψ : ψ ∉ B.frequencies) : B.width ψ = 0 := by
  rw [width_def, ewidth_eq_top_of_not_mem_frequencies hψ, ENNReal.toNNReal_top]

lemma ewidth_injective : Function.Injective (BohrSet.ewidth (G := G)) := by
  intro B₁ B₂ h
  ext ψ
  case ewidth => rw [h]
  case frequencies => rw [B₁.mem_frequencies, B₂.mem_frequencies, h]

/-- Construct a Bohr set on a finite group given an extended width function. -/
noncomputable def ofEwidth [Finite G] (ewidth : AddChar G ℂ → ℝ≥0∞) : BohrSet G :=
  { frequencies := {ψ | ewidth ψ < ⊤},
    ewidth := ewidth,
    mem_frequencies := fun ψ => by simp }

/-- Construct a Bohr set on a finite group given a width function and a frequency set. -/
noncomputable def ofWidth (width : AddChar G ℂ → ℝ≥0) (freq : Finset (AddChar G ℂ)) :
    BohrSet G :=
  { frequencies := freq,
    ewidth := fun ψ => if ψ ∈ freq then width ψ else ⊤ ,
    mem_frequencies := fun ψ => by simp [lt_top_iff_ne_top] }

@[ext]
lemma ext_width {B B' : BohrSet G} (freq : B.frequencies = B'.frequencies)
    (width : ∀ ψ : AddChar G ℂ, ψ ∈ B.frequencies → B.width ψ = B'.width ψ) :
    B = B' := by
  ext
  case frequencies => rw [freq]
  case ewidth ψ =>
    by_cases hψ : ψ ∈ B.frequencies
    case pos =>
      rw [←coe_width hψ, width _ hψ, coe_width]
      rwa [←freq]
    case neg =>
      rw [ewidth_eq_top_of_not_mem_frequencies hψ, ewidth_eq_top_of_not_mem_frequencies]
      rwa [←freq]

/-! ### Coercion, membership -/

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def chordSet (B : BohrSet G) : Set G := {x | ∀ ψ, ‖1 - ψ x‖₊ ≤ B.ewidth ψ}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe, reducible] def Elem (B : BohrSet G) : Type _ := B.chordSet

instance instCoe : Coe (BohrSet G) (Set G) := ⟨chordSet⟩
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

lemma mem_chordSet_iff_nnnorm_ewidth : x ∈ B.chordSet ↔ ∀ ψ, ‖1 - ψ x‖₊ ≤ B.ewidth ψ := Iff.rfl

lemma mem_chordSet_iff_nnnorm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖₊ ≤ B.width ψ := by
  refine forall_congr' fun ψ => ?_
  constructor
  case mpr =>
    intro h
    rcases eq_top_or_lt_top (B.ewidth ψ) with h₁ | h₁
    case inl => simp [h₁]
    case inr =>
      have : ψ ∈ B.frequencies := by simp [mem_frequencies, h₁]
      specialize h this
      rwa [←ENNReal.coe_le_coe, coe_width this] at h
  case mp =>
    intro h₁ h₂
    rwa [←ENNReal.coe_le_coe, coe_width h₂]

lemma mem_chordSet_iff_norm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖ ≤ B.width ψ :=
  mem_chordSet_iff_nnnorm_width

@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl

@[simp] lemma zero_mem : 0 ∈ B.chordSet := by simp [mem_chordSet_iff_nnnorm_width]

-- TODO: This lemma needs `Finite G` because we are using `AddChar G ℂ` rather than `AddChar G ℂˣ`
-- as the dual group.
@[simp] lemma neg_mem [Finite G] : -x ∈ B.chordSet ↔ x ∈ B.chordSet :=
  forall_congr' fun ψ ↦ by rw [Iff.comm, ← RCLike.nnnorm_conj, map_sub, map_one, map_neg_eq_conj]

/-! ### Lattice structure -/

noncomputable instance : Max (BohrSet G) where
  max B₁ B₂ :=
    { frequencies := B₁.frequencies ∩ B₂.frequencies,
      ewidth := fun ψ => B₁.ewidth ψ ⊔ B₂.ewidth ψ,
      mem_frequencies := fun ψ => by simp [mem_frequencies] }

noncomputable instance : Min (BohrSet G) where
  min B₁ B₂ := {
    frequencies := B₁.frequencies ∪ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊓ B₂.ewidth ψ,
    mem_frequencies ψ := by simp [mem_frequencies]
  }

noncomputable instance [Finite G] : Bot (BohrSet G) where
  bot.frequencies := ⊤
  bot.ewidth := 0
  bot.mem_frequencies := by simp

noncomputable instance : Top (BohrSet G) where
  top.frequencies := ⊥
  top.ewidth := ⊤
  top.mem_frequencies := by simp

noncomputable instance : DistribLattice (BohrSet G) :=
  ewidth_injective.distribLattice BohrSet.ewidth (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

lemma le_iff_ewidth {B₁ B₂ : BohrSet G} : B₁ ≤ B₂ ↔ ∀ ⦃ψ⦄, B₁.ewidth ψ ≤ B₂.ewidth ψ := Iff.rfl

@[gcongr]
lemma frequencies_anti {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₂.frequencies ⊆ B₁.frequencies := by
  intro ψ hψ
  simp only [mem_frequencies] at hψ ⊢
  exact (h ψ).trans_lt hψ

lemma frequencies_antitone : Antitone (frequencies : BohrSet G → _) := fun _ _ ↦ frequencies_anti

lemma le_iff_width {B₁ B₂ : BohrSet G} : B₁ ≤ B₂ ↔
    B₂.frequencies ⊆ B₁.frequencies ∧ ∀ ⦃ψ⦄, ψ ∈ B₂.frequencies → B₁.width ψ ≤ B₂.width ψ := by
  constructor
  case mp =>
    intro h
    refine ⟨frequencies_anti h, fun ψ hψ => ?_⟩
    rw [←ENNReal.coe_le_coe, coe_width hψ, coe_width (frequencies_anti h hψ)]
    exact h ψ
  case mpr =>
    rintro ⟨h₁, h₂⟩ ψ
    by_cases ψ ∈ B₂.frequencies
    case neg h' => simp [ewidth_eq_top_of_not_mem_frequencies h']
    case pos h' =>
      rw [←coe_width h', ←coe_width (h₁ h'), ENNReal.coe_le_coe]
      exact h₂ h'

@[gcongr]
lemma width_le_width {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) {ψ : AddChar G ℂ} (hψ : ψ ∈ B₂.frequencies) :
    B₁.width ψ ≤ B₂.width ψ := by
  rw [le_iff_width] at h
  exact h.2 hψ

noncomputable instance : OrderTop (BohrSet G) := OrderTop.lift BohrSet.ewidth (fun _ _ h => h) rfl

example [Finite G] : Finite (AddChar G ℂ) := by infer_instance

open scoped Classical in
noncomputable instance [Finite G] : SupSet (BohrSet G) where
  sSup B := {
    frequencies := {ψ | ⨆ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨆ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }

lemma iInf_lt_top {α β : Type*} [CompleteLattice β] {S : Set α} {f : α → β} :
    (⨅ i ∈ S, f i) < ⊤ ↔ ∃ i ∈ S, f i < ⊤ := by
  simp [lt_top_iff_ne_top]

open scoped Classical in
noncomputable instance [Finite G] : InfSet (BohrSet G) where
  sInf B := {
    frequencies := {ψ | ∃ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨅ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }

noncomputable def minimalAxioms [Finite G] :
    CompletelyDistribLattice.MinimalAxioms (BohrSet G) :=
  ewidth_injective.completelyDistribLatticeMinimalAxioms .of BohrSet.ewidth
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun B => by
      ext ψ
      simp only [iSup_apply]
      rfl)
    (fun B => by
      ext ψ
      simp only [iInf_apply]
      rfl)
    rfl
    rfl

noncomputable instance [Finite G] : CompletelyDistribLattice (BohrSet G) :=
  .ofMinimalAxioms BohrSet.minimalAxioms

/-! ### Width, frequencies, rank -/

/-- The rank of a Bohr set is the number of characters which have finite width. -/
def rank (B : BohrSet G) : ℕ := #B.frequencies

@[simp] lemma card_frequencies (B : BohrSet G) : #B.frequencies = B.rank := rfl

/-! ### Dilation -/

section smul
variable {ρ : ℝ}

lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ :=
  ENNReal.mul_lt_top (by simp) hy

lemma nnreal_smul_lt_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y < ⊤ ↔ y < ⊤ := by
  constructor
  case mpr => exact nnreal_smul_lt_top
  case mp =>
    intro h
    by_contra hy
    simp only [top_le_iff, not_lt] at hy
    simp [hy, ENNReal.smul_top, hx] at h

lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) hy

lemma nnreal_smul_ne_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y ≠ ⊤ ↔ y ≠ ⊤ := by
  constructor
  case mpr => exact nnreal_smul_ne_top
  case mp =>
    intro h
    by_contra hy
    simp [hy, ENNReal.smul_top, hx] at h

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := BohrSet.mk B.frequencies
      (fun ψ => if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤) fun ψ => by
        simp only [lt_top_iff_ne_top, ite_ne_right_iff, iff_self_and]
        intro hψ
        refine ENNReal.mul_ne_top (by simp) ?_
        rwa [←lt_top_iff_ne_top, ←mem_frequencies]

@[simp] lemma frequencies_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).frequencies = B.frequencies := rfl
@[simp] lemma rank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).rank = B.rank := rfl

@[simp] lemma ewidth_smul (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).ewidth ψ = if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤ := rfl

@[simp] lemma width_smul_apply (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).width ψ = Real.nnabs ρ * B.width ψ := by
  rw [width_def, ewidth_smul]
  split
  case isTrue h => simp [←coe_width h]
  case isFalse h => simp [width_eq_zero_of_not_mem_frequencies h]

lemma width_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).width = Real.nnabs ρ • B.width := by
  ext ψ
  simp [width_smul_apply]

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by ext <;> simp
  mul_smul ρ φ B := by ext <;> simp [mul_assoc]

end smul

-- Note it is not sufficient to say B.width = 0.
lemma eq_zero_of_ewidth_eq_zero {B : BohrSet G} [Finite G] (h : B.ewidth = 0) :
    B.chordSet = {0} := by
  rw [Set.eq_singleton_iff_unique_mem]
  simp only [mem_chordSet_iff_nnnorm_width, map_zero_eq_one, sub_self, nnnorm_zero, zero_le,
    implies_true, true_and]
  intro x hx
  by_contra!
  rw [←AddChar.exists_apply_ne_zero] at this
  obtain ⟨ψ, hψ⟩ := this
  apply hψ
  have hψ' : ψ ∈ B.frequencies := by simp [B.mem_frequencies, h]
  specialize hx hψ'
  rwa [B.width_def, h, Pi.zero_apply, ENNReal.toNNReal_zero, nonpos_iff_eq_zero, nnnorm_eq_zero,
    sub_eq_zero, eq_comm] at hx

@[simp] lemma AddChar.nnnorm_apply {α G : Type*}
    [NormedDivisionRing α] [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖₊ = 1 :=
  NNReal.coe_injective (by simp)

lemma eq_top_of_two_le_width {B : BohrSet G} [Finite G] (h : ∀ ψ, 2 ≤ B.width ψ) :
    B.chordSet = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_chordSet_iff_nnnorm_width]
  intro i ψ _
  calc ‖1 - ψ i‖₊ ≤ ‖(1 : ℂ)‖₊ + ‖ψ i‖₊ := nnnorm_sub_le _ _
    _ = 2 := by norm_num
    _ ≤ B.width ψ := h _

@[gcongr] lemma chordSet_mono {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₁.chordSet ⊆ B₂.chordSet :=
  fun _ hx ψ => (hx ψ).trans (h ψ)

lemma chordSet_monotone : Monotone (chordSet : BohrSet G → Set G) := fun _ _ => chordSet_mono

open Pointwise

lemma add_subset_of_ewidth [Finite G] {B₁ B₂ B₃ : BohrSet G}
    (h : B₁.ewidth + B₂.ewidth ≤ B₃.ewidth) :
    B₁.chordSet + B₂.chordSet ⊆ B₃.chordSet := by
  intro x
  simp only [mem_chordSet_iff_nnnorm_ewidth, Set.mem_add, forall_exists_index, and_imp]
  rintro x hx y hy rfl ψ
  rw [map_add_eq_mul]
  have : ‖1 - ψ x * ψ y‖₊ ≤ ‖1 - ψ x‖₊ + _ := nnnorm_one_sub_mul (by simp)
  rw [←ENNReal.coe_le_coe, ENNReal.coe_add] at this
  exact this.trans <| (h _).trans' <| add_le_add (hx _) (hy _)

lemma smul_add_smul_subset [Finite G] {B : BohrSet G} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    (ρ₁ • B).chordSet + (ρ₂ • B).chordSet ⊆ ((ρ₁ + ρ₂) • B).chordSet :=
  add_subset_of_ewidth fun ψ => by
    simp only [Pi.add_apply, ewidth_smul]; split <;> simp [add_nonneg, add_mul, *]

end BohrSet

-- variable {ρ : ℝ}

-- lemma le_card_smul (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
--     (ρ / 4) ^ B.rank * Nat.card B ≤ Nat.card ↥(ρ • B) := by
--   sorry
