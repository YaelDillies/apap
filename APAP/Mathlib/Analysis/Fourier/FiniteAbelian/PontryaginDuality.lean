module

public import APAP.Mathlib.Algebra.Module.AddChar
public import APAP.Mathlib.Algebra.Module.ZMod
public import APAP.Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Algebra.Field.ZMod

import APAP.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open scoped Finset

namespace AddChar
variable {ι G : Type*} {q : ℕ} [AddCommGroup G]

section
variable {Δ : Set (AddChar G ℂ)} {ψ : AddChar G ℂ} {x : G}

lemma map_eq_one_of_mem_closure (hψ : ψ ∈ AddSubgroup.closure Δ) (hx : ∀ γ ∈ Δ, γ x = 1) :
    ψ x = 1 := (doubleDualEmb x).toAddMonoidHom.ker.closure_le.2 (hx · <| by simpa using ·) hψ

variable [Finite G]

@[simp] lemma map_doubleDualEquiv_symm (χ : AddChar (AddChar G ℂ) ℂ) (ψ : AddChar G ℂ) :
    ψ (doubleDualEquiv.symm χ) = χ ψ :=
  congr($(doubleDualEmb_doubleDualEquiv_symm_apply χ) ψ)

lemma mem_closure_iff : ψ ∈ AddSubgroup.closure Δ ↔ ∀ x, (∀ γ ∈ Δ, γ x = 1) → ψ x = 1 where
  mp hψ x hx := map_eq_one_of_mem_closure hψ hx
  mpr hψ := by
    contrapose! hψ
    let H : AddSubgroup (AddChar G ℂ) := AddSubgroup.closure Δ
    have hquot : QuotientAddGroup.mk ψ ≠ (0 : AddChar G ℂ ⧸ H) := fun h ↦ hψ <| by simpa using h
    obtain ⟨χ, hχ⟩ := exists_apply_ne_zero.2 hquot
    let χ' : AddChar (AddChar G ℂ) ℂ := χ.compAddMonoidHom (QuotientAddGroup.mk' H)
    refine ⟨doubleDualEquiv.symm χ', fun γ hγ ↦ ?_, by simpa [χ'] using hχ⟩
    have hγH : γ ∈ H := AddSubgroup.subset_closure hγ
    simp [χ', (QuotientAddGroup.eq_zero_iff _).2 hγH]

end

variable [Module (ZMod q) G] {γ : AddChar G ℂ} {r : ZMod q} {x : G}

variable (q γ) in
/-- Characters of a `q`-group `G` are (noncanonically) the same as `ZMod q`-linear forms on `G`. -/
@[expose, simps! -isSimp]
noncomputable def toZModLinearMap [NeZero q] : G →ₗ[ZMod q] ZMod q :=
  (zmodAddEquiv.symm.toAddMonoidHom.comp <| γ.toAddMonoidHomAddChar).toZModLinearMap q

@[simp]
lemma toZModLinearMap_eq_zero [Fact <| 1 < q] : toZModLinearMap q γ x = 0 ↔ γ x = 1 := by
  simp +contextual only [toZModLinearMap_apply, EmbeddingLike.map_eq_zero_iff, DFunLike.ext_iff,
    toAddMonoidHomAddChar_apply_apply, map_zmod_smul, zero_apply, iff_iff_implies_and_implies,
    one_pow, implies_true, and_true]
  rintro h
  simpa [ZMod.val_one] using h 1

@[simp]
lemma ker_toZModLinearMap [Fact <| 1 < q] :
    (toZModLinearMap q γ).ker = γ.toAddMonoidHom.ker.toZModSubmodule q := by ext; simp

variable [Fact q.Prime] [FiniteDimensional (ZMod q) G] {γ : ι → AddChar G ℂ}
  {s : Finset ι}

lemma codim_iInf_ker_le_fintypeCard [Fintype ι] :
    Module.finrank (ZMod q) G - (⨅ i, (γ i).toAddMonoidHom.ker.toZModSubmodule q).finrank
      ≤ Fintype.card ι := by
  simpa using Module.codim_iInf_ker_le_fintypeCard (f := fun i ↦ (γ i).toZModLinearMap q)

lemma codim_iInf_ker_le_finsetCard :
    Module.finrank (ZMod q) G - ((⨅ i ∈ s, (γ i).toAddMonoidHom.ker).toZModSubmodule q).finrank
      ≤ #s := by
  simpa [iInf_subtype] using codim_iInf_ker_le_fintypeCard (ι := s) (γ := fun i ↦ γ i)

end AddChar
