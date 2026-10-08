import APAP.FiniteField

/-!
# Solution: bridge from Challenge to the APAP library
-/

noncomputable section

namespace Comparator

theorem ff {G : Type u} [AddCommGroup G] [Fintype G] {A : Finset G} {q : ℕ} [Module (ZMod q) G]
    (hq₃ : 3 ≤ q) (hq : Nat.Prime q) (hA₀ : A.Nonempty) (hA : ThreeAPFree (↑A : Set G)) :
    ↑(Module.finrank (ZMod q) G) ≤ (2 ^ 148 * (1 + Real.log (↑A.dens)⁻¹) ^ 9 : ℝ) :=
  _root_.ff hq₃ hq hA₀ hA

end Comparator
