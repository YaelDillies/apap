module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

public section

open ENNReal

namespace MeasureTheory
variable {𝕜 α : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]

/-- Hölder's inequality. -/
theorem eLpNorm_mul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f g : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) [HolderTriple p q r] :
    eLpNorm (f * g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  simpa using eLpNorm_smul_le_mul_eLpNorm hg hf

end MeasureTheory
