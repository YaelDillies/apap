module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

import APAP.Mathlib.Analysis.RCLike.Basic

public section

open scoped ENNReal

namespace MeasureTheory
variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

@[simp]
lemma eLpNorm_rclikeOfReal_comp (p : ℝ≥0∞) (f : α → ℝ) :
    eLpNorm (fun a ↦ (f a : 𝕜)) p μ = eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLpNorm_congr_norm_ae (RCLike.continuous_ofReal.comp_aestronglyMeasurable hf) hf <| by
      simp
  · have hf' : ¬ AEStronglyMeasurable (fun a ↦ ((f a : ℝ) : 𝕜)) μ := by
      rwa [_root_.RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
    rw [eLpNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hf']

end MeasureTheory
