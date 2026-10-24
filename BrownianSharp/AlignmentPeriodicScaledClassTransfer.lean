import BrownianSharp.AlignmentFractionalEntropyTransfer
import BrownianSharp.AlignmentScaledSetWidth
import BrownianSharp.AlignmentLatestStatements

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.Torus

theorem entropyNumber_ge_of_scaled_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K J : Set X) (c E : ℝ) (hc : 0 < c) (hE : 0 ≤ E)
    (hsub : (fun x : X => c • x) '' J ⊆ K)
    (k : ℕ) (hJ : ENNReal.ofReal E ≤ HaarQuarter.TheoremD.entropyNumber k J) :
    ENNReal.ofReal (c * E) ≤ HaarQuarter.TheoremD.entropyNumber k K := by
  apply AlignmentFractionalEntropyTransfer.entropyNumber_ge_of_scaled_contractive_image
    (ContinuousLinearMap.id ℝ X) (ContinuousLinearMap.norm_id_le) K J c E hc hE
    (by simpa using hsub) k hJ

theorem scaled_periodicImage_subset {d : ℕ} (K J : Set (RealPeriodic d))
    (c : ℝ) (hsub : ∀ f ∈ J, c • f ∈ K) :
    (fun x => c • x) '' Latest.periodicLInfinityImage J ⊆
      Latest.periodicLInfinityImage K := by
  rintro y ⟨z, ⟨f, hf, rfl⟩, rfl⟩
  refine ⟨c • f, hsub f hf, ?_⟩
  exact map_smul (ContinuousMap.toLp ⊤ volume ℝ) c f

theorem periodicImage_subset_scalarImage {d : ℕ}
    (K J : Set (RealPeriodic d)) (A : ℝ) (hA : 0 < A)
    (hsub : ∀ f ∈ K, A⁻¹ • f ∈ J) :
    Latest.periodicLInfinityImage K ⊆
      (fun x => A • x) '' Latest.periodicLInfinityImage J := by
  rintro y ⟨f, hf, rfl⟩
  refine ⟨(ContinuousMap.toLp ⊤ volume ℝ) (A⁻¹ • f),
    ⟨A⁻¹ • f, hsub f hf, rfl⟩, ?_⟩
  simp only [map_smul, smul_smul, mul_inv_cancel₀ hA.ne', one_smul]

end BrownianSharp.AlignmentPeriodicScaledClassTransfer
