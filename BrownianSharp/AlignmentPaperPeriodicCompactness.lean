import BrownianSharp.AlignmentPaperPeriodicEntropyDecay
import BrownianSharp.AlignmentPaperEntropyCompactness
import BrownianSharp.AlignmentContinuousLInfinity
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Topology.UniformSpace.Cauchy

/-! Compact closure of the actual continuous periodic Sobolev-2 unit ball,
obtained from its proved entropy decay in the isometric L-infinity image. -/

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped NNReal ENNReal

namespace BrownianSharp.AlignmentPaperPeriodicCompactness

open BrownianSharp.AlignmentAmbientWidth
open BrownianSharp.AlignmentPaperEntropyCompactness
open BrownianSharp.AlignmentPaperPeriodicEntropyDecay
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.Latest
open BrownianSharp.Torus
open UnitAddTorus

/-- The closure in the actual continuous-function norm of the smooth periodic
Sobolev-2 unit ball is compact for `r>1/2`. -/
theorem smoothSobolev_unitBall_closure_isCompact {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 1/2 < r) :
    IsCompact (closure {f : C(UnitAddTorus (Fin d), ℝ) |
      SobolevUnitBall BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff 2 r f}) := by
  let Kc : Set C(UnitAddTorus (Fin d), ℝ) :=
    {f | SobolevUnitBall BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff 2 r f}
  let KL : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff 2 r f}
  have hdecay := smoothSobolev_entropy_tendsto_zero hd hr
  have hdecayKL : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ,
      HaarQuarter.TheoremD.entropyNumber k KL < (ε : ℝ≥0∞) := by
    simpa only [KL, ← SobolevUnitBall_fixed] using hdecay
  have hTB_L : TotallyBounded KL :=
    totallyBounded_of_entropy_vanishes KL hdecayKL
  have himage : continuousToLInfinity
      (volume : Measure (UnitAddTorus (Fin d))) '' Kc = KL := by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f,hf,rfl⟩
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f,hf,rfl⟩
  have hTB_C : TotallyBounded Kc := by
    rw [← totallyBounded_image_iff
      ((continuousToLInfinity (volume : Measure (UnitAddTorus (Fin d)))).isometry.isUniformEmbedding.isUniformInducing)]
    rw [himage]
    exact hTB_L
  have hclosed : IsClosed (closure Kc) := isClosed_closure
  have hTBclosure : TotallyBounded (closure Kc) :=
    totallyBounded_closure.mpr hTB_C
  have hcompact : IsCompact (closure Kc) := hTBclosure.isCompact_of_isClosed hclosed
  simpa [Kc] using hcompact

end BrownianSharp.AlignmentPaperPeriodicCompactness
