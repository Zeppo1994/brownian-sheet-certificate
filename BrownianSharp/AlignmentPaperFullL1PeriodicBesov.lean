import BrownianSharp.AlignmentPeriodicL1CutoffBesovReconstruction
import BrownianSharp.AlignmentPaperPeriodicComplete

/-! The sharp periodic Besov entropy and width equivalences also hold for the
literal full-L¹ image: in the upper-bound range, every element has a
continuous representative in the same actual cutoff ball. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperFullL1PeriodicBesov

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
open BrownianSharp.AlignmentPeriodicL1CutoffBesovReconstruction
open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.AlignmentPaperPeriodicComplete
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.Latest
open BrownianSharp.Torus

/-- Full-L¹ Besov images have the paper's two-sided periodic entropy and
strict-index Kolmogorov rates whenever p, theta ≥ 2 and r > 1/2. The proof
identifies the actual L¹ image with its continuous representatives, then
transfers both equivalences for the same cutoff ball. -/
theorem fullL1_periodic_besov_entropy_width_equivalent
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r)
    {θ : ℝ≥0∞} (hθ : 2 ≤ θ) :
    twoSidedEntropyRate
      (fullL1BesovImage (d := d) φ p r θ)
      r ((r + 1/2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1/2) ∧
    AlignmentOperatorStatements.twoSidedWidthRate
      (fullL1BesovImage (d := d) φ p r θ)
      r ((r + 1/2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1/2) := by
  have himage : fullL1BesovImage (d := d) φ p r θ =
      Latest.periodicLInfinityImage
        {f : RealPeriodic d | BesovUnitBall φ p r θ f} := by
    simpa [Latest.periodicLInfinityImage] using
      (fullL1BesovImage_eq_continuous_image (d := d) φ p θ hp hθ r hr)
  simpa only [himage] using
    (periodicBesov_entropy_width_equivalent φ hd hp hr hθ)

end BrownianSharp.AlignmentPaperFullL1PeriodicBesov
