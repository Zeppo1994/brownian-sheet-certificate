import BrownianSharp.AlignmentPeriodicL1CutoffSobolevReconstruction
import BrownianSharp.AlignmentPaperPeriodic

/-!
Theorem 1.3 (two-sided entropy, Sobolev with `p ≠ ∞` and Nikol'skii) for the literal
full-`L¹` source classes, via the continuous-representative identification.
-/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperFullL1PeriodicEntropy

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.Torus

/-- Theorem 1.3 for the full-`L¹` classes. -/
def FullL1PeriodicEndpointEntropyStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1 / 2 < r →
      (p ≠ ⊤ → twoSidedEntropyRate
        (AlignmentPeriodicL1AdmissibleEntropyBoundary.fullL1SobolevImage (d := d) φ p.toReal r)
        r (r * (d - 1 : ℕ) + 1 / 2)) ∧
      twoSidedEntropyRate
        (AlignmentPeriodicL1AdmissibleEntropyBoundary.fullL1NikolskyImage (d := d) φ p r)
        r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)

theorem fullL1PeriodicEndpointEntropy_certified : FullL1PeriodicEndpointEntropyStatement := by
  intro φ d hd p hp r hr
  obtain ⟨hS, hN⟩ := periodic_sobolev_nikolsky_entropy_equivalent φ hd hp hr
  refine ⟨fun hpt => ?_, ?_⟩
  · rw [AlignmentPeriodicL1CutoffSobolevReconstruction.fullL1SobolevImage_eq_continuous_image φ
      ((ENNReal.toReal_le_toReal (by norm_num) hpt).2 hp |>.trans_eq' (by simp)) hr]
    exact hS hpt
  · rw [AlignmentPeriodicL1AdmissibleReconstruction.fullL1NikolskyImage_eq_continuous φ p hp r hr]
    exact hN

end BrownianSharp.AlignmentPaperFullL1PeriodicEntropy
