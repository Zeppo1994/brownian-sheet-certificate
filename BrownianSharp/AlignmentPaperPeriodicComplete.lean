import BrownianSharp.AlignmentPaperBesovInterpolation
import BrownianSharp.AlignmentPaperPeriodicBesov

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperPeriodicComplete
open AlignmentPeriodicAdmissibleCutoff AlignmentPeriodicCutoffClasses
open AlignmentPaperPeriodic Torus

theorem periodicBesov_entropy_width_equivalent
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r)
    {θ : ℝ≥0∞} (hθ : 2 ≤ θ) :
    twoSidedEntropyRate
      (Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r θ f})
      r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) ∧
    AlignmentOperatorStatements.twoSidedWidthRate
      (Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r θ f})
      r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) := by
  by_cases htop : θ = ⊤
  · subst θ
    have he := (periodic_sobolev_nikolsky_entropy_equivalent φ hd hp hr).2
    have hw := (AlignmentPeriodicCutoffCertified.periodic_width_certified φ d hd p hp r hr).2
    constructor
    · simpa [NikolskyUnitBall] using he
    · simpa [NikolskyUnitBall] using hw
  · have hreal : (2 : ℝ) ≤ θ.toReal := by
      have h := (ENNReal.toReal_le_toReal (by norm_num : (2:ℝ≥0∞) ≠ ⊤) htop).2 hθ
      simpa using h
    by_cases htwo : θ = 2
    · subst θ
      have hexp : (r+1/2-(2:ℝ≥0∞).toReal⁻¹)*(d-1:ℕ)+1/2 =
          r*(d-1:ℕ)+1/2 := by norm_num
      rw [hexp]
      exact ⟨AlignmentPaperPeriodicBesov.periodic_besov_theta_two_entropy_equivalent
        φ hd hp hr, AlignmentPaperPeriodicBesov.periodic_besov_theta_two_width_certified
        φ hd hp hr⟩
    · have hstrict : 2 < θ.toReal := by
        apply lt_of_le_of_ne hreal
        intro heq
        apply htwo
        apply (ENNReal.toReal_eq_toReal_iff' htop (by norm_num : (2:ℝ≥0∞) ≠ ⊤)).mp
        simpa using heq.symm
      exact ⟨AlignmentPaperBesovInterpolation.periodicBesov_entropy_equivalent_finite_theta
        φ hd hp hr htop hstrict,
        AlignmentPaperBesovInterpolation.periodicBesov_width_equivalent_finite_theta
        φ hd hp hr htop hstrict⟩

end BrownianSharp.AlignmentPaperPeriodicComplete
