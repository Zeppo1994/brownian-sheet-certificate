import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.SharpCertified
import BrownianSharp.CarlRateExtraction
import BrownianSharp.ExtendedStatements

/-! Conditional two-sided width rate for the actual restricted-cube
Cameron--Martin image. The only unproved analytic premise is the sharp
DKLL-scale width upper bound; the lower bound uses the certified finite
Gaussian confinement and Carl's multiscale extraction. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp

/-- A sharp width upper estimate implies the matching lower estimate for the
actual `KdUnitCube`; the Gaussian Ehrhard input is supplied by the checked
certificate. -/
theorem cameronMartin_width_two_sided_of_sharp_upper
    {d : ℕ} (hd : 2 ≤ d) (C : ℝ) (hC : 0 < C) (m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (CameronMartin.KdUnitCube d) k ≤ ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ∧
      HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ≤
        ENNReal.ofReal (C * cmIndexRate d k) := by
  obtain ⟨c, hc, k₁, hwidthLower⟩ :=
    CarlRateExtraction.KdUnitCube_width_lower_of_productGaussianEhrhard_and_sharp_upper
      productGaussianEhrhard_certified hd C hC m₀ hm₀ hupper
  refine ⟨c, hc, max m₀ k₁, le_trans hm₀ (le_max_left _ _), ?_⟩
  intro k hk
  constructor
  · exact hwidthLower k (le_trans (le_max_right _ _) hk)
  · exact hupper k (le_trans (le_max_left _ _) hk)

/-- The actual entropy lower rate is unconditional; this bundled interface
adds it to the width conclusion under only the sharp width upper premise. -/
theorem cameronMartin_width_and_entropy_lower_of_sharp_upper
    {d : ℕ} (hd : 2 ≤ d) (C : ℝ) (hC : 0 < C) (m₀ : ℕ) (hm₀ : 2 ≤ m₀)
    (hupper : ∀ k : ℕ, m₀ ≤ k →
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (CameronMartin.KdUnitCube d) k ≤ ENNReal.ofReal (C * cmIndexRate d k)) :
    ∃ cE cW : ℝ, 0 < cE ∧ 0 < cW ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      (∀ k : ℕ, 2 ≤ k → ENNReal.ofReal (cE * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d)) ∧
      (∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (cW * cmIndexRate d k) ≤
          HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ∧
        HaarQuarter.TheoremD.Width.kolmogorovWidth (CameronMartin.KdUnitCube d) k ≤
          ENNReal.ofReal (C * cmIndexRate d k)) := by
  obtain ⟨cW, hcw, k₀, hk₀, hwidth⟩ :=
    cameronMartin_width_two_sided_of_sharp_upper hd C hC m₀ hm₀ hupper
  obtain ⟨cE, hce, hentropy⟩ :=
    cameronMartinEntropyLower_certified hd
  exact ⟨cE, cW, hce, hcw, k₀, hk₀, hentropy, hwidth⟩

end BrownianSharp
