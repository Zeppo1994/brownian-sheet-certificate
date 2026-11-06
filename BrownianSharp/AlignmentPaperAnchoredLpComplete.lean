import BrownianSharp.AlignmentPaperAnchoredLpSeriesClass
import BrownianSharp.AlignmentPaperJointGlobalEntropy
import BrownianSharp.AlignmentPaperAnchoredLpLower

/-! The full finite-p entropy conclusion for the actual anchored integration
image. The source-to-series inclusion and the global covering theorem are
proved independently and then composed contractively. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperAnchoredLpComplete
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpLower
open BrownianSharp.AlignmentPaperAnchoredLpSeriesClass
open BrownianSharp.AlignmentPaperJointGlobalEntropy
open BrownianSharp.AlignmentPaperPeriodic

/-- The upper bound for `1 < p < 2`, on the actual rectangular-integral
image of the Lp unit ball, with constants selected before the entropy index. -/
theorem anchoredIntegrationLp_entropy_upper_lt_two
    {d : ℕ} {p : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (anchoredIntegrationLpImage d p) ≤
        ENNReal.ofReal (C * cmIndexRate d k) := by
  obtain ⟨A,hA,hdom⟩ := exists_anchoredGradeSeries_entropy_domination hd hp hp2
  obtain ⟨C,hC,k₀,hupper⟩ := gradeSeriesClass_entropy_upper hd hp hp2 hA
  refine ⟨C,hC,max 2 k₀,le_max_left _ _,?_⟩
  intro k hk
  have h := (hdom k).trans (hupper k ((le_max_right _ _).trans hk))
  simpa only [cmIndexRate, logarithmicIndexRate, Real.rpow_neg_one, Real.rpow_eq_pow, mul_assoc] using h

/-- Theorem 1.2's entropy equivalence for every finite real exponent p>1.
The strict-index width equivalence remains asserted only in its stated p≥2 range. -/
theorem anchoredIntegrationLp_entropy_equivalent_all_p
    {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 1 < p) :
    twoSidedEntropyRate (anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2) := by
  by_cases hp2 : 2 ≤ p
  · exact anchoredIntegrationLp_entropy_equivalent_ge_two hd p hp2
  · obtain ⟨cl,hcl,nl,hnl,hl⟩ := anchoredIntegrationLp_entropy_lower_all_p hd p hp
    obtain ⟨cu,hcu,nu,hnu,hu⟩ :=
      anchoredIntegrationLp_entropy_upper_lt_two hd hp (lt_of_not_ge hp2)
    refine ⟨cl,cu,hcl,hcu,max nl nu,hnl.trans (le_max_left _ _),?_⟩
    intro k hk
    exact ⟨hl k ((le_max_left _ _).trans hk), hu k ((le_max_right _ _).trans hk)⟩

end BrownianSharp.AlignmentPaperAnchoredLpComplete
