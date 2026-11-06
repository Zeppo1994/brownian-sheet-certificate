import BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget
import BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership
import BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction

/-! Unconditional inclusion of the actual anchored image in one fixed decoded
series class, followed by contractive transfer of its covering numbers. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperAnchoredLpSeriesClass
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget
open BrownianSharp.AlignmentPaperAnchoredLpSeriesMembership
open BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AtomicBlockKernelL2

/-- One series-class radius works for every density in the actual Lp unit
ball. The grade estimate is proved internally, not a hypothesis. -/
theorem exists_uniform_anchoredGradeSeries_membership {d : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) :
    ∃ A : ℝ, 0 < A ∧
      ∀ g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d), ‖g‖ ≤ 1 →
        complexifyContinuous (periodicFoldExtension (integrationPath p hp g)) ∈
          GradeSeriesClass d p A := by
  obtain ⟨D,hD,hgrade⟩ := exists_actualGradeLpCost_bound (d := d) hp hp2
  obtain ⟨A,hA,hmember⟩ :=
    integrationPath_mem_GradeSeriesClass_of_grade_cost hd hp hp2 D hD
  exact ⟨A,hA,fun g hg => hmember g (hgrade g hg)⟩

/-- The actual anchored image has no larger entropy than one fixed decoded
series class. The source radius is chosen before every entropy index. -/
theorem exists_anchoredGradeSeries_entropy_domination {d : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
      HaarQuarter.TheoremD.entropyNumber k (anchoredIntegrationLpImage d p) ≤
        HaarQuarter.TheoremD.entropyNumber k (GradeSeriesClass d p A) := by
  obtain ⟨A,hA,hmember⟩ := exists_uniform_anchoredGradeSeries_membership hd hp hp2
  refine ⟨A,hA,?_⟩
  intro k
  exact anchoredImage_entropy_le_of_fold_membership hp (GradeSeriesClass d p A) hmember k

end BrownianSharp.AlignmentPaperAnchoredLpSeriesClass
