import BrownianSharp.CovarianceSpanIsometry
import BrownianSharp.AlignmentFractionalSheetRKHS

/-! Equal feature Gram kernels give the same image of the Hilbert unit ball.
The transfer is constructed through orthogonal projection onto the closed
feature span and the canonical Gram isometry. -/
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentFeatureGramTransfer
open HaarQuarter AlignmentFractionalSheetRKHS

theorem exists_source_of_equal_gram
    {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : ι → H) (w : ι → E)
    (hGram : ∀ i j, ⟪w i,w j⟫ = ⟪v i,v j⟫) (g : H) :
    ∃ g' : E, ‖g'‖ ≤ ‖g‖ ∧ ∀ i, ⟪w i,g'⟫ = ⟪v i,g⟫ := by
  let S := (Submodule.span ℝ (Set.range v)).topologicalClosure
  obtain ⟨T,hT⟩ := exists_closedSpan_isometry_of_gram v w hGram
  let pg : S := S.orthogonalProjectionOnto g
  refine ⟨T pg,?_,?_⟩
  · rw [T.norm_map]
    exact S.norm_orthogonalProjectionOnto_apply_le g
  · intro i
    let vi : S := ⟨v i, (Submodule.span ℝ (Set.range v)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self i))⟩
    have ht : T vi = w i := hT i
    rw [← ht, T.inner_map_map]
    exact S.inner_orthogonalProjectionOnto_eq_of_mem_left vi g

theorem feature_ball_eq_of_gram
    {X H E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : C(X,H)) (w : C(X,E))
    (hGram : ∀ x y, ⟪w x,w y⟫ = ⟪v x,v y⟫) :
    featureOperator v '' Metric.closedBall (0:H) 1 =
      featureOperator w '' Metric.closedBall (0:E) 1 := by
  apply Set.Subset.antisymm
  · rintro f ⟨g,hg,rfl⟩
    obtain ⟨g',hgn,heq⟩ := exists_source_of_equal_gram v w hGram g
    refine ⟨g',?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using
        hgn.trans (show ‖g‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hg)
    · ext x
      exact heq x
  · rintro f ⟨g,hg,rfl⟩
    obtain ⟨g',hgn,heq⟩ := exists_source_of_equal_gram w v (fun x y => (hGram x y).symm) g
    refine ⟨g',?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using
        hgn.trans (show ‖g‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hg)
    · ext x
      exact heq x

end BrownianSharp.AlignmentFeatureGramTransfer
