import BrownianSharp.Carl

/-! Refinement of a coarse external cover inside the actual finite-dimensional
range. The coarse centers are first moved into the source set, so no range
membership of the original KGG centers is assumed. -/
noncomputable section
open scoped NNReal ENNReal
namespace BrownianSharp.AlignmentPaperFiniteCoverRefinement
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_internal_cover_of_finite_cover {K C : Set X} {ε : ℝ≥0}
    (hC : C.Finite) (hcover : Metric.IsCover ε K C) :
    ∃ D : Set X, D ⊆ K ∧ D.Finite ∧ D.encard ≤ C.encard ∧
      Metric.IsCover (2 * ε) K D := by
  have hcount : Metric.coveringNumber (2 * ε) K ≤ C.encard :=
    (Metric.coveringNumber_two_mul_le_externalCoveringNumber ε K).trans
      hcover.externalCoveringNumber_le_encard
  obtain ⟨D, hDK, hDfin, hDcover, hDcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber
      (ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hC) hcount)
  exact ⟨D, hDK, hDfin, hDcard.le.trans hcount, hDcover⟩

theorem exists_refined_cover_in_subspace (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    {K C : Set X} {ε : ℝ≥0} {η : ℝ}
    (hKV : K ⊆ V) (hC : C.Finite) (hcover : Metric.IsCover ε K C)
    (hη : 0 < η) :
    ∃ D : Set X, D.Finite ∧ Metric.IsCover (NNReal.mk η hη.le) K D ∧
      D.encard ≤ C.encard *
        ↑(Nat.ceil ((1 + 4 * (ε : ℝ) / η) ^ Module.finrank ℝ V)) := by
  obtain ⟨A, hAK, hAfin, hAcard, hAcover⟩ :=
    exists_internal_cover_of_finite_cover hC hcover
  obtain ⟨piece, hsource, hradius, hcard⟩ :=
    Carl.exists_submodule_ball_piece_general V
      (R := 2 * (ε : ℝ)) (ε := η) (by positivity) hη
  have hsubset : K ⊆ Carl.sumSet A piece.source := by
    intro x hx
    obtain ⟨a, ha, hdist⟩ := hAcover hx
    have hnorm : ‖x - a‖ ≤ 2 * (ε : ℝ) := by
      change edist x a ≤ ((2 * ε : ℝ≥0) : ENNReal) at hdist
      rw [edist_dist] at hdist
      have hreal : dist x a ≤ ((2 * ε : ℝ≥0) : ℝ) := by
        exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg _)).mp
          (by simpa only [ENNReal.ofReal_coe_nnreal] using hdist)
      simpa only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] using hreal
    refine ⟨(a, x - a), ⟨ha, ?_⟩, by dsimp; abel⟩
    rw [hsource]
    refine ⟨⟨x-a, V.sub_mem (hKV hx) (hKV (hAK ha))⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖x - a‖ ≤ 2 * (ε : ℝ)
    exact hnorm
  have hprod := Carl.finite_sumSet_card_le hAfin piece.centers_finite
  refine ⟨Carl.sumSet A piece.centers, hprod.1, ?_, ?_⟩
  · have hc := Carl.isCover_sumSet (Metric.IsCover.rfl (ε := 0) (s := A)) piece.cover
    rw [zero_add, hradius] at hc
    exact hc.anti hsubset
  · apply hprod.2.trans
    apply mul_le_mul hAcard
    · simpa only [show 2 * (2 * (ε : ℝ)) = 4 * (ε : ℝ) by ring] using hcard
    · positivity
    · positivity
end BrownianSharp.AlignmentPaperFiniteCoverRefinement
