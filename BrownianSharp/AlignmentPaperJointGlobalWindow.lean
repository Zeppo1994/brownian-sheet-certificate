import BrownianSharp.AlignmentPaperJointGlobalTail

/-! Finite-window entropy assembly for the actual decoded grade-series class. -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace BrownianSharp.AlignmentPaperJointGlobalWindow

open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalSeries
open BrownianSharp.AlignmentPaperJointGlobalTail
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.Torus

noncomputable def gradeSeriesTailPiece {d : ℕ} (T : ℝ) (hT : 0 ≤ T) :
    Carl.CoverPiece C(UnitAddTorus (Fin d), ℂ) :=
  ⟨Metric.closedBall (0 : C(UnitAddTorus (Fin d), ℂ)) T, {0}, Real.toNNReal T, by
    intro x hx
    refine ⟨0, by simp, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [edist_dist, dist_zero_right]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal T hT]
    apply (ENNReal.ofReal_le_ofReal_iff hT).2
    simpa [Metric.mem_closedBall, dist_zero_right] using hx, by simp⟩

theorem gradeSeriesWindow_centerBudget
    {d M : ℕ} {p A T : ℝ} (hT : 0 ≤ T)
    (C : Fin M → Set C(UnitAddTorus (Fin d), ℂ))
    (r : Fin M → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i)
      (decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) (C i))
    (hfinite : ∀ i, (C i).Finite) (b : Fin M → ℕ)
    (hcard : ∀ i, (C i).encard ≤ ((2 ^ (b i) : ℕ) : ℕ∞)) :
    (((indexedGradeCoverPieces
      (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite ++
      [gradeSeriesTailPiece T hT]).map
      (fun z : Carl.CoverPiece C(UnitAddTorus (Fin d), ℂ) => z.centers.encard)).prod) ≤
      ((2 ^ (∑ i : Fin M, b i) : ℕ) : ℕ∞) := by
  have hgrade :
      (((indexedGradeCoverPieces
        (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
          (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite).map
        (fun z : Carl.CoverPiece C(UnitAddTorus (Fin d), ℂ) => z.centers.encard)).prod) ≤
        ((2 ^ (∑ i : Fin M, b i) : ℕ) : ℕ∞) := by
    simp only [indexedGradeCoverPieces, List.map_ofFn, List.prod_ofFn]
    calc
      (∏ i : Fin M, (C i).encard) ≤
          ∏ i : Fin M, ((2 ^ (b i) : ℕ) : ℕ∞) := by
            apply Finset.prod_le_prod
            intro i hi
            exact hcard i
      _ = ((∏ i : Fin M, 2 ^ (b i) : ℕ) : ℕ∞) := by simp
      _ = ((2 ^ (∑ i : Fin M, b i) : ℕ) : ℕ∞) := by
            congr 1
            exact Finset.prod_pow_eq_pow_sum Finset.univ b 2
  rw [List.map_append, List.prod_append]
  simpa [gradeSeriesTailPiece, Set.encard_singleton] using hgrade

theorem gradeSeriesClass_entropy_le_of_window_covers
    {d M k : ℕ} {p A T : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) (hT : 0 ≤ T)
    (C : Fin M → Set C(UnitAddTorus (Fin d), ℂ))
    (r : Fin M → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i)
      (decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) (C i))
    (hfinite : ∀ i, (C i).Finite)
    (hbudget :
      ((indexedGradeCoverPieces
        (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
          (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite ++
        [gradeSeriesTailPiece T hT]).map
          (fun z : Carl.CoverPiece C(UnitAddTorus (Fin d), ℂ) => z.centers.encard)).prod ≤
        ((2^(k-1):ℕ):ℕ∞))
    (hTail : (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M)) ≤ T) :
    HaarQuarter.TheoremD.entropyNumber k (GradeSeriesClass d p A) ≤
      Carl.sumRadii (indexedGradeCoverPieces
        (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
          (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite ++
        [gradeSeriesTailPiece T hT]) := by
  apply entropyNumber_le_of_finite_grade_window (GradeSeriesClass d p A)
    (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
      (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite
    (gradeSeriesTailPiece T hT)
    k hbudget ?_
  · intro f hf
    obtain ⟨v, t, hv, htnorm, heq⟩ :=
      gradeSeriesClass_window_decomposition hd hp hp2 hA hf M
    have htm : t ∈ Metric.closedBall (0 : C(UnitAddTorus (Fin d), ℂ)) T := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact htnorm.trans hTail
    exact ⟨v, t, hv, htm, heq⟩

theorem gradeSeriesClass_entropy_le_of_window_bits
    {d M k : ℕ} {p A T : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) (hT : 0 ≤ T)
    (C : Fin M → Set C(UnitAddTorus (Fin d), ℂ))
    (r : Fin M → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i)
      (decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) (C i))
    (hfinite : ∀ i, (C i).Finite) (b : Fin M → ℕ)
    (hcard : ∀ i, (C i).encard ≤ ((2 ^ (b i) : ℕ) : ℕ∞))
    (hbits : (∑ i : Fin M, b i) + 1 ≤ k)
    (hTail : (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n + M)) ≤ T) :
    HaarQuarter.TheoremD.entropyNumber k (GradeSeriesClass d p A) ≤
      Carl.sumRadii (indexedGradeCoverPieces
        (fun i => decodedJointLpFeatureImage (d := d) (n := i.val) p
          (gradeSeriesSourceRadius d p A i.val)) C r hcover hfinite ++
        [gradeSeriesTailPiece T hT]) := by
  have hindex : ∑ i : Fin M, b i ≤ k - 1 := by omega
  have hpow : (2 ^ (∑ i : Fin M, b i) : ℕ) ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hindex
  have hbudget := gradeSeriesWindow_centerBudget hT C r hcover hfinite b hcard
  apply gradeSeriesClass_entropy_le_of_window_covers hd hp hp2 hA hT C r
    hcover hfinite ?_ hTail
  exact hbudget.trans (by exact_mod_cast hpow)

end BrownianSharp.AlignmentPaperJointGlobalWindow
