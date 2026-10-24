import BrownianSharp.BrownianCubeSpan
import BrownianSharp.CovarianceSpanIsometry

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace HaarQuarter

/-- The sheet covariance constructs an actual isometry on the closed span
of cube indicators, with the coordinate classes recovered exactly. -/
theorem brownianSheet_covariance_isometry
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianCubeAnchor d → Ω → ℝ)
    (hB : ∀ x, MemLp (B x) 2 P)
    (hcenter : ∀ x, ∫ ω, B x ω ∂P = 0)
    (hcov : ∀ x y, cov[B x, B y; P] = ∏ i, min (x.val i) (y.val i)) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ x : BrownianCubeAnchor d,
        T ⟨brownianSheetBoxIndicatorLp x.val, brownianCubeBoxIndicator_mem x⟩ =
          (hB x).toLp (B x) := by
  classical
  let v := fun x : BrownianCubeAnchor d => brownianSheetBoxIndicatorLp x.val
  let w := fun x : BrownianCubeAnchor d => (hB x).toLp (B x)
  have hGram (x y : BrownianCubeAnchor d) : ⟪w x,w y⟫ = ⟪v x,v y⟫ := by
    rw [L2.inner_def]
    calc
      (∫ ω, ⟪w x ω,w y ω⟫ ∂P) = ∫ ω, B x ω * B y ω ∂P := by
        apply integral_congr_ae
        filter_upwards [(hB x).coeFn_toLp, (hB y).coeFn_toLp] with ω hx hy
        simp [w, hx, hy, mul_comm]
      _ = cov[B x, B y; P] := by
        rw [covariance_eq_sub (hB x) (hB y), hcenter x, hcenter y]
        simp
      _ = ∏ i, min (x.val i) (y.val i) := hcov x y
      _ = ⟪v x,v y⟫ := by
        dsimp [v]
        exact (brownianSheetBoxIndicatorLp_inner x.val y.val
          (fun i => (x.property i).1) (fun i => (y.property i).1)).symm
  obtain ⟨T,hT⟩ := exists_closedSpan_isometry_of_gram v w hGram
  exact ⟨T,hT⟩

end HaarQuarter
