import BrownianSharp.BrownianSheetWhiteNoise

open MeasureTheory
namespace HaarQuarter

/-- The Brownian sheet's actual parameter domain. -/
abbrev BrownianCubeAnchor (d : ℕ) :=
  {x : Fin d → ℝ // ∀ i, x i ∈ Set.Icc (0:ℝ) 1}

/-- The integrand Hilbert space supplied by the cube-valued sheet, without
assuming an isonormal extension to all of L² over the ambient space. -/
noncomputable def brownianCubeBoxSpan (d : ℕ) :
    Submodule ℝ (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
  (Submodule.span ℝ (Set.range (fun x : BrownianCubeAnchor d =>
    brownianSheetBoxIndicatorLp x.val))).topologicalClosure

theorem brownianCubeBoxIndicator_mem {d : ℕ} (x : BrownianCubeAnchor d) :
    brownianSheetBoxIndicatorLp x.val ∈ brownianCubeBoxSpan d :=
  (Submodule.span ℝ (Set.range (fun x : BrownianCubeAnchor d =>
    brownianSheetBoxIndicatorLp x.val))).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self x))

/-- The canonical embedding preserves all existing deterministic L² inner
products of the tent and critical-vector calculations. -/
noncomputable def brownianCubeSpanEmbedding (d : ℕ) :
    brownianCubeBoxSpan d →ₗᵢ[ℝ]
      Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) where
  toLinearMap := (brownianCubeBoxSpan d).subtype
  norm_map' _ := rfl

/-- Ambient parameter version, zero outside the sheet's cube. -/
noncomputable def brownianCubeBoxVector {d : ℕ} (x : Fin d → ℝ) :
    brownianCubeBoxSpan d := by
  classical
  exact if hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1 then
    ⟨brownianSheetBoxIndicatorLp x, brownianCubeBoxIndicator_mem ⟨x,hx⟩⟩ else 0

theorem brownianCubeBoxVector_coe {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) :
    brownianCubeSpanEmbedding d (brownianCubeBoxVector x) =
      brownianSheetBoxIndicatorLp x := by
  simp only [brownianCubeBoxVector, dif_pos hx]
  rfl

end HaarQuarter
