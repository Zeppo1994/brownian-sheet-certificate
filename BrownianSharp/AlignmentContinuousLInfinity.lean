import BrownianSharp.AlignmentAmbientWidth
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The genuine isometric embedding of continuous functions into L-infinity
for a full-support finite measure, and its width comparison. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentAmbientWidth
universe u
variable {α : Type u} [TopologicalSpace α] [CompactSpace α]
  [MeasurableSpace α] [BorelSpace α] (μ : Measure α)
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

theorem continuous_toLInfinity_norm (f : C(α, ℝ)) :
    ‖ContinuousMap.toLp (E:=ℝ) ⊤ μ ℝ f‖ = ‖f‖ := by
  let F : Lp ℝ ⊤ μ := ContinuousMap.toLp ⊤ μ ℝ f
  have hupper : ‖F‖ ≤ ‖f‖ := by
    have hop : ‖ContinuousMap.toLp (E:=ℝ) ⊤ μ ℝ‖ ≤ 1 := by
      simpa using (ContinuousMap.toLp_norm_le (E:=ℝ) (p:=⊤) (𝕜:=ℝ) μ)
    exact ((ContinuousMap.toLp ⊤ μ ℝ).le_opNorm f).trans
      (by simpa using mul_le_mul_of_nonneg_right hop (norm_nonneg f))
  have hbound : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable F)]
    exact ae_le_eLpNormEssSup
  have hfae : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖F‖ := by
    filter_upwards [hbound, ContinuousMap.coeFn_toLp (p:=⊤) (𝕜:=ℝ) (μ:=μ) f] with x hx heq
    rw [heq] at hx
    exact enorm_le_iff_norm_le.mp hx
  have hclosed : IsClosed {x : α | ‖f x‖ ≤ ‖F‖} :=
    isClosed_le f.continuous.norm continuous_const
  have hset : {x : α | ‖f x‖ ≤ ‖F‖} = Set.univ :=
    hclosed.ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr hfae)
  have hlower : ‖f‖ ≤ ‖F‖ := by
    apply (ContinuousMap.norm_le f (norm_nonneg F)).2
    intro x
    have hx : x ∈ {x : α | ‖f x‖ ≤ ‖F‖} := by rw [hset]; trivial
    exact hx
  exact le_antisymm hupper hlower

/-- Unlike the finite-p map, the top-exponent inclusion is isometric under
full support. The target uses actual a.e. equivalence classes. -/
def continuousToLInfinity : C(α, ℝ) →ₗᵢ[ℝ] Lp ℝ ⊤ μ where
  toLinearMap := (ContinuousMap.toLp ⊤ μ ℝ).toLinearMap
  norm_map' := continuous_toLInfinity_norm μ

theorem continuous_width_ge_LInfinity_width
    (K : Set C(α, ℝ)) (m : ℕ) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (continuousToLInfinity μ '' K) m ≤
    HaarQuarter.TheoremD.Width.kolmogorovWidth K m :=
  kolmogorovWidth_image_le (continuousToLInfinity μ) K m

/-- The manuscript's smoothing argument, now specialized to the actual
continuous-function and L-infinity spaces. -/
theorem continuous_width_eq_LInfinity_width_of_smoothing
    (K : Set C(α, ℝ))
    (hsmooth : ∀ δ : ℝ, 0 < δ →
      ∃ S : Lp ℝ ⊤ μ →L[ℝ] C(α, ℝ),
        (∀ g, ‖S g‖ ≤ ‖g‖) ∧
        ∀ f ∈ K, ‖f-S (continuousToLInfinity μ f)‖ ≤ δ)
    (m : ℕ) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth K m =
    HaarQuarter.TheoremD.Width.kolmogorovWidth
      (continuousToLInfinity μ '' K) m :=
  kolmogorovWidth_eq_of_contractile_smoothing (continuousToLInfinity μ) K hsmooth m

end BrownianSharp.AlignmentAmbientWidth
