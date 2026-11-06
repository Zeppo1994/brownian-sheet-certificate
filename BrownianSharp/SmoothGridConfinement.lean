import BrownianSharp.SmoothPeriodicConditional
import BrownianSharp.GaussianUniformEvent

/-! Finite good-grid confinement, in the precise form required by Anderson
comparison for every translated periodic path ball. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def smoothGoodUniformEvent (d n : ℕ) (ε : ℝ) : Set (LayerIndex d n → ℝ) :=
  {x | ∀ q : SmoothGoodGrid d n,
    |∑ a, smoothLayerAtom smoothAtom q.val a * x a| ≤ ε}

theorem smoothGoodUniformEvent_mass_lt_one {d n : ℕ} (hd : 0 < d) (ε : ℝ) :
    (productStandardGaussian (LayerIndex d n)).real (smoothGoodUniformEvent d n ε) < 1 := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  have hnz : ∃ q : SmoothGoodGrid d n, ∃ a, smoothLayerAtom smoothAtom q.val a ≠ 0 := by
    by_contra hn
    push_neg at hn
    let q : SmoothGoodGrid d n := Classical.choice inferInstance
    have hv := smoothGoodGrid_variance_pos hd q
    simp only [smoothLayerVariance, hn q, zero_pow (by norm_num : (2:ℕ)≠0), Finset.sum_const_zero] at hv
    exact (lt_irrefl 0 hv)
  exact gaussian_uniform_event_mass_lt_one _ hnz ε

end BrownianSharp
