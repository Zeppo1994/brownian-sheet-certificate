import BrownianSharp.BrownianHaarCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic

/-! Restrict the finite index set of an isonormal Gaussian family to any
smaller finite type, without changing its random variables. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentIsonormalReindex

open HaarQuarter

theorem exists_reindexed_isonormal
    {H Ω κ ι : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω κ P)
    (hcard : Fintype.card ι ≤ Fintype.card κ) :
    ∃ W' : IsonormalGaussianFamily H Ω ι P, W'.eval = W.eval := by
  classical
  let e : ι ↪ κ := (Function.Embedding.nonempty_of_card_le hcard).some
  let ext : (ι → H) → (κ → H) := fun v => Function.extend e v 0
  let restrict : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)
  have hext (v : ι → H) (i : ι) : ext v (e i) = v i := by
    exact e.injective.extend_apply v 0 i
  refine ⟨{
    eval := W.eval
    jointlyGaussian := ?_
    measurable_eval := W.measurable_eval
    mean_zero := W.mean_zero
    covariance_eq_inner := W.covariance_eq_inner }, rfl⟩
  intro v
  have h := (W.jointlyGaussian (ext v)).map restrict
  have heq : (fun ω => restrict (fun k => W.eval (ext v k) ω)) =
      (fun ω i => W.eval (v i) ω) := by
    funext ω i
    simp [restrict, hext]
  rw [← heq]
  exact h

end BrownianSharp.AlignmentIsonormalReindex
