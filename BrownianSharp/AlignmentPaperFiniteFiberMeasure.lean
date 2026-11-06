import BrownianSharp.AlignmentPaperFiniteFiber
import BrownianSharp.AlignmentPaperQuantization

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperFiniteFiberMeasure
open AlignmentPaperFiniteFiber

/-- Split the mass of a finite target fiber equally among all sample labels
with that target value. Duplicate sample points are handled explicitly. -/
theorem lintegral_inverse_fiber_partition
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (γ : Measure Z) {m : ℕ} (x : Fin m → X) (p : Z → X)
    (hp : Measurable p) (hsupport : ∀ᵐ z ∂γ, p z ∈ Set.range x)
    (f : Z → ℝ≥0∞) (hf : Measurable f) :
    ∑ i : Fin m, (multiplicity x (x i) : ℝ≥0∞)⁻¹ *
      (∫⁻ z in {z | p z=x i}, f z ∂γ) = ∫⁻ z, f z ∂γ := by
  classical
  let w : Fin m → ℝ≥0∞ := fun i => (multiplicity x (x i) : ℝ≥0∞)⁻¹
  let g : Fin m → Z → ℝ≥0∞ := fun i z => if p z=x i then w i*f z else 0
  have hS (i : Fin m) : MeasurableSet {z | p z=x i} := by
    change MeasurableSet (p ⁻¹' {x i})
    exact hp (measurableSet_singleton _)
  have hg (i : Fin m) : Measurable (g i) :=
    (measurable_const.mul hf).ite (hS i) measurable_const
  have he (i : Fin m) : w i*(∫⁻ z in {z | p z=x i}, f z ∂γ)=
      ∫⁻ z, g i z ∂γ := by
    rw [←lintegral_const_mul (w i) hf]
    rw [←lintegral_indicator (hS i)]
    apply lintegral_congr
    intro z
    simp [g,Set.indicator_apply]
  calc
    _ = ∑ i : Fin m, ∫⁻ z, g i z ∂γ := Finset.sum_congr rfl (fun i _ => he i)
    _ = ∫⁻ z, ∑ i : Fin m, g i z ∂γ :=
      (lintegral_finsetSum Finset.univ (fun i _ => hg i)).symm
    _ = ∫⁻ z, f z ∂γ := by
      apply lintegral_congr_ae
      filter_upwards [hsupport] with z hz
      have h := sum_inverse_multiplicity x (p z) hz
      calc
        ∑ i : Fin m, g i z =
            (∑ i : Fin m, if p z=x i then w i else 0)*f z := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [g]
          split_ifs <;> simp
        _ = f z := by rw [show (∑ i : Fin m, if p z=x i then w i else 0)=1 from h,one_mul]

end BrownianSharp.AlignmentPaperFiniteFiberMeasure
