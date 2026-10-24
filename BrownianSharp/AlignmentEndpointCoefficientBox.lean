import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Tactic

/-! Product mass of the coordinatewise coefficient box used by the periodic
endpoint route.  The scalar Gaussian tail estimate is intentionally isolated
as a one-dimensional premise; the finite-dimensional independence/product
step is proved here.
-/

open MeasureTheory
open scoped ENNReal

namespace BrownianSharp

/-- The deterministic box in which every coefficient has absolute value at
most `M`. -/
def coefficientBox {ι : Type*} (M : ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-M) M}

theorem productMeasure_coefficientBox_lower
    {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    (hμ : ∀ i, SigmaFinite (μ i)) (M : ℝ)
    (q : ℝ≥0∞) (hcoord : ∀ i, q ≤ μ i (Set.Icc (-M) M)) :
    q ^ Fintype.card ι ≤ (Measure.pi μ) (coefficientBox M) := by
  classical
  letI : ∀ i, SigmaFinite (μ i) := hμ
  rw [show coefficientBox M = Set.univ.pi (fun _ : ι => Set.Icc (-M) M) by
    ext x
    simp [coefficientBox, Set.mem_Icc, Pi.le_def, forall_and]]
  rw [Measure.pi_pi]
  calc
    q ^ Fintype.card ι = ∏ _i : ι, q := by simp
    _ ≤ ∏ i : ι, μ i (Set.Icc (-M) M) := by
      exact Finset.prod_le_prod (fun i _ => hcoord i)
    _ = _ := rfl

/-- Exponential form of the product-box estimate.  The scalar bound
`exp(-b/4) ≤ μ_i([-M,M])` is to be supplied by the standard Gaussian tail
calculation, while the exponent scales with the full coefficient dimension. -/
theorem productMeasure_coefficientBox_exp_lower
    {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    (hμ : ∀ i, SigmaFinite (μ i)) (M b : ℝ)
    (_hb : 0 < b)
    (hcoord : ∀ i, ENNReal.ofReal (Real.exp (-b/4)) ≤
      μ i (Set.Icc (-M) M)) :
    ENNReal.ofReal (Real.exp (-b * (Fintype.card ι : ℝ) / 4)) ≤
      (Measure.pi μ) (coefficientBox M) := by
  have hbox := productMeasure_coefficientBox_lower μ hμ M
    (ENNReal.ofReal (Real.exp (-b/4))) hcoord
  have hmul : (ENNReal.ofReal (Real.exp (-b/4))) ^ Fintype.card ι =
      ENNReal.ofReal (Real.exp (-b * (Fintype.card ι : ℝ) / 4)) := by
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ Real.exp (-b/4))]
    rw [← Real.rpow_natCast]
    rw [← Real.exp_mul]
    congr 1
    push_cast
    ring
  rwa [hmul] at hbox

end BrownianSharp
