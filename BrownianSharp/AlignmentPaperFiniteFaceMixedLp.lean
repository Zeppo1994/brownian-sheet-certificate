import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A finite-face triangle inequality in the mixed `ℓ²(Lᵖ)` norm.

This is the order needed when each face has its own scalar `Lᵖ` estimate:
first sum faces in the Banach space `ℓ²(S; Lᵖ(X))`, then identify its norm
with the displayed scalar integral formula.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperFiniteFaceMixedLp

private theorem lp_toLp_norm_eq_integral_rpow_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ} (hp : 0 < p) {f : X → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ‖hf.toLp f‖ = (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  rw [Lp.norm_toLp f hf, hf.eLpNorm_eq_integral_rpow_norm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal]
  · simp [ENNReal.toReal_ofReal hp.le]
  · positivity

/-- The finite-face triangle inequality in the mixed `ℓ²(Lᵖ)` norm. -/
theorem finite_face_mixed_lp_triangle
    {X J S : Type*} [MeasurableSpace X] [Fintype J] [DecidableEq J]
    [Fintype S] [DecidableEq S] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (hp1 : 1 ≤ p)
    [IsFiniteMeasure μ]
    (f : J → S → X → ℂ)
    (hf : ∀ j s, MemLp (f j s) (ENNReal.ofReal p) μ) :
    (∑ s : S, (∫ x, ‖∑ j, f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) ≤
      ∑ j : J, (∑ s : S,
        (∫ x, ‖f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) := by
  classical
  let e : ℝ≥0∞ := ENNReal.ofReal p
  haveI : Fact (1 ≤ e) := ⟨by
    dsimp [e]
    simpa using ENNReal.ofReal_le_ofReal hp1⟩
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let faceLp (j : J) (s : S) : Lp ℂ e μ := (hf j s).toLp (f j s)
  let faceVec (j : J) : PiLp 2 (fun _ : S => Lp ℂ e μ) :=
    WithLp.toLp 2 (fun s => faceLp j s)
  let sumVec : PiLp 2 (fun _ : S => Lp ℂ e μ) := ∑ j, faceVec j
  let sumMem (s : S) : MemLp (fun x => ∑ j : J, f j s x) e μ :=
    by
      convert memLp_finsetSum (s := Finset.univ)
        (f := fun j x => f j s x) (fun j hj => hf j s) using 1
  let sumLp (s : S) : Lp ℂ e μ := (sumMem s).toLp (fun x => ∑ j, f j s x)
  have hsum_coord (s : S) : sumVec s = ∑ j : J, faceLp j s := by
    simp [sumVec, faceVec]
  have hsum_lp (s : S) : sumLp s = ∑ j : J, faceLp j s := by
    apply Lp.ext
    filter_upwards [(sumMem s).coeFn_toLp,
      Lp.coeFn_finsetSum Finset.univ (fun j => faceLp j s),
      ae_all_iff.mpr (fun j => (hf j s).coeFn_toLp)] with x hrep hsum hj
    rw [hrep, hsum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj'
    simpa [faceLp] using (hj j).symm
  have hface_norm (j : J) :
      ‖faceVec j‖ = (∑ s : S,
        (∫ x, ‖f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) := by
    rw [PiLp.norm_eq_sum (by norm_num) (faceVec j)]
    simp_rw [ENNReal.toReal_ofNat]
    have hcoord (s : S) :
        ‖faceVec j s‖ = (∫ x, ‖f j s x‖ ^ p ∂μ) ^ (1 / p) := by
      rw [show faceVec j s = faceLp j s by simp [faceVec]]
      exact lp_toLp_norm_eq_integral_rpow_norm hp (hf j s)
    simp_rw [hcoord]
    apply congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ))
    apply Finset.sum_congr rfl
    intro s hs
    have hI : 0 ≤ ∫ x, ‖f j s x‖ ^ p ∂μ := integral_nonneg fun x => by positivity
    rw [← Real.rpow_mul hI (1 / p) 2]
    congr 1
    ring
  have hsum_norm :
      ‖sumVec‖ = (∑ s : S,
        (∫ x, ‖∑ j : J, f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) := by
    rw [PiLp.norm_eq_sum (by norm_num) sumVec]
    simp_rw [ENNReal.toReal_ofNat]
    have hcoord (s : S) :
        ‖sumVec s‖ =
          (∫ x, ‖∑ j : J, f j s x‖ ^ p ∂μ) ^ (1 / p) := by
      rw [hsum_coord s, ← hsum_lp s]
      exact lp_toLp_norm_eq_integral_rpow_norm hp (sumMem s)
    simp_rw [hcoord]
    apply congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ))
    apply Finset.sum_congr rfl
    intro s hs
    have hI : 0 ≤ ∫ x, ‖∑ j : J, f j s x‖ ^ p ∂μ := integral_nonneg fun x => by positivity
    rw [← Real.rpow_mul hI (1 / p) 2]
    congr 1
    ring
  calc
    (∑ s : S, (∫ x, ‖∑ j, f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ)
        = ‖sumVec‖ := hsum_norm.symm
    _ ≤ ∑ j : J, ‖faceVec j‖ := norm_sum_le _ _
    _ = ∑ j : J, (∑ s : S,
        (∫ x, ‖f j s x‖ ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ) := by
          simp_rw [hface_norm]

end BrownianSharp.AlignmentPaperFiniteFaceMixedLp
