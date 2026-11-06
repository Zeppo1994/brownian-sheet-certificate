import BrownianSharp.AlignmentPaperMultivariateFaceInverse
import BrownianSharp.LayerIndex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Actual Young estimates for a single exact-support face at one graded shape.
The only Fourier input is the actual derivative identity for that source face;
the reconstructed output is proved from the finite inverse kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperFaceGradeYoung

open BrownianSharp.AlignmentPaperMultivariateFaceInverse
open BrownianSharp.AlignmentPaperAnchoredLpFacePartition
open BrownianSharp.Torus

private theorem shape_active_scale_sum {d n : ℕ} (J : Finset (Fin d))
    (s : BrownianSharp.Shape d n)
    (hzero : ∀ i, i ∉ J → s.1 i = 0) :
    (∑ i ∈ J, s.1 i) = n := by
  have htotal : (∑ i : Fin d, s.1 i) = n := by
    have hmem := (Finset.mem_finsuppAntidiag.mp s.2).1
    simpa using hmem
  calc
    (∑ i ∈ J, s.1 i) = ∑ i ∈ (Finset.univ : Finset (Fin d)), s.1 i := by
      apply Finset.sum_subset (Finset.subset_univ J)
      intro i hi hnot
      exact hzero i hnot
    _ = n := htotal

private theorem active_inverse_scale_product {d n : ℕ} (J : Finset (Fin d))
    (s : BrownianSharp.Shape d n)
    (hsum : (∑ i ∈ J, s.1 i) = n) :
    (∏ i ∈ J, ((2:ℝ)^(s.1 i))⁻¹) = (2:ℝ)^(-(n:ℝ)) := by
  calc
    (∏ i ∈ J, ((2:ℝ)^(s.1 i))⁻¹) =
        ((2:ℝ) ^ (∑ i ∈ J, s.1 i))⁻¹ := by
          rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    _ = ((2:ℝ) ^ n)⁻¹ := by rw [hsum]
    _ = (2:ℝ)^(-(n:ℝ)) := by
          rw [← Real.rpow_natCast (2:ℝ) n,
            Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)) (n:ℝ)]

private theorem rpow_root_mul_le {A B K p : ℝ}
    (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hAB : A ≤ K ^ p * B) :
    A ^ (1 / p) ≤ K * B ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 ≤ 1 / p := by positivity
  calc
    A ^ (1 / p) ≤ (K ^ p * B) ^ (1 / p) :=
      Real.rpow_le_rpow hA hAB hr
    _ = (K ^ p) ^ (1 / p) * B ^ (1 / p) := by
      rw [Real.mul_rpow (by positivity) hB]
    _ = K * B ^ (1 / p) := by
      rw [← Real.rpow_mul hK p (1 / p)]
      have hpow : p * (1 / p) = 1 := by field_simp
      rw [hpow, Real.rpow_one]

/-- A single actual smooth block on an exact-support face is recovered by its
finite neighboring inverse kernel and obeys the graded Young rate. The constant
is chosen before the dimension, grade, face, and source. -/
theorem exists_faceGradeYoung_Lp_bound {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {d n : ℕ} (J : Finset (Fin d))
      (s : BrownianSharp.Shape d n) (F h : UnitAddTorus (Fin d) → ℂ)
      (hh : Integrable h (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
      (hderiv : ∀ k : Fin d → ℤ, frequencySupport k = J →
        UnitAddTorus.mFourierCoeff h k =
          (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
            UnitAddTorus.mFourierCoeff F k),
      (∫ x : UnitAddTorus (Fin d), ‖faceBlockTarget J s.1 F x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1 / p) ≤
        C ^ d * (2:ℝ)^(-(n:ℝ)) *
          (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1 / p) := by
  obtain ⟨C, hC, hL1⟩ := exists_faceInverseKernel_L1_bound
  refine ⟨C, hC, ?_⟩
  intro d n J s F h hh hderiv
  by_cases hbad : ∃ i, i ∉ J ∧ 0 < s.1 i
  · obtain ⟨i, hi, hsi⟩ := hbad
    have hzero := faceBlockTarget_eq_zero_of_inactive_positive_grade J s.1 F i hi hsi
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hnonneg : 0 ≤ C ^ d * (2:ℝ)^(-(n:ℝ)) *
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1 / p) := by
      positivity
    have houter : (0:ℝ) ^ p⁻¹ = 0 :=
      Real.zero_rpow (ne_of_gt (inv_pos.mpr hp0))
    have htargetNorm :
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockTarget J s.1 F x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1 / p) = 0 := by
      rw [hzero]
      simp [Real.zero_rpow (ne_of_gt hp0), houter]
    rw [htargetNorm]
    exact hnonneg
  · have hzero : ∀ i, i ∉ J → s.1 i = 0 := by
      intro i hi
      by_contra hne
      exact hbad ⟨i, hi, Nat.pos_of_ne_zero hne⟩
    have hsum := shape_active_scale_sum J s hzero
    have hscale := active_inverse_scale_product J s hsum
    let u : C(UnitAddTorus (Fin d), ℂ) :=
      BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s.1)
        (fun k => faceBlockSymbol s.1 k * UnitAddTorus.mFourierCoeff h k)
    have hsource : faceBlockSource s.1 h = fun x => u x := by
      simpa [u] using faceBlockSource_eq_torusFourierPolynomial s.1 hh
    have hrec := faceInverse_reconstructs_actual_faceBlock J s.1 hh hderiv
    have hpoint (x : UnitAddTorus (Fin d)) :
        faceBlockTarget J s.1 F x =
          ∫ y : UnitAddTorus (Fin d), faceInverseKernel J s.1 y * u (x-y)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      calc
        _ = ∫ y : UnitAddTorus (Fin d), faceInverseKernel J s.1 y *
            faceBlockSource s.1 h (x-y)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := (hrec x).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hsource]
    have hmoment :
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockTarget J s.1 F x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
        ∫ x : UnitAddTorus (Fin d),
          ‖∫ y : UnitAddTorus (Fin d), faceInverseKernel J s.1 y * u (x-y)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoint x]
    have hYoung := BrownianSharp.unitAddTorus_complex_convolution_rpow_le
      (faceInverseKernel J s.1) u p hp
    have hkernel := hL1 J s.1
    let K : ℝ := C ^ d * ∏ i ∈ J, ((2:ℝ)^(s.1 i))⁻¹
    have hK : 0 ≤ K := by positivity
    have hsourceNonneg : 0 ≤ ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_nonneg
      intro x
      positivity
    have htargetNonneg : 0 ≤ ∫ x : UnitAddTorus (Fin d),
        ‖faceBlockTarget J s.1 F x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_nonneg
      intro x
      positivity
    have hKpow :
        (∫ y : UnitAddTorus (Fin d), ‖faceInverseKernel J s.1 y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p ≤ K ^ p := by
      dsimp [K]
      exact Real.rpow_le_rpow (integral_nonneg (fun _ => norm_nonneg _)) hkernel
        (by linarith)
    have hmomentBound :
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockTarget J s.1 F x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
        K ^ p * (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
      rw [hmoment]
      exact hYoung.trans (mul_le_mul_of_nonneg_right hKpow hsourceNonneg)
    have hroot := rpow_root_mul_le hp htargetNonneg hsourceNonneg hK hmomentBound
    have hsourceEq :
        (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(congrFun hsource x).symm]
    simpa [K, hscale, hsourceEq, mul_assoc] using hroot

end BrownianSharp.AlignmentPaperFaceGradeYoung

end
