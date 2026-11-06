import BrownianSharp.AlignmentPaperJointGlobalTail
import BrownianSharp.AlignmentPaperJointGlobalRankProfile

/-! A uniform `2^-N sqrt(N+1)` bound for the terminal grade-series tail. -/

noncomputable section

namespace BrownianSharp.AlignmentPaperJointGlobalTailRadius

open BrownianSharp.AlignmentPaperJointGlobalTail
open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGlobalCover

theorem exists_windowTail_radius_envelope {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (∑' n : ℕ, gradeSeriesNormEnvelope d p A
        (n + (N+1+highProfileWindow p N))) ≤
        K*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ) := by
  obtain ⟨K,hK,hTail⟩ := gradeSeries_envelope_shift_tail_bound hd hp hA
  let α : ℝ := 1-1/p
  let δ : ℝ := α*Real.log 2
  have hp0 : 0 < p := by linarith
  have hα : 0 < α := by
    dsimp [α]
    have : 1/p < 1 := (div_lt_one hp0).2 (by linarith)
    linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos hα (Real.log_pos (by norm_num))
  refine ⟨K,hK,?_⟩
  intro N
  have hW : 4*p*(N:ℝ)/(p-1) ≤ (highProfileWindow p N:ℝ) := by
    have hc := Nat.le_ceil (4*p*(N:ℝ)/(p-1))
    simpa [highProfileWindow, div_eq_mul_inv, mul_assoc] using hc
  have hM : 2*(N:ℝ)*Real.log 2 ≤
      δ*((N+1+highProfileWindow p N:ℝ))/2 := by
    have hratio : 4*p/(p-1) = 4/α := by
      dsimp [α]
      field_simp
    have hW' : 4/α*(N:ℝ) ≤ (highProfileWindow p N:ℝ) := by
      rw [← hratio]
      convert hW using 1 <;> ring
    have hfactor : δ*(highProfileWindow p N:ℝ)/2 ≤
        δ*((N+1+highProfileWindow p N:ℝ))/2 := by
      have hWle : (highProfileWindow p N:ℝ) ≤
          (N+1+highProfileWindow p N:ℝ) := by
        exact_mod_cast (Nat.le_add_left (highProfileWindow p N) (N+1))
      have hmulW := mul_le_mul_of_nonneg_left hWle hδ.le
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hW' hδ.le
    have hcancel : δ*(4/α*(N:ℝ)) = 4*(N:ℝ)*Real.log 2 := by
      dsimp [δ,α]
      field_simp [ne_of_gt (show 0 < p-1 by linarith)]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hfactor, hmul, hcancel, hlog]
  have hexp : Real.exp (-δ*((N+1+highProfileWindow p N:ℝ))/2) ≤
      (2:ℝ)^(-(N:ℝ)) := by
    have harg : -δ*((N+1+highProfileWindow p N:ℝ))/2 ≤
        -(N:ℝ)*Real.log 2 := by
      have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
      have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      nlinarith [hM, hN, hlog]
    calc
      Real.exp (-δ*((N+1+highProfileWindow p N:ℝ))/2) ≤
          Real.exp (-(N:ℝ)*Real.log 2) := Real.exp_le_exp.mpr harg
      _ = (2:ℝ)^(-(N:ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
        congr 1
        ring
  calc
    _ ≤ K*Real.exp (-δ*((N+1+highProfileWindow p N:ℝ))/2) := by
      simpa [δ,α] using hTail (N+1+highProfileWindow p N)
    _ ≤ K*(2:ℝ)^(-(N:ℝ)) := mul_le_mul_of_nonneg_left hexp hK.le
    _ ≤ K*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ) := by
      have hsqrt : (1:ℝ) ≤ Real.sqrt (N+1:ℝ) := by
        rw [Real.le_sqrt (by positivity)]
        norm_num
        positivity
      nlinarith [mul_nonneg (show 0 ≤ K*(2:ℝ)^(-(N:ℝ)) by positivity)
        (sub_nonneg.mpr hsqrt)]

end BrownianSharp.AlignmentPaperJointGlobalTailRadius
