import BrownianSharp.AlignmentPaperScalarKernelDecay
import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import BrownianSharp.ScalarKernelBudget
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperSmoothKernelDecay

open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.ScalarKernelL1
open HaarQuarter.TheoremD.FejerFourier
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

private theorem profile_sample_kernel_decay
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hSupport : ∀ y, 4 < |y| → f y = 0) {M : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (F : C(UnitAddCircle, ℂ))
    (hF : ∀ k : ℤ, fourierCoeff F k =
      (scalarProfileSample f N k.natAbs : ℂ)) (x : UnitAddCircle) :
    ‖F x‖ ≤ 16 * 6^3 * (2*M) * (N:ℝ) /
      (1 + ((N:ℝ)*circleCharacterChord x)^2) := by
  obtain ⟨J, hRJ, hJ⟩ := exists_scalarProfile_cutoffIndex
    (R := 4) (by norm_num) N hN
  let c : ℕ → ℂ := fun k => (scalarProfileSample f N k : ℂ)
  have htail : ∀ k, J ≤ k → c k = 0 := by
    intro k hk
    have hRNJ : 4 * (N:ℝ) < (J:ℝ) := hRJ
    have hRk : 4 * (N:ℝ) < (k:ℝ) := by
      exact lt_of_lt_of_le hRNJ (by exact_mod_cast hk)
    have hz := scalarProfileSample_eq_zero_of_outside hSupport N
      (by omega) hRk
    simpa [c] using hz
  have hweight : ∀ j ∈ Finset.range J,
      ‖secondWeight c j‖ ≤ (2*M) * ((j+1:ℕ):ℝ) / (N:ℝ)^2 := by
    intro j hj
    have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
    have hdiff := abs_centeredSecondDifference_le_of_iteratedDeriv_two hf hDeriv
      (((j+1:ℕ):ℝ)/(N:ℝ)) ((N:ℝ)⁻¹)
    have hsample :
        |scalarProfileSample f N j - 2*scalarProfileSample f N (j+1) +
          scalarProfileSample f N (j+2)| ≤ 2*M/(N:ℝ)^2 := by
      have hh : 0 < (N:ℝ)⁻¹ := inv_pos.mpr hNpos
      convert hdiff using 1 <;> simp [scalarProfileSample] <;>
        field_simp <;> ring
    have hreal :
        |scalarProfileSecondWeight f N j| ≤
          (2*M) * ((j+1:ℕ):ℝ)/(N:ℝ)^2 := by
      unfold scalarProfileSecondWeight
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        ((j+1:ℕ):ℝ) *
            |scalarProfileSample f N j - 2*scalarProfileSample f N (j+1) +
              scalarProfileSample f N (j+2)| ≤
          ((j+1:ℕ):ℝ) * (2*M/(N:ℝ)^2) :=
            mul_le_mul_of_nonneg_left hsample (Nat.cast_nonneg _)
        _ = (2*M) * ((j+1:ℕ):ℝ)/(N:ℝ)^2 := by ring
    have hcomplex : secondWeight c j =
        (scalarProfileSecondWeight f N j : ℂ) := by
      simp [secondWeight, c, scalarProfileSecondWeight, scalarProfileSample]
    rw [hcomplex, Complex.norm_real, Real.norm_eq_abs]
    exact hreal
  have hmixture : F = fejerMixture J c :=
    continuous_eq_fejerMixture F J c hF htail
  have hJ' : (J:ℝ) ≤ 6*(N:ℝ) := by
    have h := hJ
    norm_num at h ⊢
    nlinarith
  have hdec := BrownianSharp.AlignmentPaperScalarKernelDecay.fejerMixture_decay_of_weight_bound
    J N 6 (2*M) hN (by positivity)
    (by norm_num) hJ' c x hweight
  rw [hmixture]
  simpa using hdec

theorem exists_smoothResolution_scalarKernel_chord_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C * (2:ℝ)^s /
          (1 + (((2:ℝ)^s) * circleCharacterChord x)^2) := by
  have hcutoffComp : HasCompactSupport smoothResolutionCutoff.value := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0:ℝ) 2)
    intro y hy
    change smoothResolutionCutoff.value y ≠ 0 at hy
    by_contra hnorm
    have hnorm' : ¬ |y| ≤ 2 := by
      intro h
      apply hnorm
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using h
    exact hy (smoothResolutionCutoff.zero_of_two_le_abs y (le_of_not_ge hnorm'))
  obtain ⟨M₀, hM₀, hD₀⟩ := exists_iteratedDeriv_two_bound_of_compactSupport
    (smoothResolutionCutoff.smooth.of_le (by norm_num)) hcutoffComp
  have hprofile := differenceProfile_hasCompactSupport_and_C2 smoothResolutionCutoff
  obtain ⟨M₁, hM₁, hD₁⟩ := exists_iteratedDeriv_two_bound_of_compactSupport
    hprofile.1 hprofile.2
  let M := max M₀ M₁
  let C := 16 * 6^3 * (2*M)
  have hM : 0 ≤ M := le_max_of_le_left hM₀
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro s x
    by_cases hs : s = 0
    · subst s
      have hsupport : ∀ y, 4 < |y| → smoothResolutionCutoff.value y = 0 := by
        intro y hy
        exact smoothResolutionCutoff.zero_of_two_le_abs y (by linarith)
      have hderiv : ∀ y, |iteratedDeriv 2 smoothResolutionCutoff.value y| ≤ M := by
        intro y
        exact (hD₀ y).trans (le_max_left _ _)
      have hcoeff : ∀ k : ℤ, fourierCoeff
          (scalarBlockKernel smoothResolutionCutoff 0) k =
            (scalarProfileSample smoothResolutionCutoff.value 1 k.natAbs : ℂ) := by
        intro k
        rw [AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel_coefficient]
        cases k with
        | ofNat n => simp [scalarBlock, scalarProfileSample]
        | negSucc n =>
            simp only [scalarBlock, if_pos rfl, scalarProfileSample,
              Int.natAbs_negSucc, Int.cast_negSucc, Nat.cast_succ]
            rw [smoothResolutionCutoff.even]
            norm_num
      have hdec := profile_sample_kernel_decay
        (smoothResolutionCutoff.smooth.of_le (by norm_num)) hcutoffComp
        hsupport hM hderiv 1 (by norm_num)
        (scalarBlockKernel smoothResolutionCutoff 0) hcoeff x
      simpa [C, M] using hdec
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs
      let N := 2^s
      have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow s 2 (by omega)
      have hsupport : ∀ y, 4 < |y| → differenceProfile smoothResolutionCutoff y = 0 := by
        intro y hy
        exact differenceProfile_eq_zero_of_four_le_abs smoothResolutionCutoff (by linarith)
      have hderiv : ∀ y,
          |iteratedDeriv 2 (differenceProfile smoothResolutionCutoff) y| ≤ M := by
        intro y
        exact (hD₁ y).trans (le_max_right _ _)
      have hcoeff : ∀ k : ℤ, fourierCoeff
          (scalarBlockKernel smoothResolutionCutoff s) k =
            (scalarProfileSample (differenceProfile smoothResolutionCutoff) N k.natAbs : ℂ) := by
        intro k
        rw [AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel_coefficient,
          scalarBlock_eq_differenceProfile_sample smoothResolutionCutoff s hspos]
      have hdec := profile_sample_kernel_decay
        hprofile.1 hprofile.2 hsupport hM hderiv N hN
        (scalarBlockKernel smoothResolutionCutoff s) hcoeff x
      simpa [C, M, N, Nat.cast_pow, Real.rpow_natCast] using hdec

end BrownianSharp.AlignmentPaperSmoothKernelDecay
