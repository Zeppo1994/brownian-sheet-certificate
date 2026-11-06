import BrownianSharp.AlignmentPaperFejerDerivative
import BrownianSharp.AlignmentPaperSmoothKernelDecay
import BrownianSharp.FejerSecondDifference
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Derivative decay for the actual smooth-resolution scalar kernels. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperSmoothKernelDerivative

open BrownianSharp.AlignmentPaperFejerDerivative
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.ScalarKernelL1
open HaarQuarter.TheoremD.FejerFourier
open HaarQuarter.TrigonometricHaarExtraction

private theorem profile_sample_kernel_derivative_decay
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hSupport : ∀ y, 4 < |y| → f y = 0) {M : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (F : C(UnitAddCircle, ℂ))
    (hF : ∀ k : ℤ, fourierCoeff F k =
      (scalarProfileSample f N k.natAbs : ℂ)) (x : ℝ) :
    ‖deriv (fun y : ℝ => F (y : UnitAddCircle)) x‖ ≤
      96 * Real.pi * (16 * 6^4) * M * (N:ℝ)^2 /
        (1 + ((N:ℝ)*circleCharacterChord (x : UnitAddCircle))^2) := by
  classical
  obtain ⟨J, hRJ, hJ⟩ := exists_scalarProfile_cutoffIndex
    (R := 4) (by norm_num) N hN
  let c : ℕ → ℂ := fun k => (scalarProfileSample f N k : ℂ)
  have htail : ∀ k, J ≤ k → c k = 0 := by
    intro k hk
    have hRNJ : 4 * (N:ℝ) < (J:ℝ) := hRJ
    have hRk : 4 * (N:ℝ) < (k:ℝ) := by exact lt_of_lt_of_le hRNJ (by exact_mod_cast hk)
    have hz := scalarProfileSample_eq_zero_of_outside hSupport N (by omega) hRk
    simpa [c] using hz
  have hweight : ∀ j ∈ Finset.range J,
      ‖secondWeight c j‖ ≤ (2*M) * ((j+1:ℕ):ℝ)/(N:ℝ)^2 := by
    intro j hj
    have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
    have hdiff := abs_centeredSecondDifference_le_of_iteratedDeriv_two hf hDeriv
      (((j+1:ℕ):ℝ)/(N:ℝ)) ((N:ℝ)⁻¹)
    have hsample :
        |scalarProfileSample f N j - 2*scalarProfileSample f N (j+1) +
          scalarProfileSample f N (j+2)| ≤ 2*M/(N:ℝ)^2 := by
      have hh : 0 < (N:ℝ)⁻¹ := inv_pos.mpr hNpos
      convert hdiff using 1 <;> simp [scalarProfileSample] <;> field_simp <;> ring
    have hreal :
        |scalarProfileSecondWeight f N j| ≤ (2*M) * ((j+1:ℕ):ℝ)/(N:ℝ)^2 := by
      unfold scalarProfileSecondWeight
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        ((j+1:ℕ):ℝ) *
            |scalarProfileSample f N j - 2*scalarProfileSample f N (j+1) +
              scalarProfileSample f N (j+2)| ≤ ((j+1:ℕ):ℝ) * (2*M/(N:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hsample (Nat.cast_nonneg _)
        _ = (2*M) * ((j+1:ℕ):ℝ)/(N:ℝ)^2 := by ring
    have hcomplex : secondWeight c j = (scalarProfileSecondWeight f N j : ℂ) := by
      simp [secondWeight, c, scalarProfileSecondWeight, scalarProfileSample]
    rw [hcomplex, Complex.norm_real, Real.norm_eq_abs]
    exact hreal
  have hmixture : F = fejerMixture J c := continuous_eq_fejerMixture F J c hF htail
  have hJ' : (J:ℝ) ≤ 6*(N:ℝ) := by
    have h := hJ
    norm_num at h ⊢
    nlinarith
  have hFfun : (fun y : ℝ => F (y : UnitAddCircle)) =
      fun y => ∑ j ∈ Finset.range J,
        secondWeight c j *
          (HaarQuarter.TheoremD.FejerFourier.realFejerKernel (j+1) y : ℂ) := by
    funext y
    change F (y : UnitAddCircle) = _
    rw [hmixture]
    simp only [fejerMixture, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      smul_eq_mul, Finset.sum_apply, fejerKernel, ContinuousMap.coe_mk]
    congr 1
    funext j
    change secondWeight c j * fejerFourierPolynomial (j+1) (y : UnitAddCircle) = _
    rw [fejerFourierPolynomial_eval_eq_real]
  have hhas : HasDerivAt (fun y : ℝ => F (y : UnitAddCircle))
      (∑ j ∈ Finset.range J, secondWeight c j *
        (((2*@inner ℝ ℂ _ (characterSum (j+1) x)
          (characterSumDerivative (j+1) x) / ((j+1:ℕ):ℝ)) : ℝ) : ℂ)) x := by
    rw [hFfun]
    have hs := HasDerivAt.sum (u := Finset.range J) (fun j hj => by
      have hp := realFejerKernel_hasDerivAt (j+1) x
      have hp' := HasDerivAt.ofReal_comp hp
      have hmul := hp'.const_mul (secondWeight c j)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    convert hs using 1
    · ext y
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    ·
      apply Finset.sum_congr rfl
      intro j hj
      simp [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      <;> ring
  have hcoeff (j : ℕ) :
      2*@inner ℝ ℂ _ (characterSum (j+1) x) (characterSumDerivative (j+1) x) /
        ((j+1:ℕ):ℝ) =
        deriv (HaarQuarter.TheoremD.FejerFourier.realFejerKernel (j+1)) x := by
    exact (realFejerKernel_hasDerivAt (j+1) x).deriv.symm
  have hderiv : deriv (fun y : ℝ => F (y : UnitAddCircle)) x =
      ∑ j ∈ Finset.range J, secondWeight c j *
        (((2*@inner ℝ ℂ _ (characterSum (j+1) x)
          (characterSumDerivative (j+1) x) / ((j+1:ℕ):ℝ)) : ℝ) : ℂ) := hhas.deriv
  have hbound : ‖deriv (fun y : ℝ => F (y : UnitAddCircle)) x‖ ≤
      (96*Real.pi*M/(N:ℝ)^2) *
        ∑ j ∈ Finset.range J,
          (((j+1:ℕ):ℝ)^3 /
            (1+(((j+1:ℕ):ℝ)*circleCharacterChord (x:UnitAddCircle))^2)) := by
    rw [hderiv]
    calc
      _ ≤ ∑ j ∈ Finset.range J, ‖secondWeight c j‖ *
          |deriv (HaarQuarter.TheoremD.FejerFourier.realFejerKernel (j+1)) x| := by
        calc
          _ ≤ ∑ j ∈ Finset.range J,
              ‖secondWeight c j *
                (((2*@inner ℝ ℂ _ (characterSum (j+1) x)
                  (characterSumDerivative (j+1) x) / ((j+1:ℕ):ℝ)) : ℝ) : ℂ)‖ := norm_sum_le _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoeff]
            simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ j ∈ Finset.range J,
          ((2*M)*((j+1:ℕ):ℝ)/(N:ℝ)^2) *
            (48*Real.pi*((j+1:ℕ):ℝ)^2 /
              (1+(((j+1:ℕ):ℝ)*circleCharacterChord (x:UnitAddCircle))^2)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjpos : 0 < j+1 := by omega
        have hweightj := hweight j hj
        have hfj := realFejerKernel_deriv_decay (j+1) hjpos x
        have hchord : characterChord x = circleCharacterChord (x:UnitAddCircle) := by
          unfold characterChord circleCharacterChord
          rw [show fourier (T := (1:ℝ)) 1 (x:UnitAddCircle) = character 1 x by
            simpa [addCircleCharacter] using addCircleCharacter_coe (1:ℤ) x]
        simpa [Real.norm_eq_abs, hchord] using mul_le_mul hweightj hfj
          (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  let D := circleCharacterChord (x:UnitAddCircle)
  have hD : 0 ≤ D := by dsimp [D, circleCharacterChord]; positivity
  have hNreal : 0 < (N:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hN)
  have hsmallSum : (∑ j ∈ Finset.range J,
        (((j+1:ℕ):ℝ)^3/(1+(((j+1:ℕ):ℝ)*D)^2))) ≤ (J:ℝ)^4 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, ((j+1:ℕ):ℝ)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        let a : ℝ := ((j+1:ℕ):ℝ)
        have hpos : 0 < 1+(((j+1:ℕ):ℝ)*D)^2 := by positivity
        rw [div_le_iff₀ hpos]
        have ha : 0 ≤ ((j+1:ℕ):ℝ)^3 := by positivity
        nlinarith [sq_nonneg (((j+1:ℕ):ℝ)*D), ha]
      _ ≤ ∑ _j ∈ Finset.range J, (J:ℝ)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : ((j+1:ℕ):ℝ) ≤ (J:ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        exact pow_le_pow_left₀ (by positivity) hjle 3
      _ = (J:ℝ)^4 := by simp [Finset.sum_const, nsmul_eq_mul, pow_succ, mul_comm]
  have hlargeSum (hDpos : 0 < D) : (∑ j ∈ Finset.range J,
        (((j+1:ℕ):ℝ)^3/(1+(((j+1:ℕ):ℝ)*D)^2))) ≤ (J:ℝ)^2/D^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (((j+1:ℕ):ℝ)/D^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have ht : 0 < ((j+1:ℕ):ℝ) := by positivity
        have hden : 0 < 1+(((j+1:ℕ):ℝ)*D)^2 := by positivity
        rw [div_le_div_iff₀ hden (sq_pos_of_pos hDpos)]
        have hDsquare : 0 < D^2 := sq_pos_of_pos hDpos
        nlinarith [sq_nonneg (((j+1:ℕ):ℝ)*D), sq_nonneg (((j+1:ℕ):ℝ)-1)]
      _ ≤ ∑ _j ∈ Finset.range J, ((J:ℝ)/D^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : ((j+1:ℕ):ℝ) ≤ (J:ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        exact div_le_div_of_nonneg_right hjle (sq_nonneg D)
      _ = (J:ℝ)^2/D^2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hJbound : (J:ℝ) ≤ 6*(N:ℝ) := hJ'
  by_cases hsmall : (N:ℝ)*D ≤ 1
  · have hqnon : 0 ≤ (N:ℝ)*D := mul_nonneg (le_of_lt hNreal) hD
    have hden : 1+((N:ℝ)*D)^2 ≤ 2 := by nlinarith
    have hpos : 0 < 1+((N:ℝ)*D)^2 := by positivity
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (J:ℝ)) hJbound 4
    have hcoef : 0 ≤ 96*Real.pi*M/(N:ℝ)^2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hpow hcoef
    have hbase : (96*Real.pi*M/(N:ℝ)^2)*(J:ℝ)^4 ≤
        (96*Real.pi*M*(6:ℝ)^4)*(N:ℝ)^2 := by
      convert hscaled using 1 <;> field_simp [ne_of_gt hNreal] <;> ring_nf
    calc
      _ ≤ (96*Real.pi*M/(N:ℝ)^2) * (J:ℝ)^4 :=
        hbound.trans (mul_le_mul_of_nonneg_left hsmallSum (by positivity))
      _ ≤ (96*Real.pi*M*(6:ℝ)^4)*(N:ℝ)^2 := hbase
      _ ≤ 96*Real.pi*(16*6^4)*M*(N:ℝ)^2 /
          (1+((N:ℝ)*D)^2) := by
        rw [le_div_iff₀ hpos]
        have hmult := mul_le_mul_of_nonneg_left hden
          (by positivity : 0 ≤ (96*Real.pi*M*(6:ℝ)^4)*(N:ℝ)^2)
        have hbasepos : 0 ≤ (96*Real.pi*M*(6:ℝ)^4)*(N:ℝ)^2 := by positivity
        have hcoef : (96*Real.pi*M*(6:ℝ)^4)*(N:ℝ)^2 * 2 ≤
            96*Real.pi*(16*6^4)*M*(N:ℝ)^2 := by nlinarith [hbasepos]
        exact le_trans hmult hcoef
  · have hlarge : 1 < (N:ℝ)*D := lt_of_not_ge hsmall
    have hDpos : 0 < D := by
      by_contra hn
      have hz : D = 0 := le_antisymm (by linarith) hD
      rw [hz] at hlarge
      norm_num at hlarge
    have hden : 1+((N:ℝ)*D)^2 ≤ 2*((N:ℝ)*D)^2 := by nlinarith
    have hpos : 0 < 1+((N:ℝ)*D)^2 := by positivity
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (J:ℝ)) hJbound 2
    have hcoef : 0 ≤ 96*Real.pi*M/(N:ℝ)^2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hpow hcoef
    have hcancel :
        (96*Real.pi*M/(N:ℝ)^2) * (6*(N:ℝ))^2 =
          96*Real.pi*M*(6:ℝ)^2 := by
      field_simp [ne_of_gt hNreal]
    have hbase : (96*Real.pi*M/(N:ℝ)^2)*((J:ℝ)^2/D^2) ≤
        (96*Real.pi*M*(6:ℝ)^2)/D^2 := by
      calc
        _ = ((96*Real.pi*M/(N:ℝ)^2)*(J:ℝ)^2)/D^2 := by ring
        _ ≤ ((96*Real.pi*M/(N:ℝ)^2)*(6*(N:ℝ))^2)/D^2 := by
          exact div_le_div_of_nonneg_right hscaled (sq_nonneg D)
        _ = _ := by rw [hcancel]
    calc
      _ ≤ (96*Real.pi*M/(N:ℝ)^2) * ((J:ℝ)^2/D^2) :=
        hbound.trans (mul_le_mul_of_nonneg_left (hlargeSum hDpos) (by positivity))
      _ ≤ (96*Real.pi*M*(6:ℝ)^2)/D^2 := hbase
      _ ≤ 96*Real.pi*(16*6^4)*M*(N:ℝ)^2 /
          (1+((N:ℝ)*D)^2) := by
        rw [le_div_iff₀ hpos]
        field_simp [ne_of_gt hDpos]
        have hcoefpos : 0 ≤ 96*Real.pi*M*36 := by positivity
        have hcoef : 96*Real.pi*M*36*2 ≤ 96*Real.pi*16*6^4*M := by nlinarith [hcoefpos]
        have hmult := mul_le_mul_of_nonneg_left hden (by positivity : 0≤96*Real.pi*M*36)
        nlinarith [hmult, hcoef, sq_nonneg (N:ℝ), sq_nonneg D]

/-- Public generic profile-sampling derivative estimate. This exposes the
actual Fejér proof above for other compact smooth profiles without adding any
analytic premise beyond the proved derivative envelope. -/
theorem profile_sample_kernel_derivative_chord_decay
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hSupport : ∀ y, 4 < |y| → f y = 0) {M : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (F : C(UnitAddCircle, ℂ))
    (hF : ∀ k : ℤ, fourierCoeff F k =
      (scalarProfileSample f N k.natAbs : ℂ)) (x : ℝ) :
    ‖deriv (fun y : ℝ => F (y : UnitAddCircle)) x‖ ≤
      96 * Real.pi * (16 * 6^4) * M * (N:ℝ)^2 /
        (1 + ((N:ℝ)*circleCharacterChord (x : UnitAddCircle))^2) := by
  exact profile_sample_kernel_derivative_decay hf hfc hSupport hM hDeriv N hN F hF x

theorem exists_smoothResolution_scalarKernel_deriv_chord_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s (x : ℝ),
      ‖deriv (fun y : ℝ => scalarBlockKernel smoothResolutionCutoff s
          (y : UnitAddCircle)) x‖ ≤
        C * (2:ℝ)^(2*s) /
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2) := by
  have hcutoffComp : HasCompactSupport smoothResolutionCutoff.value := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℝ) 2)
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
  let C := 96*Real.pi*(16*6^4)*M
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro s x
    by_cases hs : s = 0
    · subst s
      have hsupport : ∀ y, 4 < |y| → smoothResolutionCutoff.value y = 0 := by
        intro y hy
        exact smoothResolutionCutoff.zero_of_two_le_abs y (by linarith)
      have hderiv : ∀ y,
          |iteratedDeriv 2 smoothResolutionCutoff.value y| ≤ M := by
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
      have hdec := profile_sample_kernel_derivative_decay
        (smoothResolutionCutoff.smooth.of_le (by norm_num)) hcutoffComp
        hsupport (le_max_of_le_left hM₀) hderiv 1 (by norm_num)
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
      have hdec := profile_sample_kernel_derivative_decay
        hprofile.1 hprofile.2 hsupport (le_max_of_le_right hM₁) hderiv N hN
        (scalarBlockKernel smoothResolutionCutoff s) hcoeff x
      rw [show (2:ℝ)^(2*s) = ((2:ℝ)^s)^2 by rw [show 2*s = s*2 by omega, pow_mul]]
      simpa [C, M, N] using hdec

end BrownianSharp.AlignmentPaperSmoothKernelDerivative
