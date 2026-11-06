import BrownianSharp.AlignmentPaperKernelHörmander
import BrownianSharp.AlignmentPaperSmoothKernelDerivative
import BrownianSharp.InverseDerivativeProfileIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Actual first-order inverse blocks: the odd derivative kernel is controlled
by differentiating the even compact profile kernel of order two. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperInverseFirstDerivative

open BrownianSharp.InverseDerivativeProfile
open BrownianSharp.ScalarKernelL1
open BrownianSharp.ScalarHighFrequency
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPaperSmoothKernelDerivative
open BrownianSharp.AlignmentPaperFejerPointwise
open HaarQuarter.TrigonometricHaarExtraction

private def profileTwoSampleKernel (t : ℕ) : C(UnitAddCircle, ℂ) :=
  polynomialKernel (ScalarAtomVariance.scalarFrequencyBox t) fun k =>
    (scalarProfileSample (profile 2) (2^t) k.natAbs : ℂ)

private theorem profileTwoSampleKernel_coefficient (t : ℕ) (ht : 0 < t)
    (k : ℤ) :
    fourierCoeff (profileTwoSampleKernel t) k =
      (scalarProfileSample (profile 2) (2^t) k.natAbs : ℂ) := by
  apply polynomialKernel_coefficient_of_support
  intro q hq
  have hN : 0 < (2^t : ℕ) := by positivity
  have hfreq : (2 : ℝ)^(t+1) ≤ |(q:ℝ)| := by
    simp only [ScalarAtomVariance.scalarFrequencyBox, Finset.mem_Icc,
      not_and_or, not_le] at hq
    rcases hq with hq | hq
    · have hcast : (q:ℝ) < -((2:ℝ)^(t+1)) := by exact_mod_cast hq
      exact le_trans (by linarith) (neg_le_abs _)
    · have hcast : (2:ℝ)^(t+1) < (q:ℝ) := by exact_mod_cast hq
      exact hcast.le.trans (le_abs_self _)
  have hNcast : ((2^t:ℕ):ℝ) = (2:ℝ)^t := by norm_cast
  have hcast : (q.natAbs:ℝ) = |(q:ℝ)| := by
    cases q with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.natAbs_negSucc, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
        rw [abs_of_nonpos (neg_nonpos.mpr (by positivity))]
        push_cast
        ring
  have harg : 2 ≤ ((q.natAbs:ℕ):ℝ) / ((2^t:ℕ):ℝ) := by
    rw [hNcast, hcast]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^t)).2
    have hpow : (2:ℝ)^(t+1) = 2*(2:ℝ)^t := by rw [pow_succ]; ring
    rw [hpow] at hfreq
    nlinarith
  have hargabs : 2 ≤ |((q.natAbs:ℕ):ℝ) / ((2^t:ℕ):ℝ)| := by
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact harg
  have hz := profile_eq_zero_of_two_le_abs 2 hargabs
  change (profile 2 (((q.natAbs:ℕ):ℝ) / ((2^t:ℕ):ℝ)) : ℂ) = 0
  exact_mod_cast hz

private theorem profileTwoSample_eq_signed (t : ℕ) (n : ℤ) :
    scalarProfileSample (profile 2) (2^t) n.natAbs =
      profile 2 ((n:ℝ) / (2:ℝ)^t) := by
  have hNcast : ((2^t:ℕ):ℝ) = (2:ℝ)^t := by norm_cast
  cases n with
  | ofNat m =>
      simp [scalarProfileSample, hNcast]
  | negSucc m =>
      have hprof := profile_neg_eq_of_even (K := 2) ⟨1, by norm_num⟩
        (((m+1:ℕ):ℝ)/(2:ℝ)^t)
      have hcast : ((Int.negSucc m:ℤ):ℝ) = -((m+1:ℕ):ℝ) := by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      simp only [scalarProfileSample, hNcast, Int.natAbs_negSucc,
        Nat.cast_add, Nat.cast_one, hcast]
      simp only [Nat.cast_succ]
      rw [Nat.cast_add, Nat.cast_one] at hprof
      have hdiv : -((↑m:ℝ) + 1) / (2:ℝ)^t =
          -(((↑m:ℝ) + 1) / (2:ℝ)^t) := by ring
      rw [hdiv]
      exact hprof.symm

private theorem inverseFirstDerivative_coefficient_identity
    (t : ℕ) (ht : 0 < t) (n : ℤ) :
    (2 * Real.pi * Complex.I * (n:ℂ)) *
        (scalarProfileSample (profile 2) (2^t) n.natAbs : ℂ) =
      (-4 * Real.pi^2 * (2:ℝ)^(2*t) : ℝ) * inverseMultiplier t 1 n := by
  by_cases hn : n = 0
  · subst n
    simp [inverseMultiplier, profile, cutoff_eq_one (by norm_num : |(0:ℝ)| ≤ 1)]
  · have hNcast : ((2^t:ℕ):ℝ) = (2:ℝ)^t := by norm_cast
    have hNpos : (2:ℝ)^t ≠ 0 := by positivity
    have hξ : (n:ℝ)/(2:ℝ)^t ≠ 0 := by
      exact div_ne_zero (by exact_mod_cast hn) hNpos
    have hprof := inverseMultiplier_eq_profile t 1 ht n hn
    have hsample := profileTwoSample_eq_signed t n
    have hrel : profile 1 ((n:ℝ)/(2:ℝ)^t) =
        ((n:ℝ)/(2:ℝ)^t) * profile 2 ((n:ℝ)/(2:ℝ)^t) := by
      unfold profile
      have hξpow : ((n:ℝ)/(2:ℝ)^t)^1 ≠ 0 := pow_ne_zero 1 hξ
      have hξpow2 : ((n:ℝ)/(2:ℝ)^t)^2 ≠ 0 := pow_ne_zero 2 hξ
      field_simp
      <;> ring
    rw [hrel] at hprof
    simp only [pow_one] at hprof
    rw [← hsample] at hprof
    have hNnat : ((2^t:ℕ):ℝ) = (2:ℝ)^t := hNcast
    rw [hprof]
    push_cast
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Complex.I_ne_zero
    have hNcomplex : ((2:ℝ)^t : ℂ) ≠ 0 := by exact_mod_cast hNpos
    push_cast
    field_simp [hpi, hNcomplex]
    rw [Complex.I_sq]
    ring

private theorem profileTwoSampleKernel_deriv_eq_inverseKernel
    (t : ℕ) (ht : 0 < t) (x : ℝ) :
    deriv (fun y : ℝ => profileTwoSampleKernel t (y : UnitAddCircle)) x =
      (-4 * Real.pi^2 * (2:ℝ)^(2*t) : ℂ) *
        inverseMultiplierKernel t 1 (x : UnitAddCircle) := by
  classical
  let S := ScalarAtomVariance.scalarFrequencyBox t
  let c : ℤ → ℂ := fun k =>
    (scalarProfileSample (profile 2) (2^t) k.natAbs : ℂ)
  have hfun : (fun y : ℝ => profileTwoSampleKernel t (y : UnitAddCircle)) =
      (fun y : ℝ => ∑ k ∈ S, c k * fourier k (y : UnitAddCircle)) := by
    funext y
    simp [profileTwoSampleKernel, S, c, polynomialKernel, smul_eq_mul]
  let A : ℤ → ℝ → ℂ := fun k y => c k * fourier k (y : UnitAddCircle)
  let A' : ℤ → ℂ := fun k =>
    c k * ((2 * Real.pi * Complex.I * (k:ℂ)) * fourier k (x : UnitAddCircle))
  have hhas0 : HasDerivAt (∑ k ∈ S, A k) (∑ k ∈ S, A' k) x := by
    apply HasDerivAt.sum
    intro k hk
    have h := (hasDerivAt_fourier (T := (1:ℝ)) k x).const_mul (c k)
    simpa [A, A', mul_comm, mul_left_comm, mul_assoc] using h
  have hhas : HasDerivAt
      (fun y : ℝ => ∑ k ∈ S, c k * fourier k (y : UnitAddCircle))
      (∑ k ∈ S, c k *
        ((2 * Real.pi * Complex.I * (k:ℂ)) * fourier k (x : UnitAddCircle))) x := by
    convert hhas0 using 1
    ext y
    simp [A]
  have hderiv := hhas.deriv
  rw [← hfun] at hderiv
  rw [hderiv]
  have hKpoint : inverseMultiplierKernel t 1 (x : UnitAddCircle) =
      ∑ k ∈ S, inverseMultiplier t 1 k * fourier k (x : UnitAddCircle) := by
    simp [inverseMultiplierKernel, polynomialKernel, S, smul_eq_mul]
  have hsum :
      (∑ k ∈ S, c k *
        ((2 * Real.pi * Complex.I * (k:ℂ)) * fourier k (x : UnitAddCircle))) =
      (-4 * Real.pi^2 * (2:ℝ)^(2*t) : ℂ) *
        inverseMultiplierKernel t 1 (x : UnitAddCircle) := by
    rw [hKpoint, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hc := inverseFirstDerivative_coefficient_identity t ht k
    calc
      c k * ((2 * Real.pi * Complex.I * (k:ℂ)) * fourier k (x : UnitAddCircle)) =
          ((2 * Real.pi * Complex.I * (k:ℂ)) * c k) * fourier k (x : UnitAddCircle) := by ring
      _ = ((-4 * Real.pi^2 * (2:ℝ)^(2*t) : ℝ) * inverseMultiplier t 1 k) *
          fourier k (x : UnitAddCircle) := by rw [hc]
      _ = _ := by push_cast; ring
  exact hsum

private theorem integral_circle_inverse_chord_bound (N : ℝ) (hN : 0 < N) :
    (∫ x : UnitAddCircle,
      (1 + (N * circleCharacterChord x)^2)⁻¹
        ∂AddCircle.haarAddCircle) ≤ Real.pi / (4*N) := by
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  let f : ℝ → ℝ := fun x => (1 + (N * characterChord x)^2)⁻¹
  let g : ℝ → ℝ := fun x => (1 + (4*N*x)^2)⁻¹
  have hfinite : volume I ≠ ⊤ := by
    rw [show I = Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2) by rfl, Real.volume_Ioc]
    simp
  have hchcont : Continuous characterChord := by
    unfold characterChord character
    fun_prop
  have hfmeas : Measurable f := by
    have hbase : Continuous (fun x : ℝ => 1 + (N * characterChord x)^2) := by
      exact continuous_const.add ((continuous_const.mul hchcont).pow 2)
    change Measurable (fun x : ℝ => (1 + (N * characterChord x)^2)⁻¹)
    exact hbase.measurable.inv
  have hgmeas : Measurable g := by
    have hbase : Continuous (fun x : ℝ => 1 + (4*N*x)^2) := by fun_prop
    change Measurable (fun x : ℝ => (1 + (4*N*x)^2)⁻¹)
    exact hbase.measurable.inv
  have hfint : IntegrableOn f I volume := by
    apply Measure.integrableOn_of_bounded (μ := volume) (s := I) hfinite
      hfmeas.aestronglyMeasurable (M := 1)
    filter_upwards with x
    have hpos : 0 < 1 + (N * characterChord x)^2 := by positivity
    have hval : 0 ≤ (1 + (N * characterChord x)^2)⁻¹ := by positivity
    have hden : 1 ≤ 1 + (N * characterChord x)^2 := by nlinarith
    calc
      ‖f x‖ = (1 + (N * characterChord x)^2)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hval]
      _ ≤ 1 := by
        calc
          _ ≤ 1⁻¹ := (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1)).2 hden
          _ = 1 := by norm_num
  have hgfull : Integrable g volume := by
    dsimp [g]
    exact integrable_inv_one_add_mul_sq (by positivity : 4*N ≠ 0)
  have hgint : IntegrableOn g I volume := hgfull.integrableOn
  have hpoint : ∀ x ∈ I, f x ≤ g x := by
    intro x hx
    have hxabs : |x| ≤ 1/2 := by
      rcases Set.mem_Ioc.mp (by simpa [I] using hx) with ⟨hlo, hhi⟩
      rw [abs_le]
      constructor <;> linarith
    have hchord := BrownianSharp.AlignmentPaperKernelHörmander.characterChord_lower_four_abs hxabs
    have hsq : (4*N*x)^2 ≤ (N*characterChord x)^2 := by
      have habs : |4*N*x| ≤ N*characterChord x := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4), abs_of_pos hN]
        nlinarith
      have hnonneg : 0 ≤ N*characterChord x := by
        unfold characterChord
        exact mul_nonneg hN.le (norm_nonneg _)
      have hdiff : 0 ≤ N*characterChord x - |4*N*x| := by linarith
      have hsum : 0 ≤ N*characterChord x + |4*N*x| := by positivity
      have hprod := mul_nonneg hdiff hsum
      nlinarith [sq_abs (4*N*x)]
    have hden : 1 + (4*N*x)^2 ≤ 1 + (N*characterChord x)^2 := by nlinarith
    have hpos₁ : 0 < 1 + (N*characterChord x)^2 := by positivity
    have hpos₂ : 0 < 1 + (4*N*x)^2 := by positivity
    dsimp [f, g]
    exact (inv_le_inv₀ hpos₁ hpos₂).2 hden
  have hmono : (∫ x in I, f x ∂volume) ≤ ∫ x in I, g x ∂volume :=
    MeasureTheory.setIntegral_mono_on hfint hgint (by measurability) hpoint
  have hnonneg : 0 ≤ᵐ[volume] g := by
    filter_upwards with x
    dsimp [g]
    positivity
  have hset : (∫ x in I, g x ∂volume) ≤ ∫ x, g x ∂volume :=
    MeasureTheory.setIntegral_le_integral hgfull hnonneg
  have hwhole : (∫ x, g x ∂volume) = Real.pi / (4*N) := by
    dsimp [g]
    rw [integral_univ_inv_one_add_mul_sq (4*N)]
    rw [abs_of_pos (by positivity : (0:ℝ) < 4*N)]
  have hreal : (∫ x in I, f x ∂volume) ≤ Real.pi/(4*N) := by
    calc
      _ ≤ ∫ x in I, g x ∂volume := hmono
      _ ≤ ∫ x, g x ∂volume := hset
      _ = Real.pi/(4*N) := hwhole
  have hpre := AddCircle.integral_preimage (T := (1:ℝ)) (-(1:ℝ)/2)
    (fun x : UnitAddCircle => (1 + (N * circleCharacterChord x)^2)⁻¹)
  have hpre' : (∫ x in I,
      (1 + (N * circleCharacterChord (x:UnitAddCircle))^2)⁻¹ ∂volume) =
      ∫ x : UnitAddCircle, (1 + (N * circleCharacterChord x)^2)⁻¹ := by
    convert hpre using 1 <;> norm_num [I]
  have hhaar''  : (∫ x : UnitAddCircle,
      (1 + (N * circleCharacterChord x)^2)⁻¹ ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, (1 + (N * circleCharacterChord x)^2)⁻¹ ∂(volume : Measure UnitAddCircle) := by
    rw [AddCircle.integral_haarAddCircle (T := (1:ℝ))]
    simp
  calc
    _ = ∫ x in I, f x ∂volume := by
      rw [hhaar'', ← hpre']
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      simp [I, f, BrownianSharp.AlignmentPaperKernelHörmander.circleCharacterChord_coe]
    _ ≤ Real.pi/(4*N) := hreal

/-- The actual first inverse derivative block has the sharp dyadic L1 decay.
The proof differentiates the sampled even order-two profile kernel, applies
its actual Fejér chord envelope, and integrates that envelope on the circle. -/
theorem exists_inverseFirstDerivativeKernel_L1_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 0 < t →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel t 1 x‖
        ∂AddCircle.haarAddCircle) ≤ C * ((2:ℝ)^t)⁻¹ := by
  obtain ⟨M, hM, hderiv⟩ := exists_profile_secondDerivative_bound 2
  let Cder : ℝ := 96 * Real.pi * (16 * 6^4) * M
  let C : ℝ := 1 + Cder + Cder / (16 * Real.pi)
  have hCder : 0 ≤ Cder := by dsimp [Cder]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  let N : ℕ := 2^t
  have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow t 2 (by omega)
  have hNcast : (N:ℝ) = (2:ℝ)^t := by dsimp [N]; norm_cast
  have hsupport : ∀ y, 4 < |y| → profile 2 y = 0 := by
    intro y hy
    exact profile_eq_zero_of_two_le_abs 2 (by linarith)
  have hcoeff : ∀ k : ℤ,
      fourierCoeff (profileTwoSampleKernel t) k =
        (scalarProfileSample (profile 2) N k.natAbs : ℂ) := by
    intro k
    simpa [N] using profileTwoSampleKernel_coefficient t ht k
  have hNpos : (N:ℝ) > 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by positivity : N ≠ 0))
  let major : UnitAddCircle → ℝ := fun x =>
    (Cder / (4 * Real.pi^2)) *
      (1 + ((N:ℝ) * circleCharacterChord x)^2)⁻¹
  have hdencont : Continuous (fun x : UnitAddCircle =>
      1 + ((N:ℝ) * circleCharacterChord x)^2) := by
    unfold circleCharacterChord
    fun_prop
  have hmajorcont : Continuous major := by
    have hrecip : Continuous (fun x : UnitAddCircle =>
        (1 + ((N:ℝ) * circleCharacterChord x)^2)⁻¹) :=
      hdencont.inv₀ (fun x => ne_of_gt (by positivity))
    exact continuous_const.mul hrecip
  have hmajorint : Integrable major AddCircle.haarAddCircle :=
    hmajorcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hkernelcont : Continuous (fun x : UnitAddCircle =>
      ‖inverseMultiplierKernel t 1 x‖) := by
    exact (inverseMultiplierKernel t 1).continuous.norm
  have hkernelint : Integrable (fun x : UnitAddCircle =>
      ‖inverseMultiplierKernel t 1 x‖) AddCircle.haarAddCircle :=
    hkernelcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint : ∀ x : UnitAddCircle, ‖inverseMultiplierKernel t 1 x‖ ≤ major x := by
    intro x
    obtain ⟨x0, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hdec := profile_sample_kernel_derivative_chord_decay
      ((profile_smooth 2).of_le (by norm_num)) (profile_hasCompactSupport 2)
      hsupport hM hderiv N hN (profileTwoSampleKernel t) hcoeff x0
    have hiden := profileTwoSampleKernel_deriv_eq_inverseKernel t ht x0
    have hconstpos : 0 < 4 * Real.pi^2 * (N:ℝ)^2 := by positivity
    have hNpow : (2:ℝ)^(2*t) = (N:ℝ)^2 := by
      rw [hNcast]
      rw [show 2*t = t*2 by omega, pow_mul]
    have hNpowC : ((2:ℝ)^(2*t) : ℂ) = (N:ℂ)^2 := by exact_mod_cast hNpow
    rw [hNpowC] at hiden
    have hneg : (-4 * Real.pi^2 * (N:ℝ)^2) < 0 := by
      have : 0 < (N:ℝ)^2 := sq_pos_of_pos hNpos
      nlinarith [Real.pi_pos, this]
    have hnormid :
        ‖deriv (fun y : ℝ => profileTwoSampleKernel t (y : UnitAddCircle)) x0‖ =
          (4 * Real.pi^2 * (N:ℝ)^2) *
            ‖inverseMultiplierKernel t 1 (x0:UnitAddCircle)‖ := by
      rw [hiden, norm_mul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
    have hbound : ‖inverseMultiplierKernel t 1 (x0:UnitAddCircle)‖ ≤ major (x0:UnitAddCircle) := by
      apply (mul_le_mul_iff_of_pos_left hconstpos).1
      calc
        (4 * Real.pi^2 * (N:ℝ)^2) *
            ‖inverseMultiplierKernel t 1 (x0:UnitAddCircle)‖ =
          ‖deriv (fun y : ℝ => profileTwoSampleKernel t (y : UnitAddCircle)) x0‖ := by
            rw [hnormid]
        _ ≤ Cder * (N:ℝ)^2 /
            (1 + ((N:ℝ) * circleCharacterChord (x0:UnitAddCircle))^2) := by
              simpa [Cder, hNcast] using hdec
        _ = (4 * Real.pi^2 * (N:ℝ)^2) * major (x0:UnitAddCircle) := by
              dsimp [major]
              field_simp [Real.pi_ne_zero]
              <;> ring
    simpa [major] using hbound
  have hint : (∫ x : UnitAddCircle,
      (1 + ((N:ℝ) * circleCharacterChord x)^2)⁻¹
        ∂AddCircle.haarAddCircle) ≤ Real.pi / (4 * (N:ℝ)) := by
    have h := integral_circle_inverse_chord_bound (N:ℝ) hNpos
    simpa [mul_pow] using h
  calc
    (∫ x : UnitAddCircle, ‖inverseMultiplierKernel t 1 x‖
        ∂AddCircle.haarAddCircle) ≤ ∫ x : UnitAddCircle, major x
        ∂AddCircle.haarAddCircle := integral_mono hkernelint hmajorint hpoint
    _ = (Cder / (4 * Real.pi^2)) *
        (∫ x : UnitAddCircle,
          (1 + ((N:ℝ) * circleCharacterChord x)^2)⁻¹
          ∂AddCircle.haarAddCircle) := by
      unfold major
      rw [integral_const_mul]
    _ ≤ (Cder / (4 * Real.pi^2)) * (Real.pi/(4*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (Cder/(16*Real.pi)) * ((2:ℝ)^t)⁻¹ := by
      rw [hNcast]
      field_simp [ne_of_gt Real.pi_pos]
      <;> ring
    _ ≤ C * ((2:ℝ)^t)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [C]
      nlinarith [hCder]

/-- The same first-derivative kernel bound includes the fixed low block. -/
theorem exists_inverseFirstDerivativeKernel_allGrade_L1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel t 1 x‖
        ∂AddCircle.haarAddCircle) ≤ C * ((2:ℝ)^t)⁻¹ := by
  obtain ⟨Cpos, hCpos, hpositive⟩ := exists_inverseFirstDerivativeKernel_L1_bound
  have hK0cont : Continuous (fun x : UnitAddCircle =>
      ‖inverseMultiplierKernel 0 1 x‖) :=
    (inverseMultiplierKernel 0 1).continuous.norm
  have hK0int : Integrable (fun x : UnitAddCircle =>
      ‖inverseMultiplierKernel 0 1 x‖) AddCircle.haarAddCircle :=
    hK0cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let B0 : ℝ := ∫ x : UnitAddCircle, ‖inverseMultiplierKernel 0 1 x‖
    ∂AddCircle.haarAddCircle
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact integral_nonneg (fun x => norm_nonneg _)
  let C : ℝ := Cpos + B0 + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t
  by_cases ht : t = 0
  · subst t
    have hpow : ((2:ℝ)^0)⁻¹ = 1 := by norm_num
    rw [hpow]
    dsimp [C, B0]
    linarith
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hbound := hpositive t htpos
    calc
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel t 1 x‖
          ∂AddCircle.haarAddCircle) ≤ Cpos * ((2:ℝ)^t)⁻¹ := hbound
      _ ≤ C * ((2:ℝ)^t)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith

