import BrownianSharp.InverseDerivativeProfile
import BrownianSharp.ScalarHighFrequency
import BrownianSharp.ScalarProfileKernel
import BrownianSharp.ScalarPolynomialKernel
import Mathlib.Tactic

/-! Exact rescaling identities connecting the smooth dyadic block, its profile,
and the inverse-derivative Fourier multiplier. -/

noncomputable section

namespace BrownianSharp

open BrownianSharp.SmoothResolution
open BrownianSharp.InverseDerivativeProfile
open BrownianSharp.ScalarHighFrequency
open MeasureTheory

/-- Rescaling a positive scalar block by its dyadic scale removes the scale
from the cutoff arguments exactly. -/
theorem scalarBlock_rescale (t : ℕ) (ht : 0 < t) (ξ : ℝ) :
    scalarBlock t ((2 : ℝ) ^ t * ξ) = cutoff ξ - cutoff (2 * ξ) := by
  have ht1 : 1 ≤ t := by omega
  have hpow : (2 : ℝ) ^ t = (2 : ℝ) ^ (t - 1) * 2 := by
    calc
      (2 : ℝ) ^ t = (2 : ℝ) ^ (t - 1 + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (t - 1) * 2 := by rw [pow_succ]
  have hbasePos : 0 < (2 : ℝ) ^ (t - 1) := by positivity
  unfold scalarBlock
  rw [if_neg (Nat.ne_of_gt ht)]
  have hfirst : (2 : ℝ) ^ t * ξ / (2 : ℝ) ^ t = ξ := by
    field_simp
  have hsecond : (2 : ℝ) ^ t * ξ / (2 : ℝ) ^ (t - 1) = 2 * ξ := by
    rw [hpow]
    field_simp
  rw [hfirst, hsecond]

/-- The profile is the cutoff difference divided by the exact polynomial
homogeneity factor. This identity also holds at zero because the numerator
vanishes on a neighborhood of zero. -/
theorem profile_mul_pow_eq_cutoff_difference (K : ℕ) (ξ : ℝ) :
    ξ ^ K * profile K ξ = cutoff ξ - cutoff (2 * ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [profile, cutoff_eq_one (by norm_num : |(0 : ℝ)| ≤ 1)]
  · unfold profile
    have hp : ξ ^ K ≠ 0 := pow_ne_zero K hξ
    field_simp [hp]

/-- Full exact profile rescaling at a positive dyadic block. -/
theorem scalarBlock_rescale_eq_profile (t K : ℕ) (ht : 0 < t) (ξ : ℝ) :
    scalarBlock t ((2 : ℝ) ^ t * ξ) = ξ ^ K * profile K ξ := by
  rw [scalarBlock_rescale t ht ξ, profile_mul_pow_eq_cutoff_difference]

/-- The inverse-derivative symbol is exactly a fixed scale factor times the
rescaled real profile. The complex phase is retained explicitly. -/
theorem inverseMultiplier_eq_profile (t K : ℕ) (ht : 0 < t) (n : ℤ)
    (hn : n ≠ 0) :
    inverseMultiplier t K n =
      (((2 : ℝ) ^ t : ℂ)⁻¹ / (2 * Real.pi * Complex.I)) ^ K *
        (profile K ((n : ℝ) / (2 : ℝ) ^ t) : ℂ) := by
  let C : ℝ := (2 : ℝ) ^ t
  let ξ : ℝ := (n : ℝ) / C
  have hC : C ≠ 0 := by positivity
  have hξ : ξ ≠ 0 := by
    dsimp [ξ]
    exact div_ne_zero (by exact_mod_cast hn) hC
  have hnum := scalarBlock_rescale_eq_profile t K ht ξ
  have harg : C * ξ = (n : ℝ) := by
    dsimp [C, ξ]
    field_simp
  rw [inverseMultiplier, if_neg hn]
  have hnumC := congrArg (fun y : ℝ => (y : ℂ)) hnum
  rw [harg] at hnumC
  have hcastArg : (n : ℂ) = (C : ℂ) * (ξ : ℂ) := by
    exact_mod_cast harg.symm
  rw [hcastArg, hnumC]
  have hξC : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hnumC
  have hCcast : (C : ℂ) = ((2 : ℝ) ^ t : ℂ) := by
    dsimp [C]
    norm_cast
  have hξval : ξ = (n : ℝ) / (2 : ℝ) ^ t := by rfl
  rw [← hξval]
  rw [hCcast]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero
  let a : ℂ := (2 : ℂ) ^ t
  let b : ℂ := 2 * Real.pi * Complex.I
  have ha : a ≠ 0 := by
    dsimp [a]
    exact pow_ne_zero t (by norm_num : (2 : ℂ) ≠ 0)
  have hdenpow : (b * (a * (ξ : ℂ))) ^ K = (b * a) ^ K * (ξ : ℂ) ^ K := by
    rw [show b * (a * (ξ : ℂ)) = (b * a) * (ξ : ℂ) by ring, mul_pow, mul_pow]
  change ((ξ : ℂ) ^ K * (profile K ξ : ℂ)) /
      ((2 * Real.pi * Complex.I * ((2 : ℂ) ^ t * (ξ : ℂ))) ^ K) =
    (((2 : ℂ) ^ t)⁻¹ / (2 * Real.pi * Complex.I)) ^ K *
      (profile K ξ : ℂ)
  change ((ξ : ℂ) ^ K * (profile K ξ : ℂ)) /
      (b * (a * (ξ : ℂ))) ^ K = (a⁻¹ / b) ^ K * (profile K ξ : ℂ)
  rw [hdenpow]
  calc
    ((ξ : ℂ) ^ K * (profile K ξ : ℂ)) /
        ((b * a) ^ K * (ξ : ℂ) ^ K) =
      (profile K ξ : ℂ) / (b * a) ^ K := by
        field_simp [hξC]
    _ = (a⁻¹ / b) ^ K * (profile K ξ : ℂ) := by
      field_simp [ha, hpi]
      <;> ring

/-- Even inverse powers preserve the profile's real symmetry. -/
theorem profile_neg_eq_of_even {K : ℕ} (hK : Even K) (ξ : ℝ) :
    profile K (-ξ) = profile K ξ := by
  obtain ⟨m, rfl⟩ := hK
  by_cases hξ : ξ = 0
  · subst ξ
    simp [profile, cutoff_eq_one (by norm_num : |(0 : ℝ)| ≤ 1)]
  · have hp : (-ξ) ^ (2 * m) = ξ ^ (2 * m) := by
      rw [pow_mul, pow_mul]
      congr 1
      ring
    have hp' : (-ξ) ^ (m + m) = ξ ^ (m + m) := by
      simpa [two_mul] using hp
    unfold profile
    rw [cutoff_even ξ]
    have h2 : 2 * -ξ = -(2 * ξ) := by ring
    rw [h2, cutoff_even, hp']

def inverseProfileScale (t K : ℕ) : ℂ :=
  (((2 : ℝ) ^ t : ℂ)⁻¹ / (2 * Real.pi * Complex.I)) ^ K

/-- For even K the actual inverse-derivative symbol, including negative
frequencies and the zero coefficient, is the sampled real profile multiplied
by one fixed complex normalization. -/
theorem inverseMultiplier_eq_natAbs_profile (t K : ℕ) (ht : 0 < t)
    (hK : Even K) (n : ℤ) :
    inverseMultiplier t K n = inverseProfileScale t K *
      (profile K ((n.natAbs : ℝ) / (2 : ℝ) ^ t) : ℂ) := by
  cases n with
  | ofNat m =>
      by_cases hm : m = 0
      · subst m
        simp [inverseMultiplier, inverseProfileScale, profile,
          cutoff_eq_one (by norm_num : |(0 : ℝ)| ≤ 1)]
      · have hn : (Int.ofNat m : ℤ) ≠ 0 := by
          intro hz
          apply hm
          simpa using hz
        rw [inverseProfileScale]
        simpa using inverseMultiplier_eq_profile t K ht (Int.ofNat m) hn
  | negSucc m =>
      have hn : (Int.negSucc m : ℤ) ≠ 0 := by simp
      rw [inverseProfileScale]
      have hbase := inverseMultiplier_eq_profile t K ht (Int.negSucc m) hn
      have harg : ((Int.negSucc m : ℤ) : ℝ) / (2 : ℝ) ^ t =
          -(((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ t) := by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
        ring
      rw [harg] at hbase
      have hnat : (Int.negSucc m).natAbs = m + 1 := by simp
      have hprof := profile_neg_eq_of_even hK (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ t)
      rw [hprof] at hbase
      simpa [hnat] using hbase

/-- The fixed complex normalization is nonzero, including K=0. -/
theorem inverseProfileScale_ne_zero (t K : ℕ) : inverseProfileScale t K ≠ 0 := by
  unfold inverseProfileScale
  apply pow_ne_zero
  apply div_ne_zero
  · have hpow : ((2 : ℝ) ^ t : ℂ) ≠ 0 := by
      norm_cast
      positivity
    exact inv_ne_zero hpow
  · apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero

/-- The actual inverse-multiplier coefficients inherit the uniform profile
kernel bound after extracting their fixed complex normalization. -/
theorem exists_inverseMultiplier_uniform_L1_bound {K : ℕ} (hK : Even K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t : ℕ), 0 < t → ∀ F : C(UnitAddCircle, ℂ),
      (∀ k : ℤ, fourierCoeff F k = inverseMultiplier t K k) →
      (∫ x : UnitAddCircle, ‖F x‖ ∂AddCircle.haarAddCircle) ≤
        ‖inverseProfileScale t K‖ * L := by
  obtain ⟨L, hL, hprofile⟩ := ScalarKernelL1.exists_uniform_norm_integral_bound
    ((profile_smooth K).of_le (by simp)) (profile_hasCompactSupport K)
  refine ⟨L, hL, ?_⟩
  intro t ht F hF
  let N : ℕ := 2 ^ t
  let G : C(UnitAddCircle, ℂ) := (inverseProfileScale t K)⁻¹ • F
  have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow t 2 (by omega)
  have hNcast : (N : ℝ) = (2 : ℝ) ^ t := by
    dsimp [N]
    norm_cast
  have hscale : inverseProfileScale t K ≠ 0 := inverseProfileScale_ne_zero t K
  have hG : ∀ k : ℤ, fourierCoeff G k =
      (scalarProfileSample (profile K) N k.natAbs : ℂ) := by
    intro k
    have hk := hF k
    rw [inverseMultiplier_eq_natAbs_profile t K ht hK k] at hk
    have hfourier : fourierCoeff G k = (inverseProfileScale t K)⁻¹ *
        fourierCoeff F k := by
      simp [G, fourierCoeff.const_smul]
    rw [hfourier, hk]
    simp [scalarProfileSample, hNcast, hscale]
  have hbound := hprofile N hN G hG
  have hrep : F = inverseProfileScale t K • G := by
    ext x
    simp [G, smul_smul, hscale]
  rw [hrep]
  calc
    (∫ x : UnitAddCircle, ‖(inverseProfileScale t K • G) x‖
        ∂AddCircle.haarAddCircle) =
      ‖inverseProfileScale t K‖ *
        (∫ x : UnitAddCircle, ‖G x‖ ∂AddCircle.haarAddCircle) := by
          have hpoint (x : UnitAddCircle) :
              ‖(inverseProfileScale t K • G) x‖ =
                ‖inverseProfileScale t K‖ * ‖G x‖ := by
            simp [norm_smul]
          simp_rw [hpoint]
          rw [integral_const_mul]
    _ ≤ ‖inverseProfileScale t K‖ * L :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

/-- The original low block is the cutoff sampled at unit scale. -/
theorem scalarBlock_zero_eq_cutoff_sample (n : ℤ) :
    scalarBlock 0 (n : ℝ) =
      scalarProfileSample cutoff 1 n.natAbs := by
  have habs : cutoff (n : ℝ) = cutoff (n.natAbs : ℝ) := by
    cases n with
    | ofNat m => simp
    | negSucc m =>
        have hcast : (Int.negSucc m : ℝ) = -((m + 1 : ℕ) : ℝ) := by
          simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
        rw [hcast, cutoff_even]
        simp
  rw [scalarProfileSample]
  simp only [Nat.cast_one, div_one]
  simp [scalarBlock, habs]

/-- Positive blocks are the scale-`2^t` samples of the compact profile of
order zero. -/
theorem scalarBlock_eq_profile_sample (t : ℕ) (ht : 0 < t) (n : ℤ) :
    scalarBlock t (n : ℝ) =
      scalarProfileSample (profile 0) (2 ^ t) n.natAbs := by
  have hN : (2 ^ t : ℕ) ≠ 0 := by positivity
  have hNcast : ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := by norm_cast
  cases n with
  | ofNat m =>
      have harg : (2 : ℝ) ^ t * ((m : ℝ) / (2 : ℝ) ^ t) = (m : ℝ) := by
        field_simp
      have h := scalarBlock_rescale_eq_profile t 0 ht ((m : ℝ) / (2 : ℝ) ^ t)
      rw [harg] at h
      rw [scalarProfileSample, hNcast]
      simpa using h
  | negSucc m =>
      have harg : (2 : ℝ) ^ t *
          ((Int.negSucc m : ℝ) / (2 : ℝ) ^ t) = (Int.negSucc m : ℝ) := by
        field_simp
      have h := scalarBlock_rescale_eq_profile t 0 ht
        ((Int.negSucc m : ℝ) / (2 : ℝ) ^ t)
      rw [harg] at h
      have hcast : (Int.negSucc m : ℝ) = -((m + 1 : ℕ) : ℝ) := by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      rw [hcast] at h
      have hdiv : -((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ t =
          -(((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ t) := by ring
      rw [hdiv] at h
      have hprof := profile_neg_eq_of_even (K := 0) ⟨0, by simp⟩
        (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ t)
      rw [hprof] at h
      rw [scalarProfileSample, hNcast]
      simpa using h

/-- The actual scalar block kernel has a uniform L1 bound, with the low block
handled by the cutoff and every positive block by the compact order-zero
profile. -/
theorem exists_scalarBlockKernel_uniform_L1_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel t x‖
        ∂AddCircle.haarAddCircle) ≤ L := by
  obtain ⟨Lp, hLp, hprofile⟩ := ScalarKernelL1.exists_uniform_norm_integral_bound
    ((profile_smooth 0).of_le (by simp)) (profile_hasCompactSupport 0)
  have hcutoffComp : HasCompactSupport cutoff := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
    intro ξ hξ
    change cutoff ξ ≠ 0 at hξ
    by_contra hnorm
    have hnorm' : ¬ |ξ| ≤ 2 := by
      intro h
      apply hnorm
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using h
    have hz : cutoff ξ = 0 := cutoff_eq_zero (le_of_not_ge hnorm')
    exact hξ hz
  obtain ⟨Lc, hLc, hcutoff⟩ := ScalarKernelL1.exists_uniform_norm_integral_bound
    (cutoff_smooth.of_le (by simp)) hcutoffComp
  refine ⟨max Lp Lc, le_max_of_le_left hLp, ?_⟩
  intro t
  by_cases ht : t = 0
  · subst t
    have hcoeff : ∀ k : ℤ, fourierCoeff (ScalarKernelL1.scalarBlockKernel 0) k =
        (scalarProfileSample cutoff 1 k.natAbs : ℂ) := by
      intro k
      rw [ScalarKernelL1.scalarBlockKernel_coefficient, scalarBlock_zero_eq_cutoff_sample]
    have hb := hcutoff 1 (by norm_num) (ScalarKernelL1.scalarBlockKernel 0) hcoeff
    exact hb.trans (le_max_right _ _)
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let N : ℕ := 2 ^ t
    have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow t 2 (by omega)
    have hcoeff : ∀ k : ℤ, fourierCoeff (ScalarKernelL1.scalarBlockKernel t) k =
        (scalarProfileSample (profile 0) N k.natAbs : ℂ) := by
      intro k
      rw [ScalarKernelL1.scalarBlockKernel_coefficient, scalarBlock_eq_profile_sample t htpos]
    have hb := hprofile N hN (ScalarKernelL1.scalarBlockKernel t) hcoeff
    exact hb.trans (le_max_left _ _)

/-- Finite continuous kernel for the inverse-derivative scalar symbol. -/
def inverseMultiplierKernel (t K : ℕ) : C(UnitAddCircle, ℂ) :=
  ScalarKernelL1.polynomialKernel (ScalarAtomVariance.scalarFrequencyBox t)
    (inverseMultiplier t K)

theorem inverseMultiplier_eq_zero_of_not_mem_frequencyBox {t K : ℕ}
    (ht : 0 < t) {n : ℤ}
    (hn : n ∉ ScalarAtomVariance.scalarFrequencyBox t) :
    inverseMultiplier t K n = 0 := by
  have haway : (2 : ℝ) ^ (t + 1) ≤ |(n : ℝ)| := by
    simp only [ScalarAtomVariance.scalarFrequencyBox, Finset.mem_Icc,
      not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have hcast : (n : ℝ) < -((2 : ℝ) ^ (t + 1)) := by exact_mod_cast hn
      have := neg_le_abs (n : ℝ)
      nlinarith
    · have hcast : (2 : ℝ) ^ (t + 1) < (n : ℝ) := by exact_mod_cast hn
      exact le_trans hcast.le (le_abs_self _)
  have hz : scalarBlock t (n : ℝ) = 0 :=
    ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs t haway
  by_cases hn0 : n = 0
  · simp [inverseMultiplier, hn0]
  · simp [inverseMultiplier, hn0, hz]

theorem inverseMultiplierKernel_coefficient (t K : ℕ) (ht : 0 < t)
    (n : ℤ) :
    fourierCoeff (inverseMultiplierKernel t K) n = inverseMultiplier t K n := by
  apply ScalarKernelL1.polynomialKernel_coefficient_of_support
  intro k hk
  exact inverseMultiplier_eq_zero_of_not_mem_frequencyBox ht hk

/-- The actual finite inverse-multiplier kernel has the profile L1 bound with
the expected scale factor, uniformly over all positive dyadic grades. -/
theorem exists_inverseMultiplierKernel_uniform_L1_bound {K : ℕ}
    (hK : Even K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t : ℕ), 0 < t →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel t K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale t K‖ * L := by
  obtain ⟨L, hL, hbound⟩ := exists_inverseMultiplier_uniform_L1_bound hK
  refine ⟨L, hL, ?_⟩
  intro t ht
  apply hbound t ht
  intro n
  rw [inverseMultiplierKernel_coefficient t K ht n]

/-- The actual scalar block kernel is a finite Fejer mixture whose coefficient
sequence is sampled from one of the two compact profiles above. This exact
representation can be consumed by pointwise convolution inequalities. -/
theorem scalarBlockKernel_eq_fejerMixture (t : ℕ) :
    ∃ J : ℕ, ∃ c : ℕ → ℂ,
      c = (fun k =>
        ((scalarProfileSample (if t = 0 then cutoff else profile 0)
          (if t = 0 then 1 else 2 ^ t) k : ℝ) : ℂ)) ∧
      ScalarKernelL1.scalarBlockKernel t = ScalarKernelL1.fejerMixture J c := by
  let f : ℝ → ℝ := if t = 0 then cutoff else profile 0
  let N : ℕ := if t = 0 then 1 else 2 ^ t
  have hN : 1 ≤ N := by
    dsimp [N]
    split_ifs with ht
    · norm_num
    · exact Nat.one_le_pow t 2 (by omega)
  have hSupport : ∀ y : ℝ, 2 < |y| → f y = 0 := by
    intro y hy
    dsimp [f]
    split_ifs with ht
    · exact cutoff_eq_zero (by linarith)
    · exact profile_eq_zero_of_two_le_abs 0 (by linarith)
  obtain ⟨J, hJlo, hJhi⟩ := exists_scalarProfile_cutoffIndex
    (by norm_num : 0 ≤ (2 : ℝ)) N hN
  let c : ℕ → ℂ := fun k => (scalarProfileSample f N k : ℂ)
  have htail : ∀ k, J ≤ k → c k = 0 := by
    intro k hk
    have hJk : (J : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hz := scalarProfileSample_eq_zero_of_outside hSupport N
      (by exact_mod_cast hN) (lt_of_lt_of_le hJlo hJk)
    simp [c, hz]
  have hcoeff : ∀ k : ℤ,
      fourierCoeff (ScalarKernelL1.scalarBlockKernel t) k = c k.natAbs := by
    intro k
    by_cases ht : t = 0
    · subst t
      rw [ScalarKernelL1.scalarBlockKernel_coefficient, scalarBlock_zero_eq_cutoff_sample]
      simp [c, f, N]
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht
      rw [ScalarKernelL1.scalarBlockKernel_coefficient, scalarBlock_eq_profile_sample _ htpos]
      simp [c, f, N, ht]
  refine ⟨J, c, ?_, ?_⟩
  · funext k
    simp [c, f, N]
  · exact ScalarKernelL1.continuous_eq_fejerMixture
      (ScalarKernelL1.scalarBlockKernel t) J c hcoeff htail

end BrownianSharp

end
