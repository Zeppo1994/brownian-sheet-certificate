import BrownianSharp.UniformSharpStatement
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.NativeConditional
import BrownianSharp.ScaleClosure

/-! Dimension-uniform constants for the literal Brownian-sheet event. All
scale constants are chosen before the probability-space realization; the
only random-object-dependent step is the already-proved projection comparison.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp
open HaarQuarter

/-- A uniform version of the discrete native-layer estimate. Its constants
are selected solely from `d`; the estimate then holds for every realization. -/
theorem uniformDiscreteSheetBound_of_productGaussianEhrhard
    (hEhrhard : ProductGaussianEhrhard) :
    ∀ d : ℕ, 2 ≤ d → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, 2 * d ≤ N ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : BrownianSheetOnCube d Ω P) (n : ℕ), N ≤ n →
        P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n} ≤
          Real.exp (-b * nativeDimension d n) := by
  intro d hd
  have hκ := nativeMomentSlope_pos d
  obtain ⟨Nr, hNr, hroot⟩ := nativeGoodRoot_confinement_of_ehrhard hd
    (fun n => hEhrhard (LayerIndex d n))
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds hκ
  let N := max Nr Np
  refine ⟨nativeRadiusConstant d (1 / 2) (nativeMomentSlope d),
    nativeConfinementExponent d,
    nativeRadiusConstant_pos d (by norm_num) hκ,
    nativeConfinementExponent_pos d, N, hNr.trans (le_max_left _ _), ?_⟩
  intro Ω _ P _ B n hnN
  have hnr : Nr ≤ n := (le_max_left _ _).trans hnN
  have hnp : Np ≤ n := (le_max_right _ _).trans hnN
  obtain ⟨_, hpLower, hp2⟩ := hNp n hnp
  let p := gradeEvenPower (nativeMomentSlope d) n
  have heven : Even p := gradeEvenPower_even _ _
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    have hpk : p = 2 * k := by omega
    rw [hpk]
    exact standardGaussianMoment_even_pos k
  have hn : 0 < n := by
    have : 2 * d ≤ n := hNr.trans hnr
    omega
  apply original_sheet_sharpRadius_bound_of_native_root_bound B hd hn hp2 heven
    (by norm_num : (0 : ℝ) < 1 / 2) hκ hM
  · nlinarith [hpLower]
  · simpa only [Real.rpow_eq_pow, one_div, div_eq_mul_inv, mul_comm,
      one_mul, mul_one, p] using standardGaussianMoment_evenOrder_root_lower heven hp2
  · exact hroot n hnr

/-- Uniform scale closure for all realizations of the original sheet. -/
theorem uniformSharpLog_of_uniformDiscreteSheetBound
    (hDiscrete : ∀ d : ℕ, 2 ≤ d → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ N : ℕ, 2 * d ≤ N ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : BrownianSheetOnCube d Ω P) (n : ℕ), N ≤ n →
          P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n} ≤
            Real.exp (-b * nativeDimension d n)) :
    UniformSharpLogStatement := by
  intro d hd
  obtain ⟨a, b, ha, hb, N, hN, hdiscrete⟩ := hDiscrete d hd
  let c : ℝ := ((a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2) * b /
      (2 * (1 + |Real.log a|) ^ (2 * (d - 1) + 1)))
  let ε₀ : ℝ := min (sharpRadius d a N) (Real.exp (-2))
  have hc : 0 < c := by dsimp [c]; positivity
  have hNpos : 0 < N := by omega
  have hRadius : 0 < sharpRadius d a N := sharpRadius_pos hd ha hNpos
  have hε₀ : 0 < ε₀ := lt_min hRadius (Real.exp_pos _)
  have hε₀bound : ε₀ < Real.exp (-1) :=
    (min_le_right _ _).trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  refine ⟨c, ε₀, hc, hε₀, hε₀bound, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  have hεle1 : ε ≤ 1 := by
    have hexp : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact hsmall.trans ((min_le_right _ _).trans hexp)
  have hεN : ε ≤ sharpRadius d a N := hsmall.trans (min_le_left _ _)
  have hscale : ∀ n : ℕ, (N : ℝ) ≤ n →
      b * nativeDimension d n ≤
        -Real.log (P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n}) := by
    intro n hn
    have hnNat : N ≤ n := by exact_mod_cast hn
    have hrpos := sharpRadius_pos hd ha (lt_of_lt_of_le hNpos hnNat)
    have hp := B.smallBall_probability_pos hrpos
    have hlog := Real.log_le_log hp (hdiscrete Ω P B n hnNat)
    rw [Real.log_exp] at hlog
    linarith
  have hresult := discrete_bound_implies_sharp
    (fun r => -Real.log (P.real {ω | ‖B.path ω‖ ≤ r})) hd hN ha hb
    hscale (fun _ _ hx hxy => smallBall_profile_antitone B hx hxy)
    hε hεle1 hεN
  have hexponent : 2 * (d - 1) + 1 = 2 * d - 1 := by omega
  simpa [c, sharpRate, hexponent, mul_assoc] using hresult

theorem uniformSharpLog_certified : UniformSharpLogStatement :=
  uniformSharpLog_of_uniformDiscreteSheetBound
    (uniformDiscreteSheetBound_of_productGaussianEhrhard productGaussianEhrhard_certified)

theorem uniformSharpProbability_certified : UniformSharpProbabilityStatement :=
  uniformSharp_statements_iff.mpr uniformSharpLog_certified

end BrownianSharp

end
