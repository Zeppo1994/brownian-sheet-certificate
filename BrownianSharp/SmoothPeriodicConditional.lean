import BrownianSharp.SmoothConditional
import BrownianSharp.PeriodicNativeGrid

/-! The conditional smooth-grid confinement event is inherited by the full
finite periodic synthesis because its midpoint samples are exactly the rows
used in the covariance proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open BrownianSharp.Torus

/-- Finite periodic synthesis from the independent layer coordinates. -/
def smoothPeriodicSynthesis {d n : ℕ} (x : LayerIndex d n → ℝ)
    (z : UnitAddTorus (Fin d)) : ℝ :=
  ∑ a : LayerIndex d n, x a • periodicNativeAtom a z

theorem smoothPeriodicSynthesis_midpoint_eq {d n : ℕ}
    (x : LayerIndex d n → ℝ) (q : MidpointGridIndex d n) :
    smoothPeriodicSynthesis x (periodicMidpoint q) =
      ∑ a : LayerIndex d n, smoothLayerAtom smoothAtom q a * x a := by
  unfold smoothPeriodicSynthesis
  simp_rw [periodicNativeAtom_midpoint_eq, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem smoothPeriodic_uniform_event_subset_root_event {d n p : ℕ}
    (hd : 0 < d) (hp : 2 ≤ p) (heven : Even p)
    (hM : 0 < standardGaussianMoment p) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hthreshold : ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2) ≤
      (1 / 4 : ℝ) * (standardGaussianMoment p) ^ (1 / (p : ℝ))) :
    {x : LayerIndex d n → ℝ | ∀ z : UnitAddTorus (Fin d),
      |smoothPeriodicSynthesis x z| ≤ ε} ⊆
    {x | smoothGoodRootStatistic d n p x ≤ 1 / 4} := by
  have hrows :
      {x : LayerIndex d n → ℝ | ∀ q : SmoothGoodGrid d n,
        |∑ a : LayerIndex d n, smoothLayerAtom smoothAtom q.1 a * x a| ≤ ε} ⊆
      {x | smoothGoodRootStatistic d n p x ≤ 1 / 4} :=
    smooth_uniform_event_subset_normalized_root_event hd p hp heven hM hε hthreshold
  intro x hx
  apply hrows
  intro q
  have h := hx (periodicMidpoint q.1)
  rw [smoothPeriodicSynthesis_midpoint_eq] at h
  exact h

/-- Radius scale for the smooth plateau layer. Its variance floor is of order
`S_n`, with no dyadic `2^-n` factor in the atom amplitude. -/
def smoothPeriodicRadiusConstant (d : ℕ) (κ : ℝ) : ℝ :=
  Real.sqrt κ / (16 * (2 : ℝ) ^ (d + 1))

theorem smoothPeriodicRadiusConstant_pos (d : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < smoothPeriodicRadiusConstant d κ := by
  unfold smoothPeriodicRadiusConstant
  positivity

theorem smoothPeriodicRadius_threshold {d n p : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hp : 2 ≤ p) (heven : Even p) {κ : ℝ} (hκ : 0 < κ)
    (hpLower : κ * (n : ℝ) ≤ 2 * (p : ℝ)) :
    (smoothPeriodicRadiusConstant d κ *
      Real.sqrt ((n : ℝ) * hyperbolicCount d n)) /
        Real.sqrt (smoothVarianceMeanLowerBound d n / 2) ≤
      (1 / 4 : ℝ) * (standardGaussianMoment p) ^ (1 / (p : ℝ)) := by
  have hS : 0 < hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hfloor : smoothVarianceMeanLowerBound d n / 2 =
      hyperbolicCount d n / (2 : ℝ) ^ (d + 1) := by
    unfold smoothVarianceMeanLowerBound hyperbolicCount
    rw [show (1 / 2 : ℝ) ^ d = ((2 : ℝ) ^ d)⁻¹ by
      rw [one_div, inv_pow]]
    rw [show (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d by rw [pow_succ]; ring]
    field_simp
    <;> ring
  have hv : 0 < smoothVarianceMeanLowerBound d n / 2 := by rw [hfloor]; positivity
  have hsq :
      (smoothPeriodicRadiusConstant d κ * Real.sqrt ((n : ℝ) * hyperbolicCount d n) /
        Real.sqrt (smoothVarianceMeanLowerBound d n / 2)) ^ 2 ≤
      ((1 / 4 : ℝ) * Real.sqrt (p : ℝ) / 2) ^ 2 := by
    rw [hfloor, smoothPeriodicRadiusConstant, div_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) * hyperbolicCount d n),
      Real.sq_sqrt (by positivity : 0 ≤ hyperbolicCount d n /
        (2 : ℝ) ^ (d + 1))]
    field_simp
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
    nlinarith [Real.sq_sqrt hκ.le,
      Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)), hpLower, hpow]
  have hL : 0 ≤ smoothPeriodicRadiusConstant d κ *
      Real.sqrt ((n : ℝ) * hyperbolicCount d n) /
        Real.sqrt (smoothVarianceMeanLowerBound d n / 2) :=
    div_nonneg (mul_nonneg (smoothPeriodicRadiusConstant_pos d hκ).le
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hR : 0 ≤ (1 / 4 : ℝ) * Real.sqrt (p : ℝ) / 2 := by positivity
  have hratio : smoothPeriodicRadiusConstant d κ *
      Real.sqrt ((n : ℝ) * hyperbolicCount d n) /
        Real.sqrt (smoothVarianceMeanLowerBound d n / 2) ≤
      (1 / 4 : ℝ) * Real.sqrt (p : ℝ) / 2 := by nlinarith [hsq]
  calc
    _ ≤ (1 / 4 : ℝ) * Real.sqrt (p : ℝ) / 2 := hratio
    _ ≤ (1 / 4 : ℝ) * (standardGaussianMoment p) ^ (1 / (p : ℝ)) := by
      have hmoment := standardGaussianMoment_evenOrder_root_lower heven hp
      have : Real.sqrt (p : ℝ) / 2 ≤
          (standardGaussianMoment p) ^ (1 / (p : ℝ)) := by
        simpa [Real.rpow_eq_pow, one_div] using hmoment
      nlinarith

theorem smoothPeriodic_uniform_confinement_of_ehrhard {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | ∀ z : UnitAddTorus (Fin d),
          |smoothPeriodicSynthesis x z| ≤
            smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
              Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
      Real.exp (-smoothConfinementExponent d * nativeDimension d n) := by
  obtain ⟨Nr, hNr, hroot⟩ := smoothGoodRoot_confinement_of_ehrhard hd hEhrhard
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds (smoothMomentSlope_pos d)
  let N := max Nr Np
  refine ⟨N, hNr.trans (le_max_left _ _), ?_⟩
  intro n hnN
  have hnr : Nr ≤ n := (le_max_left _ _).trans hnN
  have hnp : Np ≤ n := (le_max_right _ _).trans hnN
  have hn : 0 < n := by
    have hnd : 2 * d ≤ n := hNr.trans hnr
    omega
  obtain ⟨_, hpLower, hp2⟩ := hNp n hnp
  let p := gradeEvenPower (smoothMomentSlope d) n
  have heven : Even p := gradeEvenPower_even _ _
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    have hpk : p = 2 * k := by omega
    rw [hpk]
    exact standardGaussianMoment_even_pos k
  have hε : 0 ≤ smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
      Real.sqrt ((n : ℝ) * hyperbolicCount d n) :=
    mul_nonneg (smoothPeriodicRadiusConstant_pos d (smoothMomentSlope_pos d)).le
      (Real.sqrt_nonneg _)
  have hpLower' : smoothMomentSlope d * (n : ℝ) ≤ 2 * (p : ℝ) := by
    have hnR : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hstep := mul_le_mul_of_nonneg_left hnR (smoothMomentSlope_pos d).le
    dsimp [p] at hpLower ⊢
    nlinarith
  have hthreshold := smoothPeriodicRadius_threshold hd hn hp2 heven
    (smoothMomentSlope_pos d) hpLower'
  have hsub := smoothPeriodic_uniform_event_subset_root_event (by omega : 0 < d)
    hp2 heven hM hε hthreshold
  exact (measureReal_mono hsub).trans (hroot n hnr)

end BrownianSharp
