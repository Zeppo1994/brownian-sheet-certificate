import BrownianSharp.SmoothPeriodicConditional
import BrownianSharp.GaussianUniformEvent

/-! Finite good-grid confinement, in the precise form required by Anderson
comparison for every translated periodic path ball. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def smoothGoodUniformEvent (d n : ℕ) (ε : ℝ) : Set (LayerIndex d n → ℝ) :=
  {x | ∀ q : SmoothGoodGrid d n,
    |∑ a, smoothLayerAtom smoothAtom q.val a * x a| ≤ ε}

theorem smoothGoodUniform_confinement_of_ehrhard {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        (smoothGoodUniformEvent d n (smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
              Real.sqrt ((n : ℝ) * hyperbolicCount d n))) ≤
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
  have hsub := smooth_uniform_event_subset_normalized_root_event (by omega : 0 < d) p
    hp2 heven hM hε hthreshold
  exact (measureReal_mono hsub).trans (hroot n hnr)

theorem smoothGoodUniformEvent_mass_lt_one {d n : ℕ} (hd : 0 < d) (ε : ℝ) :
    (productStandardGaussian (LayerIndex d n)).real (smoothGoodUniformEvent d n ε) < 1 := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  have hnz : ∃ q : SmoothGoodGrid d n, ∃ a, smoothLayerAtom smoothAtom q.val a ≠ 0 := by
    by_contra hn
    push_neg at hn
    let q : SmoothGoodGrid d n := Classical.choice inferInstance
    have hv := smoothGoodGrid_variance_pos hd q
    simp only [smoothLayerVariance, hn q, zero_pow (by norm_num : (2:ℕ)≠0), Finset.sum_const_zero] at hv
    exact (lt_irrefl 0 hv)
  exact gaussian_uniform_event_mass_lt_one _ hnz ε

/-- An all-grade form for direct use in the periodic covering obstruction. -/
theorem smoothGoodUniform_confinement_all_grades_of_ehrhard
    (hEhrhard : ProductGaussianEhrhard) {d : ℕ} (hd : 2 ≤ d) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 0 < n →
      (productStandardGaussian (LayerIndex d n)).real
        (smoothGoodUniformEvent d n
          (smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
            Real.sqrt ((n:ℝ)*hyperbolicCount d n))) ≤
      Real.exp (-b*nativeDimension d n) := by
  obtain ⟨N, hN, hbound⟩ := smoothGoodUniform_confinement_of_ehrhard hd
    (fun n => hEhrhard (LayerIndex d n))
  obtain ⟨b, hb, hall⟩ := eventual_exponential_bound_global
    (fun n => (productStandardGaussian (LayerIndex d n)).real
      (smoothGoodUniformEvent d n
        (smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
          Real.sqrt ((n:ℝ)*hyperbolicCount d n))))
    (nativeDimension d) 1 N
    (fun n hn => (by positivity : (0:ℝ)<2^n).trans_le
      (nativeDimension_ge_dyadic d n (by omega)))
    (fun n hn => smoothGoodUniformEvent_mass_lt_one (by omega) _)
    (smoothConfinementExponent_pos d) hbound
  exact ⟨b, hb, fun n hn => hall n (by omega)⟩

end BrownianSharp
