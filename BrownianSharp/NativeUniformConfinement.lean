import BrownianSharp.NativeConditional
import BrownianSharp.CameronMartinCover

/-! Actual native Gaussian grid confinement, independent of the full-sheet
comparison, for the Cameron--Martin entropy application. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

/-- The literal unnormalized native coefficient field on its deterministic
good midpoint grid. -/
def nativeGoodUniformEvent (d n : ℕ) (ε : ℝ) : Set (LayerIndex d n → ℝ) :=
  {x | ∀ q : NativeGoodGrid d n,
    |∑ a, nativeLayerRowCoefficient q.val a * x a| ≤ ε}

/-- Both the native field and its entire confinement scale are actual objects;
the only premise remaining is finite-dimensional Gaussian Ehrhard. -/
theorem nativeGoodUniform_confinement_of_ehrhard (hEhrhard : ProductGaussianEhrhard)
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, 2*d ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        (nativeGoodUniformEvent d n
          (sharpRadius d (nativeRadiusConstant d (1/2) (nativeMomentSlope d)) n)) ≤
      Real.exp (-nativeConfinementExponent d * nativeDimension d n) := by
  obtain ⟨Nr, hNr, hroot⟩ := nativeGoodRoot_confinement_of_ehrhard hd
    (fun n => hEhrhard (LayerIndex d n))
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds (nativeMomentSlope_pos d)
  refine ⟨max Nr Np, hNr.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnr : Nr ≤ n := (le_max_left _ _).trans hn
  have hnp : Np ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by have h := hNr.trans hnr; omega
  obtain ⟨_, hpLower, hp2⟩ := hNp n hnp
  let p := gradeEvenPower (nativeMomentSlope d) n
  have heven : Even p := gradeEvenPower_even (nativeMomentSlope d) n
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    rw [show p=2*k by omega]
    exact standardGaussianMoment_even_pos k
  have hmoment : (1/2:ℝ)*Real.sqrt (p:ℝ) ≤ standardGaussianMoment p ^ (1/(p:ℝ)) :=
    by simpa only [Real.rpow_eq_pow, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one, p] using
      standardGaussianMoment_evenOrder_root_lower heven hp2
  have hthreshold := native_sharpRadius_standardized_threshold hd hn0 hp2
    (show (0:ℝ)<1/2 by norm_num) (nativeMomentSlope_pos d) (by nlinarith [hpLower]) hmoment
  have hε : 0 ≤ sharpRadius d (nativeRadiusConstant d (1/2) (nativeMomentSlope d)) n :=
    (sharpRadius_pos hd (nativeRadiusConstant_pos d (by norm_num) (nativeMomentSlope_pos d)) hn0).le
  letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0<d)
  have hsub := native_uniform_event_subset_normalized_root_event
    (fun q : NativeGoodGrid d n => q.val) p hp2 heven hM
    (half_pos (nativeVarianceMeanLowerBound_pos (by omega : 0<d)))
    (fun q => q.property) hε hthreshold
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  exact hroot n hnr

end BrownianSharp
