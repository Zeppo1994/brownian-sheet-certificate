import BrownianSharp.AlignmentPeriodicReconstruction
import BrownianSharp.ScalarHighFrequency
import BrownianSharp.ScalarPolynomialKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPeriodicFourierReconstruction
open Torus SmoothResolution AtomicBlockKernelL2 UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierPolynomial_coefficient {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) :
    mFourierCoeff (torusFourierPolynomial S a) k = if k∈S then a k else 0 := by
  classical
  rw [← mFourierCoeff_toLp, ← mFourierBasis_repr,
    AlignmentTrigonometricL2.fourierPolynomial_toLp]
  rw [mFourierBasis.repr_apply_apply, coe_mFourierBasis]
  simp only [inner_sum, inner_smul_right]
  simp_rw [orthonormal_iff_ite.mp orthonormal_mFourier]
  simp

def fourierCoefficientCLM {d : ℕ} (k : Fin d → ℤ) :
    C(UnitAddTorus (Fin d), ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (mFourierLp 2 k)).comp (ContinuousMap.toLp 2 volume ℂ)

theorem fourierCoefficientCLM_apply {d : ℕ} (k : Fin d → ℤ)
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    fourierCoefficientCLM k f = mFourierCoeff f k := by
  change inner ℂ (mFourierLp 2 k) (f.toLp 2 volume ℂ) = _
  rw [← coe_mFourierBasis, ← mFourierBasis.repr_apply_apply,
    mFourierBasis_repr, mFourierCoeff_toLp]

theorem tensorMultiplier_eq_zero_outside_box {d : ℕ} (s : Fin d → ℕ)
    (k : Fin d → ℤ) (hk : k∉frequencyBox s) : tensorMultiplier s k = 0 := by
  classical
  have hnot : ¬∀ i, k i ∈ Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1)) := by
    simpa only [frequencyBox, Fintype.mem_piFinset] using hk
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hout : (2:ℝ)^(s i+1) ≤ |(k i:ℝ)| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · have h : (k i:ℝ) < -((2:ℝ)^(s i+1)) := by exact_mod_cast hi
      exact (by linarith : (2:ℝ)^(s i+1) ≤ -(k i:ℝ)).trans (neg_le_abs _)
    · have h : (2:ℝ)^(s i+1) < (k i:ℝ) := by exact_mod_cast hi
      exact h.le.trans (le_abs_self _)
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (ScalarKernelL1.scalarBlock_eq_zero_of_two_pow_le_abs (s i) hout)

theorem block_coefficient {d : ℕ} (s : Fin d → ℕ) (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    mFourierCoeff (block s f) k =
      (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k := by
  rw [block, fourierPolynomial_coefficient]
  split_ifs with hk
  · rfl
  · rw [tensorMultiplier_eq_zero_outside_box s k hk]
    simp

theorem tensorMultiplier_hasSum {d : ℕ} (k : Fin d → ℤ) :
    HasSum (fun s : Fin d → ℕ => tensorMultiplier s k) 1 := by
  classical
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hall : ∀ᶠ N : ℕ in Filter.atTop, ∀ i, |(k i:ℝ)| ≤ (2:ℝ)^N :=
    Filter.eventually_all.mpr (fun i => hp.eventually_ge_atTop _)
  obtain ⟨N,hN⟩ := hall.exists
  let S := Fintype.piFinset (fun _ : Fin d => Finset.range (N+1))
  have hzero : ∀ s ∉ S, tensorMultiplier s k = 0 := by
    intro s hs
    have hnot : ¬∀ i, s i∈Finset.range (N+1) := by simpa [S] using hs
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hsi : N+1 ≤ s i := by simpa only [Finset.mem_range, not_lt] using hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ScalarHighFrequency.scalarBlock_eq_zero_of_abs_le_lower (s i) (by omega)
      ((hN i).trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hsum : ∑ s ∈ S, tensorMultiplier s k = 1 := by
    unfold S tensorMultiplier
    rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.range (N+1))
      (fun i n => scalarBlock n (k i))]
    have hi : ∀ i, ∑ t ∈ Finset.range (N+1), scalarBlock t (k i) = 1 := by
      intro i
      rw [scalarBlock_sum]
      apply cutoff_eq_one
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<2^N)]
      exact (div_le_one₀ (by positivity)).2 (hN i)
    simp_rw [hi]
    simp
  simpa only [hsum] using hasSum_sum_of_ne_finset_zero hzero

/-- Uniform reconstruction from the literal smooth dyadic blocks. This
establishes the function-space identification needed by the width proof. -/
theorem nikolsky_two_blocks_hasSum {d : ℕ} (r : ℝ) (hr : 1/2<r)
    (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f) :
    HasSum (fun s : Fin d → ℕ => block s f) (complexifyContinuous f) := by
  have hs := AlignmentPeriodicReconstruction.nikolsky_two_blocks_summable r hr f hf
  have hcoeff : ∀ k, mFourierCoeff ((∑' s, block s f) : C(UnitAddTorus (Fin d), ℂ)) k =
      mFourierCoeff (complexifyContinuous f) k := by
    intro k
    have h1 := (fourierCoefficientCLM k).hasSum hs.hasSum
    have h2 := (Complex.ofRealCLM.hasSum (tensorMultiplier_hasSum k)).mul_right
      (realPeriodicFourierCoeff f k)
    simp only [fourierCoefficientCLM_apply, block_coefficient] at h1
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h2
    exact h1.unique h2
  have hLp : (∑' s, block s f).toLp 2 volume ℂ =
      (complexifyContinuous f).toLp 2 volume ℂ := by
    apply mFourierBasis.repr.injective
    ext k
    simp only [mFourierBasis_repr, mFourierCoeff_toLp]
    exact hcoeff k
  have heq : (∑' s, block s f) = complexifyContinuous f :=
    ContinuousMap.toLp_injective volume hLp
  simpa only [heq] using hs.hasSum

theorem sobolev_two_blocks_hasSum {d : ℕ} (r : ℝ) (hr : 1/2<r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    HasSum (fun s : Fin d → ℕ => block s f) (complexifyContinuous f) :=
  nikolsky_two_blocks_hasSum r hr f
    (AlignmentPeriodicEnergy.sobolev_two_subset_nikolsky_two r f hf)

end BrownianSharp.AlignmentPeriodicFourierReconstruction
