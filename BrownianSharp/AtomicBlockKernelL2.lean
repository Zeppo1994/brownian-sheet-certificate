import BrownianSharp.AtomicBlockKernel
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! Exact finite Fourier-kernel energy from orthogonality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernel
open UnitAddTorus

def complexifyContinuous {d : ℕ} (f : RealPeriodic d) :
    C(UnitAddTorus (Fin d), ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

theorem norm_sq_orthonormal_finset_sum {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (hv : Orthonormal ℂ v) (S : Finset ι) (c : ι → ℂ) :
    ‖∑ i ∈ S, c i • v i‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ E _ _ _]
  simp only [sum_inner, inner_smul_left]
  change Complex.re (∑ i ∈ S,
    star (c i) * inner ℂ (v i) (∑ j ∈ S, c j • v j)) = _
  rw [Complex.re_sum]
  calc
    (∑ i ∈ S, Complex.re (star (c i) * inner ℂ (v i) (∑ j ∈ S, c j • v j))) =
        ∑ i ∈ S, Complex.re (star (c i) * c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hv.inner_right_sum c hi]
    _ = ∑ i ∈ S, ‖c i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Complex.mul_conj, pow_two]

/-- Finite multiplier kernel as an `L²` trigonometric polynomial. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Fact (0 < (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

def kernelLp {d : ℕ} (s : Fin d → ℕ) : Lp ℂ (2 : ℝ≥0∞)
    (volume : Measure (UnitAddTorus (Fin d))) :=
  ∑ k ∈ frequencyBox s,
    (tensorMultiplier s k : ℂ) • UnitAddTorus.mFourierLp 2 k

/-- Parseval's exact identity for the actual smooth-resolution multiplier
kernel; the bound by the frequency-box cardinal follows immediately. -/
theorem kernelLp_norm_sq {d : ℕ} (s : Fin d → ℕ) :
    ‖kernelLp s‖ ^ 2 =
      ∑ k ∈ frequencyBox s, ‖(tensorMultiplier s k : ℂ)‖ ^ 2 := by
  unfold kernelLp
  exact norm_sq_orthonormal_finset_sum (fun k : Fin d → ℤ =>
    UnitAddTorus.mFourierLp (d := Fin d) (2 : ℝ≥0∞) k)
    UnitAddTorus.orthonormal_mFourier (frequencyBox s)
    (fun k => (tensorMultiplier s k : ℂ))

theorem scalarBlock_abs_le_one (n : ℕ) (ξ : ℝ) :
    |scalarBlock n ξ| ≤ 1 := by
  unfold scalarBlock
  split_ifs with hn
  · rw [abs_of_nonneg (cutoff_bounds ξ).1]
    exact (cutoff_bounds ξ).2
  · have h₁ := cutoff_bounds (ξ / (2 : ℝ) ^ n)
    have h₂ := cutoff_bounds (ξ / (2 : ℝ) ^ (n - 1))
    rw [abs_le]
    constructor <;> linarith

end BrownianSharp.AtomicBlockKernelL2
