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

/-- The evaluation functional at `x` represented by its conjugate Fourier
kernel in torus `L²`. -/
def evaluationKernelLp {d : ℕ} (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) :=
  ∑ k ∈ frequencyBox s,
    star ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x) •
      UnitAddTorus.mFourierLp 2 k

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

theorem tensorMultiplier_abs_le_one {d : ℕ} (s : Fin d → ℕ)
    (k : Fin d → ℤ) : |tensorMultiplier s k| ≤ 1 := by
  unfold tensorMultiplier
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    exact scalarBlock_abs_le_one (s i) (k i)

/-- Exact finite kernel energy is at most the number of retained frequencies. -/
theorem kernelLp_norm_sq_le_card {d : ℕ} (s : Fin d → ℕ) :
    ‖kernelLp s‖ ^ 2 ≤ (frequencyBox s).card := by
  rw [kernelLp_norm_sq]
  calc
    ∑ k ∈ frequencyBox s, ‖(tensorMultiplier s k : ℂ)‖ ^ 2 ≤
        ∑ _k ∈ frequencyBox s, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have h := tensorMultiplier_abs_le_one s k
          have hn : ‖(tensorMultiplier s k : ℂ)‖ ≤ 1 := by
            calc
              ‖(tensorMultiplier s k : ℂ)‖ = |tensorMultiplier s k| :=
                RCLike.norm_ofReal _
              _ ≤ 1 := h
          have hprod := mul_nonneg (sub_nonneg.mpr hn)
            (show 0 ≤ 1 + ‖(tensorMultiplier s k : ℂ)‖ by positivity)
          nlinarith [sq_nonneg (‖(tensorMultiplier s k : ℂ)‖)]
    _ = (frequencyBox s).card := by simp

theorem evaluationKernelLp_norm_sq_le_card {d : ℕ} (s : Fin d → ℕ)
    (x : UnitAddTorus (Fin d)) :
    ‖evaluationKernelLp s x‖ ^ 2 ≤ (frequencyBox s).card := by
  rw [evaluationKernelLp, norm_sq_orthonormal_finset_sum
    (fun k : Fin d → ℤ => UnitAddTorus.mFourierLp (d := Fin d) 2 k)
    UnitAddTorus.orthonormal_mFourier (frequencyBox s)
    (fun k => star ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x))]
  calc
    ∑ k ∈ frequencyBox s,
        ‖star ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x)‖ ^ 2 ≤
      ∑ _k ∈ frequencyBox s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hmult : ‖(tensorMultiplier s k : ℂ)‖ ≤ 1 := by
          calc
            ‖(tensorMultiplier s k : ℂ)‖ = |tensorMultiplier s k| :=
              RCLike.norm_ofReal _
            _ ≤ 1 := tensorMultiplier_abs_le_one s k
        have hchar : ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
          calc
            ‖UnitAddTorus.mFourier k x‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
              (UnitAddTorus.mFourier k).norm_coe_le_norm x
            _ = 1 := UnitAddTorus.mFourier_norm
        have hcoef : ‖star ((tensorMultiplier s k : ℂ) *
            UnitAddTorus.mFourier k x)‖ ≤ 1 := by
          rw [norm_star, norm_mul]
          calc
            ‖(tensorMultiplier s k : ℂ)‖ * ‖UnitAddTorus.mFourier k x‖ ≤ 1 * 1 :=
              mul_le_mul hmult hchar (norm_nonneg _) (by norm_num)
            _ = 1 := by ring
        have hprod := mul_nonneg (sub_nonneg.mpr hcoef)
          (by positivity : 0 ≤ 1 + ‖star ((tensorMultiplier s k : ℂ) *
            UnitAddTorus.mFourier k x)‖)
        nlinarith
    _ = (frequencyBox s).card := by simp

/-- The smooth Fourier-block evaluation is the `L²` inner product of its
evaluation kernel with the input function. -/
theorem block_eq_inner_evaluationKernelLp {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    inner ℂ (evaluationKernelLp s x) ((complexifyContinuous f).toLp (2 : ℝ≥0∞)
      (volume : Measure (UnitAddTorus (Fin d))) ℂ) =
        BrownianSharp.SmoothResolution.block s f x := by
  classical
  unfold evaluationKernelLp BrownianSharp.SmoothResolution.block
    BrownianSharp.Torus.torusFourierPolynomial
  simp only [sum_inner, inner_smul_left]
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hrepr := UnitAddTorus.mFourierBasis_repr
    ((complexifyContinuous f).toLp (2 : ℝ≥0∞)
      (volume : Measure (UnitAddTorus (Fin d))) ℂ) k
  rw [UnitAddTorus.mFourierBasis.repr_apply_apply] at hrepr
  rw [UnitAddTorus.mFourierCoeff_toLp] at hrepr
  rw [UnitAddTorus.coe_mFourierBasis] at hrepr
  change star (star ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x)) *
      inner ℂ (UnitAddTorus.mFourierLp 2 k)
        ((complexifyContinuous f).toLp (2 : ℝ≥0∞)
          (volume : Measure (UnitAddTorus (Fin d))) ℂ) = _
  rw [hrepr]
  have hcoeff : UnitAddTorus.mFourierCoeff
      (fun y : UnitAddTorus (Fin d) => (f y : ℂ)) k =
      BrownianSharp.Torus.realPeriodicFourierCoeff f k := rfl
  change star (star ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x)) *
    UnitAddTorus.mFourierCoeff (fun y : UnitAddTorus (Fin d) => (f y : ℂ)) k = _
  rw [hcoeff]
  simp only [star_star]
  change (tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x *
      BrownianSharp.Torus.realPeriodicFourierCoeff f k =
    ((tensorMultiplier s k : ℂ) * BrownianSharp.Torus.realPeriodicFourierCoeff f k) *
      UnitAddTorus.mFourier k x
  ring

end BrownianSharp.AtomicBlockKernelL2
