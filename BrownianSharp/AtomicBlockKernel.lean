import BrownianSharp.AtomicBlockVariance
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Finite multiplier kernels for the smooth resolution.  This file records the
exact convolution identity before the L² estimates are added.  In particular,
no asymptotic kernel bound is assumed or claimed here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AtomicBlockKernel
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open UnitAddTorus

/-- The finite torus kernel associated to the actual smooth tensor multiplier. -/
def kernel {d : ℕ} (s : Fin d → ℕ) : C(UnitAddTorus (Fin d), ℂ) :=
  ∑ k ∈ frequencyBox s,
    (tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k

private theorem integrable_kernel_term {d : ℕ} (s : Fin d → ℕ)
    (k : Fin d → ℤ) (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) * (f y : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
      ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) * (f y : ℂ)) := by
    fun_prop
  have hbound : ∀ y, ‖((tensorMultiplier s k : ℂ) •
      UnitAddTorus.mFourier k (x - y)) * (f y : ℂ)‖ ≤
      ‖(tensorMultiplier s k : ℂ)‖ * ‖f‖ := by
    intro y
    rw [norm_mul, norm_smul]
    have hm : ‖UnitAddTorus.mFourier k (x - y)‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k (x - y)‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          (UnitAddTorus.mFourier k).norm_coe_le_norm _
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖(f y : ℂ)‖ ≤ ‖f‖ := by simpa using f.norm_coe_le_norm y
    calc
      ‖(tensorMultiplier s k : ℂ)‖ * ‖UnitAddTorus.mFourier k (x - y)‖ * ‖(f y : ℂ)‖
          ≤ ‖(tensorMultiplier s k : ℂ)‖ * 1 * ‖f‖ := by
            gcongr
      _ = ‖(tensorMultiplier s k : ℂ)‖ * ‖f‖ := by ring
  exact Integrable.of_bound hc.aestronglyMeasurable
    (‖(tensorMultiplier s k : ℂ)‖ * ‖f‖) (ae_of_all _ hbound)

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  classical
  have hcoord : ∀ i : Fin d,
      fourier (k i) ((x - y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

/-- Evaluation of the finite smooth block is convolution by its finite multiplier
kernel. This is the structural identity needed for localized-atom estimates. -/
theorem block_eq_kernelSum_integral {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    BrownianSharp.SmoothResolution.block s f x =
      ∫ y : UnitAddTorus (Fin d),
        (∑ k ∈ frequencyBox s,
          ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) * (f y : ℂ))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  unfold BrownianSharp.SmoothResolution.block BrownianSharp.Torus.torusFourierPolynomial
    BrownianSharp.Torus.realPeriodicFourierCoeff BrownianSharp.Torus.complexifyRealPeriodic
    UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul,
    Finset.sum_apply]
  calc
    _ = ∑ k ∈ frequencyBox s,
        (tensorMultiplier s k : ℂ) *
          UnitAddTorus.mFourierCoeff (BrownianSharp.Torus.complexifyRealPeriodic f) k *
            UnitAddTorus.mFourier k x := by
              rfl
    _ = ∑ k ∈ frequencyBox s,
        ∫ y : UnitAddTorus (Fin d),
          ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) * (f y : ℂ)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [show (fun y : UnitAddTorus (Fin d) =>
                ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) *
                  (f y : ℂ)) = fun y =>
                    ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x) *
                      (UnitAddTorus.mFourier (-k) y * (f y : ℂ)) by
                  funext y
                  rw [smul_eq_mul, mFourier_sub_mul]
                  ring]
            change (tensorMultiplier s k : ℂ) *
                UnitAddTorus.mFourierCoeff
                  (BrownianSharp.Torus.complexifyRealPeriodic f) k *
                  UnitAddTorus.mFourier k x = _
            rw [UnitAddTorus.mFourierCoeff]
            simp only [BrownianSharp.Torus.complexifyRealPeriodic, smul_eq_mul]
            calc
              (tensorMultiplier s k : ℂ) *
                  (∫ y : UnitAddTorus (Fin d),
                    UnitAddTorus.mFourier (-k) y * (f y : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) *
                  UnitAddTorus.mFourier k x =
                  ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x) *
                  ∫ y, UnitAddTorus.mFourier (-k) y * (f y : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                      ring
              _ = ∫ y, ((tensorMultiplier s k : ℂ) * UnitAddTorus.mFourier k x) *
                  (UnitAddTorus.mFourier (-k) y * (f y : ℂ))
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                    rw [integral_const_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        ∑ k ∈ frequencyBox s,
          ((tensorMultiplier s k : ℂ) • UnitAddTorus.mFourier k (x - y)) * (f y : ℂ)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            symm
            apply integral_finsetSum
            intro k hk
            exact integrable_kernel_term s k f x

end BrownianSharp.AtomicBlockKernel
