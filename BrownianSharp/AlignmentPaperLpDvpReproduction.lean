import BrownianSharp.AlignmentPaperLpDvpGrid
import BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.AlignmentPaperTorusTranslation
import Mathlib.MeasureTheory.Integral.Pi

/-! Reproduction by the tensor product of the actual de la Vallée-Poussin
kernels, with independent coordinate bandwidths. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperLpDvpReproduction

open BrownianSharp.Torus
open BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
open BrownianSharp.AlignmentPaperLpDvpGrid
open HaarQuarter.TheoremD.FejerFourier
open UnitAddTorus

def tensorDvpKernel {d : ℕ} (N : Fin d → ℕ) : C(UnitAddTorus (Fin d), ℂ) :=
  BrownianSharp.coordinateProductKernel
    (fun i => deLaValleePoussinCircleKernel (N i))

/-- Coordinatewise midpoint grid on the unit torus, at the prescribed
bandwidths. -/
def midpointTorusGridPoint {d : ℕ} (N : Fin d → ℕ)
    (j : ∀ i, Fin (N i)) : UnitAddTorus (Fin d) :=
  fun i => ((((j i).val : ℝ) + 1 / 2) / (N i : ℝ) : UnitAddCircle)

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x-y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  have hcoord : ∀ i : Fin d,
      fourier (k i) ((x-y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem tensor_dvp_mode_convolution {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ i, 0 < N i) (k : Fin d → ℤ)
    (hk : ∀ i, (k i).natAbs ≤ N i) (x : UnitAddTorus (Fin d)) :
    (∫ y : UnitAddTorus (Fin d), tensorDvpKernel N y *
      UnitAddTorus.mFourier k (x-y)
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      UnitAddTorus.mFourier k x := by
  let K := tensorDvpKernel N
  have hterm (y : UnitAddTorus (Fin d)) :
      K y * UnitAddTorus.mFourier k (x-y) =
        UnitAddTorus.mFourier k x *
          ∏ i : Fin d,
            (deLaValleePoussinCircleKernel (N i) (y i) * fourier (-(k i)) (y i)) := by
    change
      (∏ i : Fin d, deLaValleePoussinCircleKernel (N i) (y i)) *
          UnitAddTorus.mFourier k (x-y) = _
    rw [mFourier_sub_mul]
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
  have hprodint :
      (∫ y : UnitAddTorus (Fin d),
        ∏ i : Fin d,
          (deLaValleePoussinCircleKernel (N i) (y i) * fourier (-(k i)) (y i))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∏ i : Fin d, fourierCoeff (T := (1 : ℝ))
        (deLaValleePoussinCircleKernel (N i)) (k i) := by
    change (∫ y : (Fin d → UnitAddCircle),
        ∏ i : Fin d,
          (deLaValleePoussinCircleKernel (N i) (y i) *
            fourier (-(k i)) (y i))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) = _
    calc
      _ = ∏ i : Fin d, ∫ y : UnitAddCircle,
          deLaValleePoussinCircleKernel (N i) y * fourier (-(k i)) y
          ∂AddCircle.haarAddCircle :=
        MeasureTheory.integral_fintype_prod_eq_prod _
      _ = ∏ i : Fin d, fourierCoeff (T := (1 : ℝ))
          (deLaValleePoussinCircleKernel (N i)) (k i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [fourierCoeff, smul_eq_mul, mul_comm]
  have hcoeff :
      ∏ i : Fin d, fourierCoeff (T := (1 : ℝ))
        (deLaValleePoussinCircleKernel (N i)) (k i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact deLaValleePoussinCircleKernel_fourierCoeff_of_natAbs_le
      (N i) (hN i) (k i) (hk i)
  calc
    _ = UnitAddTorus.mFourier k x *
        ∫ y : UnitAddTorus (Fin d),
          ∏ i : Fin d,
            (deLaValleePoussinCircleKernel (N i) (y i) * fourier (-(k i)) (y i))
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
        rw [integral_congr_ae (ae_of_all _ hterm), integral_const_mul]
    _ = UnitAddTorus.mFourier k x := by rw [hprodint, hcoeff, mul_one]

/-- The actual tensor-product de la Vallée-Poussin kernel reproduces every
rectangularly bandlimited finite torus Fourier polynomial. -/
theorem tensor_dvp_reproduces_bandlimited_polynomial {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (hband : ∀ k ∈ S, ∀ i, (k i).natAbs ≤ N i)
    (x : UnitAddTorus (Fin d)) :
    (∫ y : UnitAddTorus (Fin d), tensorDvpKernel N y *
        torusFourierPolynomial S a (x-y)
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      torusFourierPolynomial S a x := by
  classical
  simp only [torusFourierPolynomial, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  have hterm_int (k : Fin d → ℤ) (hk : k ∈ S) :
      Integrable (fun y : UnitAddTorus (Fin d) =>
        tensorDvpKernel N y * (a k * UnitAddTorus.mFourier k (x-y)))
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
        tensorDvpKernel N y * (a k * UnitAddTorus.mFourier k (x-y))) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsumfun : (fun y : UnitAddTorus (Fin d) =>
      tensorDvpKernel N y *
        (∑ k ∈ S, a k * UnitAddTorus.mFourier k (x-y))) =
      fun y => ∑ k ∈ S,
        tensorDvpKernel N y * (a k * UnitAddTorus.mFourier k (x-y)) := by
    funext y
    rw [Finset.mul_sum]
  rw [hsumfun, integral_finset_sum S hterm_int]
  apply Finset.sum_congr rfl
  intro k hk
  have hmode := tensor_dvp_mode_convolution N hN k (hband k hk) x
  calc
    ∫ y : UnitAddTorus (Fin d),
        tensorDvpKernel N y * (a k * UnitAddTorus.mFourier k (x-y))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) =
      a k * ∫ y : UnitAddTorus (Fin d),
        tensorDvpKernel N y * UnitAddTorus.mFourier k (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
          calc
            _ = ∫ y : UnitAddTorus (Fin d),
                a k * (tensorDvpKernel N y * UnitAddTorus.mFourier k (x-y))
                ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                  apply integral_congr_ae
                  filter_upwards [] with y
                  ring
            _ = _ := by rw [integral_const_mul]
    _ = a k * UnitAddTorus.mFourier k x := by rw [hmode]

/-- Same reproducing identity in the standard `K(x-y) f(y)` convolution
orientation used by the shifted-grid sampling argument. -/
theorem tensor_dvp_reproduces_bandlimited_polynomial_standard {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (hband : ∀ k ∈ S, ∀ i, (k i).natAbs ≤ N i)
    (x : UnitAddTorus (Fin d)) :
    (∫ y : UnitAddTorus (Fin d), tensorDvpKernel N (x-y) *
        torusFourierPolynomial S a y
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      torusFourierPolynomial S a x := by
  have hcurrent := tensor_dvp_reproduces_bandlimited_polynomial N hN S a hband x
  let μ : Measure (UnitAddTorus (Fin d)) :=
    AlignmentPaperTorusTranslation.torusMeasure d
  let g : UnitAddTorus (Fin d) → ℂ := fun y => tensorDvpKernel N (x-y) *
    torusFourierPolynomial S a y
  have hchange :
      (∫ y : UnitAddTorus (Fin d), tensorDvpKernel N y *
        torusFourierPolynomial S a (x-y) ∂μ) =
      ∫ y : UnitAddTorus (Fin d), tensorDvpKernel N (x-y) *
        torusFourierPolynomial S a y ∂μ := by
    have h := integral_sub_left_eq_self g μ x
    change (∫ y : UnitAddTorus (Fin d), g (x-y) ∂μ) = ∫ y, g y ∂μ at h
    have hleft : (fun y : UnitAddTorus (Fin d) => g (x-y)) = fun y =>
        tensorDvpKernel N y * torusFourierPolynomial S a (x-y) := by
      funext y
      simp [g, sub_sub_cancel]
    rw [hleft] at h
    exact h
  calc
    _ = ∫ y : UnitAddTorus (Fin d), tensorDvpKernel N y *
        torusFourierPolynomial S a (x-y) ∂μ := hchange.symm
    _ = torusFourierPolynomial S a x := by
      simpa [μ, AlignmentPaperTorusTranslation.torusMeasure] using hcurrent

/-- The actual tensor DVP kernel has the translated-grid absolute mass
bound at every torus translation. -/
theorem tensor_dvp_torus_grid_abs_mass_le {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) (y : UnitAddTorus (Fin d)) :
    (∑ j : (∀ i, Fin (N i)),
      ‖tensorDvpKernel N (midpointTorusGridPoint N j - y)‖) ≤
      ∏ i, (5 * (N i : ℝ)) := by
  classical
  have hsurj : Function.Surjective (fun t : ℝ => (t : UnitAddCircle)) := by
    intro z
    exact Quotient.mk_surjective z
  let t : Fin d → ℝ := fun i => Classical.choose (hsurj (y i))
  have ht (i : Fin d) : (t i : UnitAddCircle) = y i :=
    Classical.choose_spec (hsurj (y i))
  have hterm (j : ∀ i, Fin (N i)) :
      ‖tensorDvpKernel N (midpointTorusGridPoint N j - y)‖ =
        ∏ i, |realDeLaValleePoussinKernel (N i)
          ((((j i).val : ℝ) + 1 / 2) / (N i) - t i)| := by
    change ‖∏ i : Fin d, deLaValleePoussinCircleKernel (N i)
        (midpointTorusGridPoint N j i - y i)‖ = _
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have harg : midpointTorusGridPoint N j i - y i =
        (((((j i).val : ℝ) + 1 / 2) / (N i : ℝ) - t i : ℝ) : UnitAddCircle) := by
      rw [← ht i]
      simp [midpointTorusGridPoint]
    rw [harg, deLaValleePoussinCircleKernel_eval_eq_real]
    simp [Complex.norm_real]
  calc
    _ = ∑ j : (∀ i, Fin (N i)),
        ∏ i, |realDeLaValleePoussinKernel (N i)
          ((((j i).val : ℝ) + 1 / 2) / (N i) - t i)| := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ ≤ ∏ i, (5 * (N i : ℝ)) :=
      tensor_shifted_dvp_grid_abs_mass_le_five_pi N hN t

end BrownianSharp.AlignmentPaperLpDvpReproduction
