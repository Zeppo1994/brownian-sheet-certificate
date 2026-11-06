import BrownianSharp.AlignmentPaperLpDvpReproduction
import BrownianSharp.AlignmentPaperLpWeightedHolder
import BrownianSharp.AlignmentPaperTorusTranslation
import BrownianSharp.ScalarKernelL1
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Genuine coordinate-dependent Lp sampling for finite torus Fourier blocks,
using tensor DVP reproduction and the manuscript's translated-grid mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperLpDvpSampling

open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.AlignmentPaperLpWeightedHolder
open BrownianSharp.AlignmentPaperTorusTranslation
open BrownianSharp.Torus
open HaarQuarter.TheoremD.FejerFourier

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
open BrownianSharp.ScalarKernelL1

theorem deLaValleePoussin_norm_integral_le_three (N : ℕ) (hN : 0 < N) :
    (∫ x : UnitAddCircle,
      ‖deLaValleePoussinCircleKernel N x‖ ∂AddCircle.haarAddCircle) ≤ 3 := by
  let F : ℕ → C(UnitAddCircle, ℂ) := fun n =>
    ⟨fejerFourierPolynomial n, BrownianSharp.ScalarKernelL1.fejer_continuous n⟩
  have hpoint (x : UnitAddCircle) :
      ‖deLaValleePoussinCircleKernel N x‖ ≤
        2 * ‖F (2*N) x‖ + ‖F N x‖ := by
    change ‖2 * fejerFourierPolynomial (2*N) x - fejerFourierPolynomial N x‖ ≤ _
    calc
      _ ≤ ‖2 * fejerFourierPolynomial (2*N) x‖ +
          ‖fejerFourierPolynomial N x‖ := norm_sub_le _ _
      _ = 2 * ‖F (2*N) x‖ + ‖F N x‖ := by
        simp [F, norm_mul, Complex.norm_ofNat]
  have hleft : Integrable (fun x : UnitAddCircle =>
      ‖deLaValleePoussinCircleKernel N x‖) AddCircle.haarAddCircle := by
    exact (deLaValleePoussinCircleKernel N).continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF (n : ℕ) : Integrable (fun x : UnitAddCircle => ‖F n x‖)
      AddCircle.haarAddCircle := by
    exact (F n).continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfejer (n : ℕ) (hn : 0 < n) :
      (∫ x : UnitAddCircle, ‖F n x‖ ∂AddCircle.haarAddCircle) = 1 := by
    simpa [F] using ScalarKernelL1.fejer_norm_integral n hn
  have hright : Integrable (fun x : UnitAddCircle =>
      2 * ‖F (2*N) x‖ + ‖F N x‖) AddCircle.haarAddCircle :=
    ((hF (2*N)).const_mul 2).add (hF N)
  calc
    _ ≤ ∫ x : UnitAddCircle, 2 * ‖F (2*N) x‖ + ‖F N x‖
        ∂AddCircle.haarAddCircle := integral_mono_ae hleft hright (ae_of_all _ hpoint)
    _ = 2 * (∫ x : UnitAddCircle, ‖F (2*N) x‖ ∂AddCircle.haarAddCircle) +
        ∫ x : UnitAddCircle, ‖F N x‖ ∂AddCircle.haarAddCircle := by
      calc
        _ = (∫ x : UnitAddCircle, 2 * ‖F (2*N) x‖ ∂AddCircle.haarAddCircle) +
            ∫ x : UnitAddCircle, ‖F N x‖ ∂AddCircle.haarAddCircle :=
              integral_add ((hF (2*N)).const_mul 2) (hF N)
        _ = _ := by
          simpa only [integral_const_mul]
    _ = 3 := by
      rw [hfejer (2*N) (by omega), hfejer N hN]
      norm_num [F]

theorem tensor_dvp_norm_integral_le_three_pow {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) :
    (∫ x : UnitAddTorus (Fin d), ‖tensorDvpKernel N x‖
      ∂(torusMeasure d)) ≤ (3 : ℝ) ^ d := by
  have hprod := BrownianSharp.coordinateProductKernel_norm_integral_le
    (fun i => deLaValleePoussinCircleKernel (N i))
    (fun _ => 3) (fun _ => by norm_num)
    (fun i => deLaValleePoussin_norm_integral_le_three (N i) (hN i))
  simpa [tensorDvpKernel, torusMeasure] using hprod

/-- The empirical coordinate-grid Lp norm of a genuinely bandlimited
polynomial is bounded by its actual torus Lp norm. The constant is explicit
and the bandwidth may vary independently by coordinate. -/
theorem torusFourierPolynomial_shifted_grid_lp_bound {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (hband : ∀ k ∈ S, ∀ i, (k i).natAbs ≤ N i)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    (∑ j : (∀ i, Fin (N i)),
      ‖torusFourierPolynomial S a (midpointTorusGridPoint N j)‖ ^ p) ≤
      ((3 : ℝ) ^ d) ^ (p - 1) *
        (∏ i, (5 * (N i : ℝ))) *
        (∫ y : UnitAddTorus (Fin d), ‖torusFourierPolynomial S a y‖ ^ p
          ∂(torusMeasure d)) := by
  classical
  let P := torusFourierPolynomial S a
  let μ := torusMeasure d
  let L1 : ℝ := (3 : ℝ)^d
  have hL1 := tensor_dvp_norm_integral_le_three_pow N hN
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hgridWeight (j : ∀ i, Fin (N i)) (y : UnitAddTorus (Fin d)) :
      ‖tensorDvpKernel N (midpointTorusGridPoint N j - y)‖ =
        ‖tensorDvpKernel N (midpointTorusGridPoint N j - y)‖ := rfl
  have hsample (j : ∀ i, Fin (N i)) :
      ‖P (midpointTorusGridPoint N j)‖ ^ p ≤
        L1 ^ (p - 1) *
          ∫ y : UnitAddTorus (Fin d),
            ‖tensorDvpKernel N (midpointTorusGridPoint N j - y)‖ * ‖P y‖ ^ p ∂μ := by
    let x := midpointTorusGridPoint N j
    let w : UnitAddTorus (Fin d) → ℝ := fun y => ‖tensorDvpKernel N (x-y)‖
    let v : UnitAddTorus (Fin d) → ℝ := fun y => ‖P y‖
    have hw : ∀ y, 0 ≤ w y := fun y => norm_nonneg _
    have hv : ∀ y, 0 ≤ v y := fun y => norm_nonneg _
    have hwcont : Continuous w := by fun_prop
    have hvcont : Continuous v := by fun_prop
    have hpInv : 0 < 1/p := one_div_pos.mpr hp0
    have hqInv : 0 < 1/q := one_div_pos.mpr hq0
    have hUcont : Continuous (fun y => w y ^ (1/p) * v y) :=
      (hwcont.rpow_const (fun _ => Or.inr hpInv.le)).mul hvcont
    have hWcont : Continuous (fun y => w y ^ (1/q)) :=
      hwcont.rpow_const (fun _ => Or.inr hqInv.le)
    have hU : MemLp (fun y => w y ^ (1/p) * v y) (ENNReal.ofReal p) μ :=
      hUcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hW : MemLp (fun y => w y ^ (1/q)) (ENNReal.ofReal q) μ :=
      hWcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hnormInt :
        (∫ y : UnitAddTorus (Fin d), ‖tensorDvpKernel N (x-y)‖ ∂μ) ≤ L1 := by
      have hs := integral_norm_rpow_sub_left (tensorDvpKernel N) 1 x
      have heq : (∫ y : UnitAddTorus (Fin d),
          ‖tensorDvpKernel N (x-y)‖ ∂μ) =
          ∫ y : UnitAddTorus (Fin d), ‖tensorDvpKernel N y‖ ∂μ := by
        simpa [Real.rpow_one, μ] using hs
      rw [heq]
      simpa [L1, μ] using hL1
    have hconv := tensor_dvp_reproduces_bandlimited_polynomial_standard
      N hN S a hband x
    have hnormconv :
        ‖P x‖ ≤ ∫ y : UnitAddTorus (Fin d), w y * v y ∂μ := by
      rw [show P x = ∫ y : UnitAddTorus (Fin d),
        tensorDvpKernel N (x-y) * P y ∂μ by simpa [P, μ] using hconv.symm]
      calc
        _ ≤ ∫ y : UnitAddTorus (Fin d),
          ‖tensorDvpKernel N (x-y) * P y‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ y : UnitAddTorus (Fin d), w y * v y ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [w, v, norm_mul]
    have hwv : 0 ≤ ∫ y : UnitAddTorus (Fin d), w y * v y ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [] with y
      exact mul_nonneg (hw y) (hv y)
    have hpower := Real.rpow_le_rpow (norm_nonneg (P x)) hnormconv hp0.le
    have hweighted := integral_weighted_mul_rpow_le hpq w v
      (ae_of_all μ hw) (ae_of_all μ hv) hU hW
    have hconst : (∫ y : UnitAddTorus (Fin d), w y ∂μ) ≤ L1 := by
      simpa [w, L1, μ] using hnormInt
    have hrightnonneg : 0 ≤ L1 ^ (p - 1) := by positivity
    have hpminus : 0 ≤ p - 1 := by
      have hrecip : 1/p < 1 := by
        have hInv : 1/p + 1/q = 1 := by
          simpa [one_div] using hpq.inv_add_inv_eq_one
        have hqrecip : 0 < 1/q := one_div_pos.mpr hpq.symm.pos
        calc
          1/p < 1/p + 1/q := by linarith
          _ = 1 := hInv
      have hrecip' : 1/p < 1/1 := by simpa using hrecip
      have hp1 : 1 < p := (one_div_lt_one_div hpq.pos (by norm_num)).mp hrecip'
      linarith
    calc
      ‖P x‖ ^ p ≤ (∫ y : UnitAddTorus (Fin d), w y * v y ∂μ) ^ p := hpower
      _ ≤ (∫ y : UnitAddTorus (Fin d), w y * v y ^ p ∂μ) *
          (∫ y : UnitAddTorus (Fin d), w y ∂μ) ^ (p - 1) := hweighted
      _ ≤ (∫ y : UnitAddTorus (Fin d), w y * v y ^ p ∂μ) * L1 ^ (p - 1) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hconst hpminus)
          (integral_nonneg_of_ae (by
            filter_upwards [] with y
            exact mul_nonneg (hw y) (Real.rpow_nonneg (hv y) p)))
      _ = L1 ^ (p - 1) *
          ∫ y : UnitAddTorus (Fin d), w y * v y ^ p ∂μ := by ring
  have hsumint :
      (∑ j : (∀ i, Fin (N i)),
        ∫ y : UnitAddTorus (Fin d),
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ *
            ‖P y‖ ^ p ∂μ) ≤
        (∏ i, (5 * (N i : ℝ))) *
          (∫ y : UnitAddTorus (Fin d), ‖P y‖ ^ p ∂μ) := by
    have hterm (j : ∀ i, Fin (N i)) : Integrable
        (fun y : UnitAddTorus (Fin d) =>
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) μ := by
      have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) := by
        exact ((tensorDvpKernel N).continuous.norm.comp
          (continuous_const.sub continuous_id)).mul
          ((P.continuous.norm).rpow_const (fun _ => Or.inr hp0.le))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hsumcont : Continuous (fun y : UnitAddTorus (Fin d) =>
        ∑ j : (∀ i, Fin (N i)),
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) := by
      apply continuous_finset_sum
      intro j hj
      exact ((tensorDvpKernel N).continuous.norm.comp
        (continuous_const.sub continuous_id)).mul
        ((P.continuous.norm).rpow_const (fun _ => Or.inr hp0.le))
    have hsumintg : Integrable
        (fun y : UnitAddTorus (Fin d) =>
          ∑ j : (∀ i, Fin (N i)),
            ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) μ :=
      hsumcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hrightcont : Continuous (fun y : UnitAddTorus (Fin d) =>
        (∏ i, (5 * (N i : ℝ))) * ‖P y‖ ^ p) :=
      continuous_const.mul ((P.continuous.norm).rpow_const (fun _ => Or.inr hp0.le))
    have hrightint : Integrable
        (fun y : UnitAddTorus (Fin d) =>
          (∏ i, (5 * (N i : ℝ))) * ‖P y‖ ^ p) μ :=
      hrightcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hpoint : ∀ y : UnitAddTorus (Fin d),
        (∑ j : (∀ i, Fin (N i)),
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) ≤
        (∏ i, (5 * (N i : ℝ))) * ‖P y‖ ^ p := by
      intro y
      have hmass := tensor_dvp_torus_grid_abs_mass_le N hN y
      have hpow : 0 ≤ ‖P y‖ ^ p := Real.rpow_nonneg (norm_nonneg (P y)) p
      have hmul := mul_le_mul_of_nonneg_right hmass hpow
      simpa [Finset.sum_mul] using hmul
    calc
      _ = ∫ y : UnitAddTorus (Fin d),
          (∑ j : (∀ i, Fin (N i)),
            ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p) ∂μ := by
        symm
        rw [integral_finset_sum]
        intro j hj
        exact hterm j
      _ ≤ ∫ y : UnitAddTorus (Fin d),
          (∏ i, (5 * (N i : ℝ))) * ‖P y‖ ^ p ∂μ :=
        integral_mono_ae hsumintg hrightint (ae_of_all μ hpoint)
      _ = (∏ i, (5 * (N i : ℝ))) *
          (∫ y : UnitAddTorus (Fin d), ‖P y‖ ^ p ∂μ) := by
        rw [integral_const_mul]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j hj => hsample j
  calc
    _ ≤ ∑ j : (∀ i, Fin (N i)), L1 ^ (p - 1) *
        ∫ y : UnitAddTorus (Fin d),
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p ∂μ := hsum
    _ = L1 ^ (p - 1) * ∑ j : (∀ i, Fin (N i)),
        ∫ y : UnitAddTorus (Fin d),
          ‖tensorDvpKernel N (midpointTorusGridPoint N j-y)‖ * ‖P y‖ ^ p ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      calc
        _ ≤ L1 ^ (p - 1) *
            ((∏ i, (5 * (N i : ℝ))) *
              ∫ y : UnitAddTorus (Fin d), ‖P y‖ ^ p ∂μ) :=
          mul_le_mul_of_nonneg_left hsumint (by positivity)
        _ = _ := by simp [L1, P, μ, mul_assoc]

end BrownianSharp.AlignmentPaperLpDvpSampling
