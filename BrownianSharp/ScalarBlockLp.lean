import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.YoungFejerMixtureLp
import BrownianSharp.ComplexYoungConvolutionLp

noncomputable section
open MeasureTheory
open scoped BigOperators
open AddCircle BrownianSharp.ScalarKernelL1
open BrownianSharp.SmoothResolution

namespace BrownianSharp

theorem fejerKernel_eq_real (N : ℕ) :
    ScalarKernelL1.fejerKernel N =
      ⟨fun x => (realFejerKernel N x : ℂ),
        Complex.continuous_ofReal.comp (realFejerKernel N).continuous⟩ := by
  apply ContinuousMap.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    change HaarQuarter.TheoremD.FejerFourier.fejerFourierPolynomial N
        (t : UnitAddCircle) = (realFejerKernel N t : ℂ)
    have h := HaarQuarter.TheoremD.FejerFourier.fejerFourierPolynomial_eval_eq_real N t
    have hn := ScalarKernelL1.fejer_norm_eq_re N (t : UnitAddCircle)
    have hrr : 0 ≤ HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t := by
      have hh := hn
      rw [h] at hh
      have habs : |HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t| =
          HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hh
      exact abs_eq_self.mp habs
    have hnorm : ‖HaarQuarter.TheoremD.FejerFourier.fejerFourierPolynomial N
        (t : UnitAddCircle)‖ =
        HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t := by
      rw [h]
      simp [Complex.norm_real, Real.norm_eq_abs, hrr]
    rw [h]
    change (HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t : ℂ) =
      (realFejerKernel N (t : UnitAddCircle) : ℂ)
    congr 1
    simpa [realFejerKernel, hnorm]

theorem scalarBlockKernel_eq_realFejerMixture (t : ℕ) :
    ∃ J : ℕ, ∃ f : ℕ → ℝ,
      ScalarKernelL1.scalarBlockKernel t =
        ⟨fun x => ((∑ j ∈ Finset.range J,
          f j * realFejerKernel (j+1) x : ℝ) : ℂ), by
            have hc : Continuous (fun x : UnitAddCircle =>
              ∑ j ∈ Finset.range J, f j * realFejerKernel (j+1) x) := by fun_prop
            exact Complex.continuous_ofReal.comp hc⟩ := by
  obtain ⟨J, c, hc, hmix⟩ := scalarBlockKernel_eq_fejerMixture t
  let prof := if t = 0 then cutoff else InverseDerivativeProfile.profile 0
  let scale := if t = 0 then 1 else 2 ^ t
  let f : ℕ → ℝ := fun j => scalarProfileSecondWeight prof scale j
  have hweight (j : ℕ) : secondWeight c j = (f j : ℂ) := by
    rw [hc]
    simp [secondWeight, f, scalarProfileSecondWeight, scalarProfileSample,
      prof, scale, InverseDerivativeProfile.profile]
  refine ⟨J, f, ?_⟩
  rw [hmix]
  apply ContinuousMap.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    change (ScalarKernelL1.fejerMixture J c : UnitAddCircle → ℂ) (z : UnitAddCircle) =
      ((∑ j ∈ Finset.range J, f j * realFejerKernel (j+1) (z : UnitAddCircle) : ℝ) : ℂ)
    dsimp [ScalarKernelL1.fejerMixture]
    simp_rw [fejerKernel_eq_real]
    simp_rw [hweight]
    simp [smul_eq_mul, Complex.ofReal_mul, ← Finset.sum_mul]

end BrownianSharp

namespace BrownianSharp

/-- Finite-p scalar block bound with the exact coefficient-variation
constant from its finite Fejer representation. -/
theorem scalarBlockKernel_convolution_rpow_le
    (t : ℕ) (u : C(UnitAddCircle, ℝ)) (p : ℝ) (hp : 1 ≤ p) :
    ∃ J : ℕ, ∃ f : ℕ → ℝ,
      (∫ x : UnitAddCircle,
        ‖∫ y, ScalarKernelL1.scalarBlockKernel t y *
          (u (x-y) : ℂ) ∂AddCircle.haarAddCircle‖ ^ p
          ∂AddCircle.haarAddCircle) ≤
        (∑ j ∈ Finset.range J, |f j|) ^ p *
          ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle := by
  obtain ⟨J, f, hK⟩ := scalarBlockKernel_eq_realFejerMixture t
  refine ⟨J, f, ?_⟩
  let S : Finset ℕ := (Finset.range J).image Nat.succ
  let w : ℕ → ℝ := fun N => if N = 0 then 0 else f (N-1)
  have hpos (N : ℕ) (hN : N ∈ S) : 0 < N := by
    rcases Finset.mem_image.mp hN with ⟨j, hj, rfl⟩
    exact Nat.succ_pos _
  have hkernel (y : UnitAddCircle) :
      ScalarKernelL1.scalarBlockKernel t y =
        ((∑ j ∈ Finset.range J, f j * realFejerKernel (j+1) y : ℝ) : ℂ) := by
    have := congrArg (fun F : C(UnitAddCircle, ℂ) => F y) hK
    simpa only [ContinuousMap.coe_mk] using this
  have hmixture (y : UnitAddCircle) :
      (∑ N ∈ S, w N * realFejerKernel N y) =
        ∑ j ∈ Finset.range J, f j * realFejerKernel (j+1) y := by
    classical
    simp [S, w, Finset.sum_image, Nat.succ_injective.injOn]
  have hcoefsum :
      (∑ N ∈ S, |w N|) = ∑ j ∈ Finset.range J, |f j| := by
    classical
    simp [S, w, Finset.sum_image, Nat.succ_injective.injOn]
  have hrealConv (x : UnitAddCircle) :
      (∫ y, ScalarKernelL1.scalarBlockKernel t y * (u (x-y) : ℂ)
        ∂AddCircle.haarAddCircle) =
      (((∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y)
        ∂AddCircle.haarAddCircle) : ℝ) : ℂ) := by
    calc
      _ = ∫ y, (((∑ N ∈ S, w N * realFejerKernel N y) * u (x-y) : ℝ) : ℂ)
          ∂AddCircle.haarAddCircle := by
        congr 1
        funext y
        rw [hkernel, hmixture]
        push_cast
        ring
      _ = _ := by exact integral_ofReal
  have hbound := realFejer_mixture_convolution_rpow_le S w hpos u p hp
  have hnorm (x : UnitAddCircle) :
      ‖∫ y, ScalarKernelL1.scalarBlockKernel t y * (u (x-y) : ℂ)
        ∂AddCircle.haarAddCircle‖ ^ p =
      |∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y)
        ∂AddCircle.haarAddCircle| ^ p := by
    rw [hrealConv]
    simp [Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = ∫ x : UnitAddCircle,
        |∫ y, (∑ N ∈ S, w N * realFejerKernel N y) * u (x-y)
          ∂AddCircle.haarAddCircle| ^ p ∂AddCircle.haarAddCircle := by
      congr 1
      funext x
      exact hnorm x
    _ ≤ (∑ N ∈ S, |w N|) ^ p *
        ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle := hbound
    _ = _ := by rw [hcoefsum]

end BrownianSharp

namespace BrownianSharp

/-- The actual scalar smooth blocks are uniformly bounded on every finite
Lp space; the constant is the proved profile L1 budget. -/
theorem exists_scalarBlockKernel_uniform_convolution_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t : ℕ) (u : C(UnitAddCircle, ℝ)) (p : ℝ),
      1 ≤ p →
      (∫ x : UnitAddCircle,
        ‖∫ y, ScalarKernelL1.scalarBlockKernel t y * (u (x-y) : ℂ)
          ∂AddCircle.haarAddCircle‖ ^ p ∂AddCircle.haarAddCircle) ≤
        L ^ p * ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle := by
  obtain ⟨L, hL, hbound⟩ := exists_scalarBlockKernel_uniform_L1_bound
  refine ⟨L, hL, ?_⟩
  intro t u p hp
  have hyoung := addCircle_complex_convolution_rpow_le
    (ScalarKernelL1.scalarBlockKernel t)
    ⟨fun x => (u x : ℂ), Complex.continuous_ofReal.comp u.continuous⟩ p hp
  have hscale : (∫ y : UnitAddCircle,
      ‖ScalarKernelL1.scalarBlockKernel t y‖ ∂AddCircle.haarAddCircle) ^ p ≤ L ^ p :=
    Real.rpow_le_rpow (integral_nonneg (fun y => norm_nonneg _))
      (hbound t) (le_trans (by norm_num) hp)
  have hpoweq : ∀ x : UnitAddCircle,
      ‖(u x : ℂ)‖ ^ p = |u x| ^ p := by
    intro x
    simp [Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (∫ y : UnitAddCircle,
          ‖ScalarKernelL1.scalarBlockKernel t y‖ ∂AddCircle.haarAddCircle) ^ p *
        ∫ x : UnitAddCircle, ‖(u x : ℂ)‖ ^ p ∂AddCircle.haarAddCircle := hyoung
    _ ≤ L ^ p * ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle := by
      rw [show (∫ x : UnitAddCircle, ‖(u x : ℂ)‖ ^ p ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, |u x| ^ p ∂AddCircle.haarAddCircle by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoweq x]
      exact mul_le_mul_of_nonneg_right hscale
        (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))

end BrownianSharp
