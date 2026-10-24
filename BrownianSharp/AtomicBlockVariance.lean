import BrownianSharp.PeriodicCover
import BrownianSharp.SmoothResolution
import BrownianSharp.GaussianGridStatistics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Moments.Variance

/-!
Finite-dimensional deterministic estimates for the actual atom synthesis.
These are separated from `PeriodicCover` so the covering bridge remains a
stable dependency while the analytic norm estimates are developed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp.AtomicBlockVariance
open BrownianSharp.Torus
open BrownianSharp.PeriodicCover
open BrownianSharp.CameronMartinEntropy

private theorem periodicFourierIntegrable {d : ℕ} (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    Integrable (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) x • (f x : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hcont : Continuous (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) x • (f x : ℂ)) := by fun_prop
  have hbound : ∀ x, ‖UnitAddTorus.mFourier (-k) x • (f x : ℂ)‖ ≤ ‖f‖ := by
    intro x
    rw [norm_smul]
    have hm : ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ ‖UnitAddTorus.mFourier (-k)‖ :=
          (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖(f x : ℂ)‖ ≤ ‖f‖ := by
      simpa using f.norm_coe_le_norm x
    calc
      ‖UnitAddTorus.mFourier (-k) x‖ * ‖(f x : ℂ)‖ ≤ 1 * ‖f‖ :=
        mul_le_mul hm hf (norm_nonneg _) (by norm_num)
      _ = ‖f‖ := one_mul _
  exact Integrable.of_bound hcont.aestronglyMeasurable ‖f‖
    (ae_of_all _ hbound)

/-- The actual smooth-resolution Fourier coefficient is additive on real
periodic functions. -/
theorem realPeriodicFourierCoeff_add {d : ℕ} (f g : RealPeriodic d)
    (k : Fin d → ℤ) :
    BrownianSharp.Torus.realPeriodicFourierCoeff (f + g) k =
      BrownianSharp.Torus.realPeriodicFourierCoeff f k +
        BrownianSharp.Torus.realPeriodicFourierCoeff g k := by
  classical
  unfold BrownianSharp.Torus.realPeriodicFourierCoeff
    BrownianSharp.Torus.complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_add, Pi.add_apply, Complex.ofReal_add, smul_add]
  exact integral_add (periodicFourierIntegrable f k) (periodicFourierIntegrable g k)

/-- Real scalar homogeneity of the actual torus Fourier coefficient. -/
theorem realPeriodicFourierCoeff_smul {d : ℕ} (c : ℝ) (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    BrownianSharp.Torus.realPeriodicFourierCoeff (c • f) k =
      (c : ℂ) * BrownianSharp.Torus.realPeriodicFourierCoeff f k := by
  classical
  unfold BrownianSharp.Torus.realPeriodicFourierCoeff
    BrownianSharp.Torus.complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have hfun : (fun t : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) t * ((c : ℂ) * (f t : ℂ))) =
      fun t => (c : ℂ) * (UnitAddTorus.mFourier (-k) t * (f t : ℂ)) := by
    funext t
    ring
  rw [hfun, integral_const_mul]

/-- Each actual smooth tensor Fourier block is additive. -/
theorem smoothBlock_add {d : ℕ} (s : Fin d → ℕ) (f g : RealPeriodic d) :
    BrownianSharp.SmoothResolution.block s (f + g) =
      BrownianSharp.SmoothResolution.block s f +
        BrownianSharp.SmoothResolution.block s g := by
  classical
  ext x
  simp [BrownianSharp.SmoothResolution.block,
    BrownianSharp.Torus.torusFourierPolynomial, realPeriodicFourierCoeff_add,
    Finset.sum_add_distrib, mul_add, add_smul]

/-- Each actual smooth tensor Fourier block is homogeneous under real scaling. -/
theorem smoothBlock_smul {d : ℕ} (s : Fin d → ℕ) (c : ℝ) (f : RealPeriodic d) :
    BrownianSharp.SmoothResolution.block s (c • f) =
      (c : ℂ) • BrownianSharp.SmoothResolution.block s f := by
  classical
  ext x
  simp [BrownianSharp.SmoothResolution.block,
    BrownianSharp.Torus.torusFourierPolynomial, realPeriodicFourierCoeff_smul,
    Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The actual smooth Fourier block, as a real-linear operator on continuous
periodic functions. -/
noncomputable def smoothBlockLinear {d : ℕ} (s : Fin d → ℕ) :
    RealPeriodic d →ₗ[ℝ] C(UnitAddTorus (Fin d), ℂ) where
  toFun := BrownianSharp.SmoothResolution.block s
  map_add' := smoothBlock_add s
  map_smul' := smoothBlock_smul s

/-- Fourier-block evaluation of a finite Gaussian atom synthesis is the
corresponding finite real Gaussian linear form. -/
theorem smoothBlock_gaussianSynthesis {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d) (z : Fin ι → ℝ)
    (x : UnitAddTorus (Fin d)) :
    BrownianSharp.SmoothResolution.block s (gaussianSynthesis atoms z) x =
      ∑ i : Fin ι, (z i : ℂ) *
        BrownianSharp.SmoothResolution.block s (atoms i) x := by
  classical
  change smoothBlockLinear s (gaussianSynthesis atoms z) x = _
  simp [smoothBlockLinear, gaussianSynthesis, map_sum, map_smul]

/-- Exact pointwise second moment of a finite Gaussian atom synthesis after an
actual smooth Fourier block. This is the algebraic variance identity before
any block-kernel estimate is applied. -/
theorem smoothBlock_gaussian_secondMoment {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    ∫ z : Fin ι → ℝ,
      ‖BrownianSharp.SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ 2
        ∂BrownianSharp.productStandardGaussian (Fin ι) =
      ∑ i : Fin ι,
        ‖BrownianSharp.SmoothResolution.block s (atoms i) x‖ ^ 2 := by
  classical
  let G : Fin ι → (Fin ι → ℝ) → ℝ := fun i z => z i
  let P : Measure (Fin ι → ℝ) := BrownianSharp.productStandardGaussian (Fin ι)
  let c : Fin ι → ℝ := fun i =>
    (BrownianSharp.SmoothResolution.block s (atoms i) x).re
  let e : Fin ι → ℝ := fun i =>
    (BrownianSharp.SmoothResolution.block s (atoms i) x).im
  have hG : ∀ i, Measurable (G i) := by
    intro i
    exact measurable_pi_apply i
  have hLaw : ∀ i, P.map (G i) = gaussianReal 0 1 := by
    intro i
    dsimp [P, G, BrownianSharp.productStandardGaussian]
    exact BrownianSharp.productStandardGaussian_coordinate_law i
  have hIndep : iIndepFun G P := by
    dsimp [P, G, BrownianSharp.productStandardGaussian]
    exact BrownianSharp.productStandardGaussian_coordinates_independent (Fin ι)
  let X : (Fin ι → ℝ) → ℝ := BrownianSharp.GaussianRows.row G c
  let Y : (Fin ι → ℝ) → ℝ := BrownianSharp.GaussianRows.row G e
  have hRe : ∀ z, (BrownianSharp.SmoothResolution.block s
      (gaussianSynthesis atoms z) x).re = X z := by
    intro z
    rw [smoothBlock_gaussianSynthesis]
    simp [X, G, c, BrownianSharp.GaussianRows.row, Complex.mul_re]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hIm : ∀ z, (BrownianSharp.SmoothResolution.block s
      (gaussianSynthesis atoms z) x).im = Y z := by
    intro z
    rw [smoothBlock_gaussianSynthesis]
    simp [Y, G, e, BrownianSharp.GaussianRows.row, Complex.mul_im]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hXmean : ∫ z, X z ∂P = 0 := by
    exact BrownianSharp.GaussianRows.row_mean G hG hLaw c
  have hYmean : ∫ z, Y z ∂P = 0 := by
    exact BrownianSharp.GaussianRows.row_mean G hG hLaw e
  have hXgauss : HasGaussianLaw X P := by
    exact BrownianSharp.GaussianRows.row_gaussian G hG hLaw hIndep c
  have hYgauss : HasGaussianLaw Y P := by
    exact BrownianSharp.GaussianRows.row_gaussian G hG hLaw hIndep e
  have hXint : Integrable (fun z => X z ^ 2) P := by
    exact hXgauss.memLp_two.integrable_sq
  have hYint : Integrable (fun z => Y z ^ 2) P := by
    exact hYgauss.memLp_two.integrable_sq
  have hXsq : ∫ z, X z ^ 2 ∂P = ∑ i, c i ^ 2 := by
    rw [← variance_of_integral_eq_zero hXgauss.aemeasurable hXmean,
      BrownianSharp.GaussianRows.row_variance G hG hLaw hIndep c]
  have hYsq : ∫ z, Y z ^ 2 ∂P = ∑ i, e i ^ 2 := by
    rw [← variance_of_integral_eq_zero hYgauss.aemeasurable hYmean,
      BrownianSharp.GaussianRows.row_variance G hG hLaw hIndep e]
  have hpoint : ∀ z, ‖BrownianSharp.SmoothResolution.block s
      (gaussianSynthesis atoms z) x‖ ^ 2 = X z ^ 2 + Y z ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, hRe z, hIm z]
    ring
  have hsum : (∑ i, c i ^ 2) + ∑ i, e i ^ 2 =
      ∑ i : Fin ι, ‖BrownianSharp.SmoothResolution.block s (atoms i) x‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [c, e]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [pow_two]
  calc
    _ = ∫ z, X z ^ 2 + Y z ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    _ = (∫ z, X z ^ 2 ∂P) + ∫ z, Y z ^ 2 ∂P := integral_add hXint hYint
    _ = _ := by rw [hXsq, hYsq, hsum]

/-- The periodized, rescaled one-dimensional atom remains between zero and
one pointwise; compact support is not needed for this range bound. -/
theorem periodizedDyadicAtom1_bounds (s j : ℕ) (hj : j < 2 ^ s)
    (x : UnitAddCircle) :
    0 ≤ periodizedDyadicAtom1 s j hj x ∧ periodizedDyadicAtom1 s j hj x ≤ 1 := by
  change 0 ≤ AddCircle.liftIco (1 : ℝ) 0
      (fun x : ℝ => smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))) x ∧
    AddCircle.liftIco (1 : ℝ) 0
      (fun x : ℝ => smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))) x ≤ 1
  obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ico x
  rw [AddCircle.liftIco_zero_coe_apply hy]
  exact smoothAtom_bounds _

/-- Every actual tensor atom has uniform norm at most one. -/
theorem periodizedDyadicAtom_norm_le_one {d : ℕ} (a : AtomIndex d) :
    ‖periodizedDyadicAtom a‖ ≤ 1 := by
  rw [ContinuousMap.norm_le_of_nonempty]
  intro x
  change ‖∏ i : Fin d,
    periodizedDyadicAtom1 (a.depth i) (a.cell i) (a.valid i) (x i)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact Finset.prod_le_one₀
      (fun i _ => (periodizedDyadicAtom1_bounds (a.depth i) (a.cell i) (a.valid i) (x i)).1)
      (fun i _ => (periodizedDyadicAtom1_bounds (a.depth i) (a.cell i) (a.valid i) (x i)).2)
  · exact Finset.prod_nonneg fun i _ =>
      (periodizedDyadicAtom1_bounds (a.depth i) (a.cell i) (a.valid i) (x i)).1

/-- Cauchy--Schwarz turns the coefficient-energy cutoff into an `l¹` bound. -/
theorem coefficient_l1_le_two_card {ι : Type*} [Fintype ι]
    (z : ι → ℝ)
    (hcut : coefficientEnergy z ≤ 4 * (Fintype.card ι : ℝ)) :
    (∑ i, |z i|) ≤ 2 * (Fintype.card ι : ℝ) := by
  let D : ℝ := Fintype.card ι
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => |z i|)
  have hcs' : (∑ i, |z i|) ≤ √D * √(coefficientEnergy z) := by
    simpa [D, coefficientEnergy, sq_abs] using hcs
  have hD : 0 ≤ D := by positivity
  have hroot : √(coefficientEnergy z) ≤ 2 * √D := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        coefficientEnergy z ≤ 4 * D := by simpa [D] using hcut
        _ = (2 * √D) ^ 2 := by rw [mul_pow, Real.sq_sqrt hD]; ring
  calc
    ∑ i, |z i| ≤ √D * √(coefficientEnergy z) := hcs'
    _ ≤ √D * (2 * √D) := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
    _ = 2 * D := by
      calc
        √D * (2 * √D) = 2 * (√D * √D) := by ring
        _ = 2 * D := by nlinarith [Real.sq_sqrt hD]

/-- The uniform norm of a finite Gaussian atom synthesis is bounded by its
coefficient `l¹` norm times the largest atom norm. -/
theorem gaussianSynthesis_norm_le_coeff_l1 {ι d : ℕ}
    (atoms : Fin ι → RealPeriodic d) (z : Fin ι → ℝ)
    (A : ℝ) (hatom : ∀ i, ‖atoms i‖ ≤ A) :
    ‖gaussianSynthesis atoms z‖ ≤ A * ∑ i, |z i| := by
  classical
  rw [gaussianSynthesis]
  calc
    ‖∑ i : Fin ι, z i • atoms i‖ ≤ ∑ i : Fin ι, ‖z i • atoms i‖ := norm_sum_le _ _
    _ = ∑ i : Fin ι, |z i| * ‖atoms i‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin ι, |z i| * A :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hatom i) (abs_nonneg _)
    _ = A * ∑ i : Fin ι, |z i| := by rw [← Finset.sum_mul]; ring

/-- On the Cameron--Martin coefficient cutoff, bounded atoms give an explicit
uniform bound for the synthesized function. This is not the mixed smoothness
estimate needed for class membership, but it is a concrete bound for the
actual finite synthesis. -/
theorem gaussianSynthesis_norm_le_of_energy {ι d : ℕ}
    (atoms : Fin ι → RealPeriodic d) (z : Fin ι → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hatom : ∀ i, ‖atoms i‖ ≤ A)
    (hcut : coefficientEnergy z ≤ 4 * (ι : ℝ)) :
    ‖gaussianSynthesis atoms z‖ ≤ 2 * A * (ι : ℝ) := by
  calc
    ‖gaussianSynthesis atoms z‖ ≤ A * ∑ i, |z i| :=
      gaussianSynthesis_norm_le_coeff_l1 atoms z A hatom
    _ ≤ A * (2 * (ι : ℝ)) := by
      have hl1 := coefficient_l1_le_two_card z (by simpa using hcut)
      simpa using mul_le_mul_of_nonneg_left hl1 hA
    _ = 2 * A * (ι : ℝ) := by ring

/-- The coefficient-energy cutoff yields the explicit uniform bound `2D` for
the actual periodized dyadic atom synthesis. -/
theorem periodizedSynthesis_norm_le_of_energy {ι d : ℕ}
    (addresses : Fin ι → AtomIndex d) (z : Fin ι → ℝ)
    (hcut : coefficientEnergy z ≤ 4 * (ι : ℝ)) :
    ‖gaussianSynthesis (fun i => periodizedDyadicAtom (addresses i)) z‖ ≤
      2 * (ι : ℝ) := by
  have h := gaussianSynthesis_norm_le_of_energy
    (fun i => periodizedDyadicAtom (addresses i)) z 1 (by norm_num)
    (fun i => periodizedDyadicAtom_norm_le_one (addresses i)) hcut
  simpa using h

end BrownianSharp.AtomicBlockVariance
