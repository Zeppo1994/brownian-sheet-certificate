import BrownianSharp.AlignmentMaternScalarFeature
import BrownianSharp.AlignmentMaternSpectralWeights
import BrownianSharp.AlignmentMaternComplexFeature
import BrownianSharp.AlignmentPaperLatticePeriodization
import BrownianSharp.AlignmentPaperMixedWeight
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import BrownianSharp.SmoothResolution
import Mathlib.Tactic

/-! Reverse spectral-source energy estimates for Matérn features. -/

noncomputable section
set_option maxHeartbeats 1000000

open MeasureTheory
open Filter TopologicalSpace Asymptotics
open scoped ENNReal RealInnerProductSpace
open scoped SchwartzMap FourierTransform

namespace BrownianSharp.AlignmentPaperMaternSourceEnergy

/-- Summation over a finite-coordinate lattice factors for products of
absolutely summable scalar sequences. This is the discrete product step used
to tensorize the cutoff kernel's scalar column bound. -/
theorem summable_pi_prod_lattice (d : ℕ)
    (f : Fin d → ℤ → ℝ) (hf : ∀ i, Summable (f i)) :
    Summable (fun k : Fin d → ℤ => ∏ i, f i (k i)) := by
  induction d with
  | zero =>
      classical
      letI : Unique (Fin 0 → ℤ) := inferInstance
      exact Summable.of_finite
  | succ d ih =>
      let tail : Fin d → ℤ → ℝ := fun i z => f i.succ z
      have htail : ∀ i, Summable (tail i) := fun i => hf i.succ
      have hsTail : Summable (fun k : Fin d → ℤ => ∏ i, tail i (k i)) := ih tail htail
      let e : (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d+1) => ℤ)
      have hprod : Summable (fun p : ℤ × (Fin d → ℤ) =>
          f 0 p.1 * ∏ i, tail i (p.2 i)) :=
        summable_mul_of_summable_norm (f := f 0)
          (g := fun k : Fin d → ℤ => ∏ i, tail i (k i)) (hf 0).norm hsTail.norm
      have hprod' : Summable
          ((fun k : Fin (d+1) → ℤ => ∏ i, f i (k i)) ∘ e) := by
        refine hprod.congr ?_
        intro p
        change f 0 p.1 * (∏ i : Fin d, tail i (p.2 i)) =
          ∏ i : Fin (d+1), f i ((e p) i)
        rw [Fin.prod_univ_succ]
        simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, tail]
      have htrans := e.summable_iff.mp hprod'
      refine htrans.congr ?_
      intro k
      rfl

/-- Exact factorization of the sum over an indexed integer lattice. -/
theorem tsum_pi_prod_lattice (d : ℕ)
    (f : Fin d → ℤ → ℝ) (hf : ∀ i, Summable (f i)) :
    ∑' k : Fin d → ℤ, ∏ i, f i (k i) = ∏ i, ∑' z : ℤ, f i z := by
  induction d with
  | zero => simp
  | succ d ih =>
      let tail : Fin d → ℤ → ℝ := fun i z => f i.succ z
      have htail : ∀ i, Summable (tail i) := fun i => hf i.succ
      have hsTail : Summable (fun k : Fin d → ℤ => ∏ i, tail i (k i)) :=
        summable_pi_prod_lattice d tail htail
      let e : (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ) :=
        Fin.consEquiv (fun _ : Fin (d+1) => ℤ)
      have hprod : Summable (fun p : ℤ × (Fin d → ℤ) =>
          f 0 p.1 * ∏ i, tail i (p.2 i)) :=
        summable_mul_of_summable_norm (f := f 0)
          (g := fun k : Fin d → ℤ => ∏ i, tail i (k i)) (hf 0).norm hsTail.norm
      have hts := (hf 0).tsum_mul_tsum hsTail hprod
      calc
        ∑' k : Fin (d+1) → ℤ, ∏ i, f i (k i) =
            ∑' p : ℤ × (Fin d → ℤ), f 0 p.1 * ∏ i, tail i (p.2 i) := by
              symm
              have hpoint : ∀ p : ℤ × (Fin d → ℤ),
                  f 0 p.1 * (∏ i : Fin d, tail i (p.2 i)) =
                    ∏ i : Fin (d+1), f i ((e p) i) := by
                intro p
                rw [Fin.prod_univ_succ]
                simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, tail]
              have ht := e.tsum_eq (fun k => ∏ i, f i (k i))
              calc
                ∑' p : ℤ × (Fin d → ℤ), f 0 p.1 * ∏ i, tail i (p.2 i) =
                    ∑' p : ℤ × (Fin d → ℤ), ∏ i, f i ((e p) i) :=
                      tsum_congr hpoint
                _ = _ := ht
        _ = (∑' z : ℤ, f 0 z) *
            ∑' k : Fin d → ℤ, ∏ i, tail i (k i) := by
              exact hts.symm
        _ = ∏ i : Fin (d+1), ∑' z : ℤ, f i z := by
              rw [ih tail htail]
              rw [Fin.prod_univ_succ]

open BrownianSharp.AlignmentMaternComplexFeature

/-- Compactly supported smooth spatial cutoff equal to one on the unit cube.
This is the scalar factor used to localize the inverse-Fourier feature before
periodizing it. -/
def cubeSpatialCutoff (x : ℝ) : ℝ := BrownianSharp.SmoothResolution.cutoff x

theorem cubeSpatialCutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cubeSpatialCutoff := by
  exact BrownianSharp.SmoothResolution.cutoff_smooth

theorem complexCubeSpatialCutoff_hasCompactSupport :
    HasCompactSupport (fun x : ℝ => (cubeSpatialCutoff x : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
  intro x hx
  change (fun x : ℝ => (cubeSpatialCutoff x : ℂ)) x ≠ 0 at hx
  have hx' : |x| ≤ 2 := by
    by_contra hout
    have hout : 2 < |x| := lt_of_not_ge hout
    have hzero : cubeSpatialCutoff x = 0 := by
      exact BrownianSharp.SmoothResolution.cutoff_eq_zero hout.le
    exact hx (by simp [hzero])
  simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hx'

/-- Schwartz realization of the spatial cutoff. Its Fourier transform is
again Schwartz, so all polynomial Fourier-tail estimates needed for sampling
are available from the Schwartz seminorms. -/
def cubeSpatialCutoffSchwartz : 𝓢(ℝ, ℂ) :=
  complexCubeSpatialCutoff_hasCompactSupport.toSchwartzMap (by
    exact Complex.ofRealCLM.contDiff.comp
      (cubeSpatialCutoff_smooth.of_le (by norm_num)))

def cubeSpatialCutoffFourierSchwartz : 𝓢(ℝ, ℂ) := 𝓕 cubeSpatialCutoffSchwartz

/-- Fourier cutoff profile rescaled to the frequency grid of the period-eight
torus. -/
def periodEightCutoffFourierSchwartz : 𝓢(ℝ, ℂ) := by
  have hg : (fun x : ℝ => x / 8).HasTemperateGrowth := by
    have h := (Function.HasTemperateGrowth.const (1 / 8 : ℝ)).smul
      (Function.HasTemperateGrowth.id (E := ℝ))
    have h' : (fun x : ℝ => (1 / 8 : ℝ) * x).HasTemperateGrowth := by
      convert h using 1
      funext x
      simp [smul_eq_mul]
    simpa [div_eq_mul_inv, mul_comm] using h'
  have hupper : ∃ k : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ≤ C * (1 + ‖x / 8‖) ^ k := by
    refine ⟨1, 8, ?_⟩
    intro x
    rw [norm_div]
    norm_num
    nlinarith [norm_nonneg x]
  exact SchwartzMap.compCLM ℂ hg hupper cubeSpatialCutoffFourierSchwartz

@[simp] theorem periodEightCutoffFourierSchwartz_apply (x : ℝ) :
    periodEightCutoffFourierSchwartz x = cubeSpatialCutoffFourierSchwartz (x / 8) := rfl

/-- Polynomially weighted period-eight Fourier profile. -/
def integerWeightedPeriodEightCutoffFourierSchwartz (N : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ N : ℝ) : ℂ))
    periodEightCutoffFourierSchwartz

@[simp] theorem integerWeightedPeriodEightCutoffFourierSchwartz_apply
    (N : ℕ) (x : ℝ) :
    integerWeightedPeriodEightCutoffFourierSchwartz N x =
      ((1 + x ^ 2) ^ N : ℝ) * periodEightCutoffFourierSchwartz x := by
  have hreal : (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ N).HasTemperateGrowth := by
    have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (N : ℝ)
    simpa only [Real.rpow_natCast] using h
  have hcomplex : (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ N : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp hreal
  rw [integerWeightedPeriodEightCutoffFourierSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply hcomplex]
  simp [Complex.real_smul, Real.norm_eq_abs]

theorem integerWeightedPeriodEightCutoffFourier_translateSeries_summable
    (N : ℕ) : ∀ K : Compacts ℝ,
      Summable fun n : ℤ =>
        ‖(⟨(integerWeightedPeriodEightCutoffFourierSchwartz N : ℝ → ℂ),
          (integerWeightedPeriodEightCutoffFourierSchwartz N).continuous⟩ : C(ℝ, ℂ)).comp
            (ContinuousMap.addRight n) |>.restrict K‖ := by
  let f : C(ℝ, ℂ) :=
    ⟨(integerWeightedPeriodEightCutoffFourierSchwartz N : ℝ → ℂ),
      (integerWeightedPeriodEightCutoffFourierSchwartz N).continuous⟩
  have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    simpa [f] using
      (integerWeightedPeriodEightCutoffFourierSchwartz N).isBigO_cocompact_rpow (-2)
  intro K
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
  exact Asymptotics.IsBigO.comp_tendsto
    (isBigO_norm_restrict_cocompact f (by norm_num : 0 < (2 : ℝ)) hf K)
    Int.tendsto_coe_cofinite

theorem periodEightBesselKernel_le_integerWeighted (r : ℝ) (N : ℕ)
    (hrN : r ≤ N) (y : ℝ) :
    (1 + (y / 8) ^ 2) ^ r *
      ‖periodEightCutoffFourierSchwartz y‖ ≤
        ‖integerWeightedPeriodEightCutoffFourierSchwartz N y‖ := by
  have hbase : 1 ≤ 1 + (y / 8) ^ 2 := by nlinarith [sq_nonneg (y / 8)]
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hrN
  have hpowN : (1 + (y / 8) ^ 2) ^ r ≤ (1 + y ^ 2) ^ N := by
    calc
      (1 + (y / 8) ^ 2) ^ r ≤ (1 + (y / 8) ^ 2) ^ N := by
        simpa only [Real.rpow_natCast] using hpow
      _ ≤ (1 + y ^ 2) ^ N := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [sq_nonneg y]
  rw [integerWeightedPeriodEightCutoffFourierSchwartz_apply]
  rw [periodEightCutoffFourierSchwartz_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right hpowN (norm_nonneg _)

/-- Uniform periodized weighted tail at the period-eight sampling grid. -/
theorem periodEightBesselKernel_lattice_bound
    (r : ℝ) (N : ℕ) (hrN : r ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      Summable (fun k : ℤ => (1 + ((k : ℝ) / 8 - ξ) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz ((k : ℝ) / 8 - ξ)‖) ∧
      (∑' k : ℤ, (1 + ((k : ℝ) / 8 - ξ) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz ((k : ℝ) / 8 - ξ)‖) ≤ C := by
  let K : Compacts ℝ := ⟨Set.Icc (-1 : ℝ) 0, isCompact_Icc⟩
  let F : C(ℝ, ℂ) :=
    ⟨(integerWeightedPeriodEightCutoffFourierSchwartz N : ℝ → ℂ),
      (integerWeightedPeriodEightCutoffFourierSchwartz N).continuous⟩
  let C : ℝ := ∑' k : ℤ, ‖(F.comp (ContinuousMap.addRight k)).restrict K‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact tsum_nonneg fun k => norm_nonneg _
  have hlocal : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum
        (fun y => (1 + (y / 8) ^ 2) ^ r *
          ‖cubeSpatialCutoffFourierSchwartz (y / 8)‖) u ≤ C := by
    intro u hu
    have hseries := integerWeightedPeriodEightCutoffFourier_translateSeries_summable N K
    let b' : ℤ → ℝ := fun k => (1 + (((k : ℝ) - u) / 8) ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz (((k : ℝ) - u) / 8)‖
    have hb : ∀ k, 0 ≤ b' k := by
      intro k
      dsimp [b']
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
    have hbc : ∀ k, b' k ≤
        ‖integerWeightedPeriodEightCutoffFourierSchwartz N ((k-u))‖ := by
      intro k
      simpa [b', sub_eq_add_neg] using
        periodEightBesselKernel_le_integerWeighted r N hrN ((k : ℝ) - u)
    have hmajor : Summable b' ∧ ∑' k : ℤ, b' k ≤ C := by
      let x : ℝ := -u
      have hx : x ∈ K := by
        change x ∈ Set.Icc (-1 : ℝ) 0
        dsimp [x]
        constructor <;> linarith [hu.1, hu.2]
      have hpoint : ∀ k : ℤ, ‖integerWeightedPeriodEightCutoffFourierSchwartz N
          (x + (k : ℝ))‖ ≤ ‖(F.comp (ContinuousMap.addRight k)).restrict K‖ := by
        intro k
        dsimp [F]
        exact ContinuousMap.norm_coe_le_norm
          ((F.comp (ContinuousMap.addRight k)).restrict (K : Set ℝ)) ⟨x, hx⟩
      have hle : ∀ k, b' k ≤ ‖(F.comp (ContinuousMap.addRight k)).restrict K‖ := by
        intro k
        calc
          b' k ≤ ‖integerWeightedPeriodEightCutoffFourierSchwartz N
              ((k : ℝ) - u)‖ := hbc k
          _ ≤ ‖(F.comp (ContinuousMap.addRight k)).restrict K‖ := by
            simpa [x, sub_eq_add_neg, add_comm] using hpoint k
      have hsum : Summable b' := Summable.of_nonneg_of_le hb hle hseries
      exact ⟨hsum, Summable.tsum_le_tsum hle hsum hseries⟩
    dsimp [BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum]
    simpa [C, F, K, b', sub_eq_add_neg] using hmajor.2
  refine ⟨C, hC, ?_⟩
  intro ξ
  have h := BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum_uniform_bound
    (fun y => (1 + (y / 8) ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz (y / 8)‖) C hlocal (8 * ξ)
  have hscale : (fun k : ℤ =>
      (1 + ((k : ℝ) / 8 - ξ) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz ((k : ℝ) / 8 - ξ)‖) =
      fun k : ℤ => (1 + (((k : ℝ) - 8 * ξ) / 8) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz (((k : ℝ) - 8 * ξ) / 8)‖ := by
    funext k
    congr 2 <;> ring
  have hsummable :=
    BrownianSharp.AlignmentPaperLatticePeriodization.lattice_summable_of_fundamental
      (fun y => (1 + (y / 8) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz (y / 8)‖)
      (fun u hu => by
        have hl := hlocal u hu
        -- The compact-open majorant used above proves the same local series.
        simpa [BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum,
          C, F, K] using (by
            -- Rebuild the summability part from the local weighted Schwartz bound.
            let x : ℝ := -u
            let g : ℤ → ℝ := fun k =>
              (1 + (((k : ℝ) - u) / 8) ^ 2) ^ r *
                ‖cubeSpatialCutoffFourierSchwartz (((k : ℝ) - u) / 8)‖
            have hg : ∀ k, 0 ≤ g k := fun k => mul_nonneg
              (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
            have hK' : x ∈ K := by
              change x ∈ Set.Icc (-1 : ℝ) 0
              dsimp [x]
              constructor <;> linarith [hu.1, hu.2]
            have hle' : ∀ k, g k ≤
                ‖integerWeightedPeriodEightCutoffFourierSchwartz N (x + (k : ℝ))‖ := by
              intro k
              have hp := periodEightBesselKernel_le_integerWeighted r N hrN
                ((k : ℝ) - u)
              simpa [g, x, sub_eq_add_neg, add_comm] using hp
            have hle'' : ∀ k, g k ≤ ‖(F.comp (ContinuousMap.addRight k)).restrict K‖ := by
              intro k
              exact (hle' k).trans (ContinuousMap.norm_coe_le_norm
                ((F.comp (ContinuousMap.addRight k)).restrict (K : Set ℝ)) ⟨x, hK'⟩)
            exact Summable.of_nonneg_of_le hg hle''
              (integerWeightedPeriodEightCutoffFourier_translateSeries_summable N K)))
      (8 * ξ)
  have hscale : (fun k : ℤ =>
      (1 + ((k : ℝ) / 8 - ξ) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz ((k : ℝ) / 8 - ξ)‖) =
      fun k : ℤ => (1 + (((k : ℝ) - 8 * ξ) / 8) ^ 2) ^ r *
        ‖cubeSpatialCutoffFourierSchwartz (((k : ℝ) - 8 * ξ) / 8)‖ := by
    funext k
    congr 2 <;> ring
  constructor
  · rw [hscale]
    simpa [BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum] using hsummable
  · rw [hscale]
    simpa [BrownianSharp.AlignmentPaperLatticePeriodization.latticeSum] using h

/-- Integer Bessel-weighted cutoff kernel. Multiplication by this polynomial
weight preserves the Schwartz class, so its lattice translates have the same
compact-open summability property. -/
def integerWeightedCubeCutoffFourierSchwartz (N : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ N : ℝ) : ℂ))
    cubeSpatialCutoffFourierSchwartz

@[simp] theorem integerWeightedCubeCutoffFourierSchwartz_apply (N : ℕ) (x : ℝ) :
    integerWeightedCubeCutoffFourierSchwartz N x =
      ((1 + x ^ 2) ^ N : ℝ) * cubeSpatialCutoffFourierSchwartz x := by
  have hreal : (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ N).HasTemperateGrowth := by
    have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (N : ℝ)
    simpa only [Real.rpow_natCast] using h
  have hcomplex : (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ N : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp hreal
  rw [integerWeightedCubeCutoffFourierSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply hcomplex]
  simp [Complex.real_smul, Real.norm_eq_abs]

/-- A real Bessel weight of any exponent bounded by the chosen integer power
is dominated pointwise by the polynomially weighted Schwartz kernel. -/
theorem besselWeightedCutoffKernel_le_integerWeighted (r : ℝ) (N : ℕ)
    (hrN : r ≤ N) (x : ℝ) :
    (1 + x ^ 2) ^ r * ‖cubeSpatialCutoffFourierSchwartz x‖ ≤
      ‖integerWeightedCubeCutoffFourierSchwartz N x‖ := by
  have hbase : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hrN
  have hpowN : (1 + x ^ 2) ^ r ≤ (1 + x ^ 2) ^ N := by
    simpa only [Real.rpow_natCast] using hpow
  rw [integerWeightedCubeCutoffFourierSchwartz_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right hpowN (norm_nonneg _)

/-- The polynomially weighted scalar cutoff Fourier kernel is L¹. This is
the row-integral bound needed by the weighted Schur estimate. -/
theorem besselWeightedCutoffKernel_integrable (r : ℝ) (N : ℕ)
    (hr0 : 0 ≤ r) (hrN : r ≤ N) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz x‖) volume := by
  have hmajor : Integrable (fun x : ℝ =>
      ‖integerWeightedCubeCutoffFourierSchwartz N x‖) volume :=
    (integerWeightedCubeCutoffFourierSchwartz N).integrable.norm
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      (1 + x ^ 2) ^ r * ‖cubeSpatialCutoffFourierSchwartz x‖) volume := by
    fun_prop
  apply Integrable.mono' hmajor hmeas
  filter_upwards with x
  have hnonneg : 0 ≤ (1 + x ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz x‖ :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  simpa [Real.norm_of_nonneg hnonneg] using
    besselWeightedCutoffKernel_le_integerWeighted r N hrN x

/-- Translation/reflection invariance gives a uniform row integral for the
period-eight scalar cutoff kernel. -/
theorem periodEightBesselKernel_row_integral (r : ℝ) (N : ℕ)
    (hr0 : 0 ≤ r) (hrN : r ≤ N) (k : ℝ) :
    ∫ ξ : ℝ, (1 + (k / 8 - ξ) ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz (k / 8 - ξ)‖ ∂volume =
    ∫ y : ℝ, (1 + y ^ 2) ^ r *
      ‖cubeSpatialCutoffFourierSchwartz y‖ ∂volume := by
  let g : ℝ → ℝ := fun y => (1 + y ^ 2) ^ r *
    ‖cubeSpatialCutoffFourierSchwartz y‖
  have hg : Integrable g volume := by
    simpa [g] using besselWeightedCutoffKernel_integrable r N hr0 hrN
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun x : ℝ => x + k / 8) volume volume := by
    exact ⟨measurable_add_const _, map_add_right_eq_self volume (k / 8)⟩
  let e : ℝ ≃ₜ ℝ := {
    toEquiv := {
      toFun := fun x => k / 8 - x
      invFun := fun x => k / 8 - x
      left_inv := by intro x; dsimp; ring
      right_inv := by intro x; dsimp; ring }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hmp : MeasurePreserving e volume volume := by
    convert hadd.comp hneg using 1
    funext x
    change k / 8 - x = -x + k / 8
    ring
  calc
    _ = ∫ ξ, g (k / 8 - ξ) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by simp [g]
    _ = ∫ y, g y ∂volume := by
      simpa [e] using hmp.integral_comp e.measurableEmbedding g

/-- Tensor product of the scalar spatial cutoff used in the coefficient
Fubini identity. -/
def tensorCubeSpatialCutoff {d : ℕ} (x : Fin d → ℝ) : ℂ :=
  ∏ i, (cubeSpatialCutoff (x i) : ℂ)

theorem tensorCubeSpatialCutoff_integrable {d : ℕ} :
    Integrable (tensorCubeSpatialCutoff (d := d))
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  letI (i : Fin d) : SigmaFinite (volume : Measure ℝ) := inferInstance
  have hcut : Integrable (fun x : ℝ => (cubeSpatialCutoff x : ℂ)) volume := by
    change Integrable (cubeSpatialCutoffSchwartz : ℝ → ℂ) volume
    exact cubeSpatialCutoffSchwartz.integrable
  exact Integrable.fintype_prod (fun _ : Fin d => hcut)

/-- Fubini applies to the cutoff-feature integrand: integrable factors in the
spatial and spectral variables dominate the oscillatory factor, whose norm
is one. This is the exact product-integrability step needed to exchange the
cutoff integral with the Matérn inverse-Fourier integral. -/
theorem normOne_product_integral_swap {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (χ : α → ℂ) (A : β → ℂ) (q : α → β → ℂ)
    (hχ : Integrable χ μ) (hA : Integrable A ν)
    (hq : Measurable (Function.uncurry q))
    (hqnorm : ∀ x y, ‖q x y‖ = 1) :
    ∫ x, ∫ y, χ x * q x y * A y ∂ν ∂μ =
      ∫ y, ∫ x, χ x * q x y * A y ∂μ ∂ν := by
  apply integral_integral_swap
  have hdom : Integrable (fun p : α × β => ‖χ p.1‖ * ‖A p.2‖) (μ.prod ν) :=
    Integrable.mul_prod hχ.norm hA.norm
  have hχp : AEStronglyMeasurable (fun p : α × β => χ p.1) (μ.prod ν) :=
    hχ.aestronglyMeasurable.comp_fst
  have hAp : AEStronglyMeasurable (fun p : α × β => A p.2) (μ.prod ν) :=
    hA.aestronglyMeasurable.comp_snd
  have hqp : AEStronglyMeasurable (Function.uncurry q) (μ.prod ν) :=
    hq.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun p : α × β => χ p.1 * q p.1 p.2 * A p.2) (μ.prod ν) := by
    exact (hχp.mul hqp).mul hAp
  apply Integrable.mono' hdom hmeas
  filter_upwards with p
  calc
    ‖χ p.1 * q p.1 p.2 * A p.2‖ =
        ‖χ p.1‖ * 1 * ‖A p.2‖ := by rw [norm_mul, norm_mul, hqnorm]
    _ = ‖χ p.1‖ * ‖A p.2‖ := by ring
    _ ≤ ‖χ p.1‖ * ‖A p.2‖ := le_rfl

/-- Oscillatory factor for the Fourier coefficient of the localized
inverse-Fourier feature at integer frequency `k`. -/
def cutoffFeaturePhase {d : ℕ} (k x ξ : Fin d → ℝ) : ℂ :=
  star (complexSheetPhase x ξ) * complexSheetPhase k x

theorem cutoffFeaturePhase_measurable {d : ℕ} (k : Fin d → ℝ) :
    Measurable (Function.uncurry (fun x ξ => cutoffFeaturePhase k x ξ)) := by
  unfold cutoffFeaturePhase complexSheetPhase complexPhase
  fun_prop

theorem cutoffFeaturePhase_norm {d : ℕ} (k x ξ : Fin d → ℝ) :
    ‖cutoffFeaturePhase k x ξ‖ = 1 := by
  simp [cutoffFeaturePhase, complexSheetPhase_norm]

/-- Exact coefficient-side Fubini identity for a spatially cut off spectral
feature. The inner spatial integral is the Fourier kernel at the translated
frequency; the outer integral averages that kernel against the raw spectral
amplitude. -/
theorem cutoffFeature_coefficient_fubini {d : ℕ}
    (χ A : (Fin d → ℝ) → ℂ) (k : Fin d → ℝ)
    (hχ : Integrable χ (Measure.pi fun _ : Fin d => (volume : Measure ℝ)))
    (hA : Integrable A (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :
    ∫ x, ∫ ξ, χ x * cutoffFeaturePhase k x ξ * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) =
      ∫ ξ, (∫ x, χ x * cutoffFeaturePhase k x ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  calc
    _ = ∫ ξ, ∫ x, χ x * cutoffFeaturePhase k x ξ * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
          apply normOne_product_integral_swap
          · exact hχ
          · exact hA
          · exact cutoffFeaturePhase_measurable k
          · exact cutoffFeaturePhase_norm k
    _ = _ := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [integral_mul_const]

/-- The Fourier kernel of the tensor spatial cutoff, evaluated at the
frequency difference `k−ξ`. -/
def tensorCubeCutoffFourierKernel {d : ℕ} (k ξ : Fin d → ℝ) : ℂ :=
  ∫ x, tensorCubeSpatialCutoff x * cutoffFeaturePhase k x ξ
    ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))

/-- Scalar Fourier kernel of the compact spatial cutoff. -/
def scalarCubeCutoffFourierKernel (k ξ : ℝ) : ℂ :=
  ∫ x, (cubeSpatialCutoff x : ℂ) *
      (star (complexPhase x ξ) * complexPhase k x) ∂volume

/-- Identify the scalar cutoff kernel with the ordinary Schwartz Fourier
transform at the difference frequency. -/
theorem scalarCubeCutoffFourierKernel_eq_schwartzFourier (k ξ : ℝ) :
    scalarCubeCutoffFourierKernel k ξ =
      cubeSpatialCutoffFourierSchwartz (k - ξ) := by
  unfold scalarCubeCutoffFourierKernel
  change _ = 𝓕 cubeSpatialCutoffSchwartz (k - ξ)
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  change (cubeSpatialCutoff x : ℂ) *
      (star (complexPhase x ξ) * complexPhase k x) =
    Complex.exp ((↑(-2 * Real.pi * ((k - ξ) * x)) : ℂ) * Complex.I) *
      (cubeSpatialCutoff x : ℂ)
  have hphase : star (complexPhase x ξ) * complexPhase k x =
      Complex.exp ((↑(-2 * Real.pi * ((k - ξ) * x)) : ℂ) * Complex.I) := by
    rw [complexPhase, complexPhase, Complex.star_def,
      ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [hphase]
  ring

/-- The tensor cutoff Fourier kernel factors coordinatewise. This is what lets
the scalar weighted lattice estimate tensorize to the mixed product weight. -/
theorem tensorCubeCutoffFourierKernel_eq_prod {d : ℕ} (k ξ : Fin d → ℝ) :
    tensorCubeCutoffFourierKernel k ξ = ∏ i, scalarCubeCutoffFourierKernel (k i) (ξ i) := by
  have hfactor (i : Fin d) :
      Integrable (fun x : ℝ => (cubeSpatialCutoff x : ℂ) *
        (star (complexPhase x (ξ i)) * complexPhase (k i) x)) volume := by
    have hcut : Integrable (fun x : ℝ => (cubeSpatialCutoff x : ℂ)) volume := by
      change Integrable (cubeSpatialCutoffSchwartz : ℝ → ℂ) volume
      exact cubeSpatialCutoffSchwartz.integrable
    have hphase : Measurable (fun x : ℝ =>
        star (complexPhase x (ξ i)) * complexPhase (k i) x) := by
      unfold complexPhase
      fun_prop
    have hphaseBound : ∀ x, ‖star (complexPhase x (ξ i)) * complexPhase (k i) x‖ ≤ 1 := by
      intro x
      rw [norm_mul, norm_star, complexPhase_norm, complexPhase_norm]
      norm_num
    have hmul := hcut.bdd_mul hphase.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
    exact hmul.congr (Filter.Eventually.of_forall fun x => by ring)
  have hpoint (x : Fin d → ℝ) :
      tensorCubeSpatialCutoff x * cutoffFeaturePhase k x ξ =
        ∏ i, ((cubeSpatialCutoff (x i) : ℂ) *
          (star (complexPhase (x i) (ξ i)) * complexPhase (k i) (x i))) := by
    simp [tensorCubeSpatialCutoff, cutoffFeaturePhase, complexSheetPhase,
      Finset.prod_mul_distrib, mul_assoc]
  calc
    _ = ∫ x, ∏ i, ((cubeSpatialCutoff (x i) : ℂ) *
          (star (complexPhase (x i) (ξ i)) * complexPhase (k i) (x i)))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
          rw [tensorCubeCutoffFourierKernel]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∏ i, ∫ x, (cubeSpatialCutoff x : ℂ) *
          (star (complexPhase x (ξ i)) * complexPhase (k i) x) ∂volume := by
          exact integral_fintype_prod_eq_prod
            (fun i x => (cubeSpatialCutoff x : ℂ) *
              (star (complexPhase x (ξ i)) * complexPhase (k i) x))
    _ = ∏ i, scalarCubeCutoffFourierKernel (k i) (ξ i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rfl

/-- Product lattice estimate at the period-eight frequency grid. Its proof
uses the proved finite-coordinate `tsum` factorization, scalar Schwartz tail
bound, and the actual tensor cutoff Fourier kernel. -/
theorem tensorPeriodEightBesselKernel_lattice_bound {d : ℕ}
    (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Fin d → ℝ,
      Summable (fun k : Fin d → ℤ =>
        BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) ∧
      (∑' k : Fin d → ℤ,
        BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) ≤ C := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := periodEightBesselKernel_lattice_bound (r / 2) N hrN
  refine ⟨C₀ ^ d, by positivity, ?_⟩
  intro ξ
  let f : Fin d → ℤ → ℝ := fun i z =>
    (1 + ((z : ℝ) / 8 - ξ i) ^ 2) ^ (r / 2) *
      ‖cubeSpatialCutoffFourierSchwartz ((z : ℝ) / 8 - ξ i)‖
  have hfsum : ∀ i, Summable (f i) := by
    intro i
    simpa [f] using (hC₀bound (ξ i)).1
  have hpoint : ∀ k : Fin d → ℤ,
      BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ =
          ∏ i, f i (k i) := by
    intro k
    rw [tensorCubeCutoffFourierKernel_eq_prod]
    simp [f, BrownianSharp.AlignmentPaperMixedWeight.mixedWeight,
      scalarCubeCutoffFourierKernel_eq_schwartzFourier,
      Finset.prod_mul_distrib, Complex.norm_prod]
  have hsumle : ∀ i, ∑' z : ℤ, f i z ≤ C₀ := by
    intro i
    simpa [f] using (hC₀bound (ξ i)).2
  have hsumNonneg : ∀ i, 0 ≤ ∑' z : ℤ, f i z := by
    intro i
    exact tsum_nonneg fun z => mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  have hprodle : (∏ i, ∑' z : ℤ, f i z) ≤ C₀ ^ d := by
    calc
      (∏ i, ∑' z : ℤ, f i z) ≤ ∏ _i : Fin d, C₀ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact hsumNonneg i
        · intro i hi
          exact hsumle i
      _ = C₀ ^ d := by simp
  constructor
  · apply (summable_pi_prod_lattice d f hfsum).congr
    intro k
    exact (hpoint k).symm
  · rw [show (fun k : Fin d → ℤ =>
        BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
          ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖) =
        fun k => ∏ i, f i (k i) by funext k; exact hpoint k]
    rw [tsum_pi_prod_lattice d f hfsum]
    exact hprodle

/-- A uniform row-integral bound for the period-eight tensor cutoff kernel.
The scalar row mass factors by Fubini across the product coordinates. -/
theorem tensorPeriodEightBesselKernel_row_integral_bound {d : ℕ}
    (r : ℝ) (hr0 : 0 ≤ r) (N : ℕ) (hrN : r / 2 ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : Fin d → ℤ,
      ∫ ξ : Fin d → ℝ,
        BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≤ A := by
  let R : ℝ := ∫ y : ℝ, (1 + y ^ 2) ^ (r / 2) *
    ‖cubeSpatialCutoffFourierSchwartz y‖ ∂volume
  have hR : 0 ≤ R := by
    dsimp [R]
    exact integral_nonneg fun y => mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  refine ⟨R ^ d, by positivity, ?_⟩
  intro k
  let a : Fin d → ℝ → ℝ := fun i ξ =>
    (1 + (k i / 8 - ξ) ^ 2) ^ (r / 2) *
      ‖cubeSpatialCutoffFourierSchwartz (k i / 8 - ξ)‖
  have hpoint (ξ : Fin d → ℝ) :
      BrownianSharp.AlignmentPaperMixedWeight.mixedWeight (r / 2)
          (fun i => (k i : ℝ) / 8 - ξ i) *
        ‖tensorCubeCutoffFourierKernel (fun i => (k i : ℝ) / 8) ξ‖ =
          ∏ i, a i (ξ i) := by
    rw [tensorCubeCutoffFourierKernel_eq_prod]
    simp [a, BrownianSharp.AlignmentPaperMixedWeight.mixedWeight,
      scalarCubeCutoffFourierKernel_eq_schwartzFourier,
      Finset.prod_mul_distrib, Complex.norm_prod]
  calc
    _ = ∫ ξ : Fin d → ℝ, ∏ i, a i (ξ i)
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∏ i, ∫ ξ : ℝ, a i ξ ∂volume := by
          exact integral_fintype_prod_eq_prod a
    _ = R ^ d := by
          rw [show (∏ i, ∫ ξ : ℝ, a i ξ ∂volume) = ∏ _i : Fin d, R by
            apply Finset.prod_congr rfl
            intro i hi
            dsimp [a, R]
            exact periodEightBesselKernel_row_integral (r / 2) N
              (by linarith) hrN (k i : ℝ) ]
          simp
    _ ≤ R ^ d := le_rfl

/-- Actual tensor cutoff coefficient identity for an arbitrary L¹ raw spectral
amplitude. The only analytic input is precisely its Lebesgue integrability. -/
theorem tensorCubeCutoff_coefficient_fubini {d : ℕ}
    (A : (Fin d → ℝ) → ℂ) (k : Fin d → ℝ)
    (hA : Integrable A (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :
    ∫ x, ∫ ξ, tensorCubeSpatialCutoff x * cutoffFeaturePhase k x ξ * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) =
      ∫ ξ, tensorCubeCutoffFourierKernel k ξ * A ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  simpa [tensorCubeCutoffFourierKernel] using
    cutoffFeature_coefficient_fubini tensorCubeSpatialCutoff A k
      tensorCubeSpatialCutoff_integrable hA

open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentMaternSpectralWeights
open BrownianSharp.AlignmentMaternComplexFeature

/-- Continuous-to-discrete weighted Schur estimate. It is the integral
counterpart of `finiteSchur_l2_bound`: bounded row integrals and bounded
sampled column sums control all sampled convolutions in ℓ². -/
theorem finiteIntegralSchur_l2_bound {α I : Type*} [MeasurableSpace α]
    [Fintype I] (μ : Measure α) (K : I → α → ℝ) (f : α → ℝ)
    (A B : ℝ)
    (hKnonneg : ∀ i x, 0 ≤ K i x)
    (hf : MemLp f 2 μ) (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hweighted : ∀ i, MemLp (fun x => f x * Real.sqrt (K i x)) 2 μ)
    (hroot : ∀ i, MemLp (fun x => Real.sqrt (K i x)) 2 μ)
    (hrow : ∀ i, ∫ x, K i x ∂μ ≤ A)
    (hcol : ∀ x, ∑ i, K i x ≤ B) (hA : 0 ≤ A) :
    ∑ i, (∫ x, f x * K i x ∂μ) ^ 2 ≤ A * B * ∫ x, f x ^ 2 ∂μ := by
  have hrootSq (i : I) : (fun x => Real.sqrt (K i x) ^ 2) = K i := by
    funext x
    exact Real.sq_sqrt (hKnonneg i x)
  have hweightedSq (i : I) :
      (fun x => (f x * Real.sqrt (K i x)) ^ 2) = fun x => f x ^ 2 * K i x := by
    funext x
    rw [mul_pow, Real.sq_sqrt (hKnonneg i x)]
  have hKint (i : I) : Integrable (K i) μ := by
    have hs := (hroot i).integrable_sq
    exact hs.congr (Filter.Eventually.of_forall fun x => congrFun (hrootSq i) x)
  have hweightedInt (i : I) :
      Integrable (fun x => f x ^ 2 * K i x) μ := by
    have hs := (hweighted i).integrable_sq
    exact hs.congr (Filter.Eventually.of_forall fun x => congrFun (hweightedSq i) x)
  have hbaseInt : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hrowCauchy (i : I) :
      (∫ x, f x * K i x ∂μ) ^ 2 ≤
        (∫ x, f x ^ 2 * K i x ∂μ) * (∫ x, K i x ∂μ) := by
    let u : α → ℝ := fun x => f x * Real.sqrt (K i x)
    let v : α → ℝ := fun x => Real.sqrt (K i x)
    have hUpos : 0 ≤ᵐ[μ] u := by
      filter_upwards [hf_nonneg] with x hx
      exact mul_nonneg hx (Real.sqrt_nonneg _)
    have hVpos : 0 ≤ᵐ[μ] v := Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) (p := 2) (q := 2)
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      hUpos hVpos (by simpa [u] using hweighted i) (by simpa [v] using hroot i)
    have hmul : ∫ x, u x * v x ∂μ = ∫ x, f x * K i x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [u, v]
      calc
        f x * Real.sqrt (K i x) * Real.sqrt (K i x) =
            f x * (Real.sqrt (K i x) ^ 2) := by ring
        _ = f x * K i x := by rw [Real.sq_sqrt (hKnonneg i x)]
    have hU : ∫ x, u x ^ 2 ∂μ = ∫ x, f x ^ 2 * K i x ∂μ := by
      rw [show (fun x => u x ^ 2) = (fun x => f x ^ 2 * K i x) by
        funext x; exact congrFun (hweightedSq i) x]
    have hV : ∫ x, v x ^ 2 ∂μ = ∫ x, K i x ∂μ := by
      rw [show (fun x => v x ^ 2) = K i by funext x; exact congrFun (hrootSq i) x]
    have hholder :
        ∫ x, f x * K i x ∂μ ≤
          (∫ x, f x ^ 2 * K i x ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, K i x ∂μ) ^ (1 / 2 : ℝ) := by
      calc
        ∫ x, f x * K i x ∂μ = ∫ x, u x * v x ∂μ := hmul.symm
        _ ≤ (∫ x, u x ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, v x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hh
        _ = (∫ x, f x ^ 2 * K i x ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, K i x ∂μ) ^ (1 / 2 : ℝ) := by
              have hU' : ∫ x, u x ^ (2 : ℝ) ∂μ = ∫ x, f x ^ 2 * K i x ∂μ := by
                calc
                  ∫ x, u x ^ (2 : ℝ) ∂μ = ∫ x, u x ^ 2 ∂μ := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun x => Real.rpow_natCast (u x) 2
                  _ = _ := hU
              have hV' : ∫ x, v x ^ (2 : ℝ) ∂μ = ∫ x, K i x ∂μ := by
                calc
                  ∫ x, v x ^ (2 : ℝ) ∂μ = ∫ x, v x ^ 2 ∂μ := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun x => Real.rpow_natCast (v x) 2
                  _ = _ := hV
              apply congrArg₂ (· * ·)
              · exact congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) hU'
              · exact congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) hV'
    have hleft : 0 ≤ ∫ x, f x * K i x ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hf_nonneg] with x hx
      exact mul_nonneg hx (hKnonneg i x)
    have hE : 0 ≤ ∫ x, f x ^ 2 * K i x ∂μ := by
      apply integral_nonneg
      intro x
      exact mul_nonneg (sq_nonneg _) (hKnonneg i x)
    have hM : 0 ≤ ∫ x, K i x ∂μ := integral_nonneg fun x => hKnonneg i x
    have hholderSqrt :
        ∫ x, f x * K i x ∂μ ≤
          Real.sqrt (∫ x, f x ^ 2 * K i x ∂μ) * Real.sqrt (∫ x, K i x ∂μ) := by
      simpa [Real.sqrt_eq_rpow] using hholder
    have hrootBound := (sq_le_sq₀ hleft (mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hholderSqrt
    calc
      _ ≤ (Real.sqrt (∫ x, f x ^ 2 * K i x ∂μ) *
          Real.sqrt (∫ x, K i x ∂μ)) ^ 2 := hrootBound
      _ = (∫ x, f x ^ 2 * K i x ∂μ) * (∫ x, K i x ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hM]
  have hsumInt :
      ∑ i, ∫ x, f x ^ 2 * K i x ∂μ =
        ∫ x, f x ^ 2 * (∑ i, K i x) ∂μ := by
    calc
      ∑ i, ∫ x, f x ^ 2 * K i x ∂μ =
          ∫ x, ∑ i, (f x ^ 2 * K i x) ∂μ := by
            symm
            exact integral_finsetSum Finset.univ (fun i hi => hweightedInt i)
      _ = ∫ x, f x ^ 2 * (∑ i, K i x) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by simp [Finset.mul_sum]
  have hsumBound :
      ∫ x, f x ^ 2 * (∑ i, K i x) ∂μ ≤ B * ∫ x, f x ^ 2 ∂μ := by
    have hsumInteg : Integrable (fun x => f x ^ 2 * (∑ i, K i x)) μ := by
      have hsum' := integrable_finsetSum (s := Finset.univ)
        (fun i hi => hweightedInt i)
      have hfun : (fun x => ∑ i, f x ^ 2 * K i x) =
          fun x => f x ^ 2 * ∑ i, K i x := by
        funext x
        rw [Finset.mul_sum]
      exact hsum'.congr (Filter.Eventually.of_forall fun x => congrFun hfun x)
    calc
      _ ≤ ∫ x, f x ^ 2 * B ∂μ := by
        apply integral_mono
        · exact hsumInteg
        · exact hbaseInt.mul_const B
        · intro x
          exact mul_le_mul_of_nonneg_left (hcol x) (sq_nonneg (f x))
      _ = B * ∫ x, f x ^ 2 ∂μ := by rw [integral_mul_const]; ring
  calc
    ∑ i, (∫ x, f x * K i x ∂μ) ^ 2 ≤
        ∑ i, A * ∫ x, f x ^ 2 * K i x ∂μ := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ (∫ x, f x ^ 2 * K i x ∂μ) * (∫ x, K i x ∂μ) := hrowCauchy i
            _ ≤ (∫ x, f x ^ 2 * K i x ∂μ) * A :=
              mul_le_mul_of_nonneg_left (hrow i)
                (integral_nonneg fun x => mul_nonneg (sq_nonneg (f x)) (hKnonneg i x))
            _ = A * ∫ x, f x ^ 2 * K i x ∂μ := by ring
    _ = A * ∫ x, f x ^ 2 * (∑ i, K i x) ∂μ := by
          rw [← Finset.mul_sum, hsumInt.symm]
    _ ≤ A * (B * ∫ x, f x ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left hsumBound hA
    _ = A * B * ∫ x, f x ^ 2 ∂μ := by ring

/-- Finite-product Tonelli for products of nonnegative integrable real
functions, expressed as an ENNReal lintegral. This fills the exact bridge
needed when comparing product spectral measures by rectangle values. -/
theorem lintegral_fintype_prod_ofReal_eq_prod_integrals {d : ℕ}
    (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) volume)
    (hn : ∀ i x, 0 ≤ f i x) :
    ∫⁻ ξ, ∏ i, ENNReal.ofReal (f i (ξ i))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) =
      ∏ i, ENNReal.ofReal (∫ x, f i x) := by
  have hprod := Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ)) hf
  have hnonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin d => (volume : Measure ℝ))]
      fun ξ : Fin d → ℝ => ∏ i, f i (ξ i) := by
    filter_upwards with ξ
    exact Finset.prod_nonneg fun i hi => hn i (ξ i)
  have hpoint (ξ : Fin d → ℝ) :
      ∏ i, ENNReal.ofReal (f i (ξ i)) =
        ENNReal.ofReal (∏ i, f i (ξ i)) := by
    rw [ENNReal.ofReal_prod_of_nonneg]
    exact fun i hi => hn i (ξ i)
  calc
    _ = ∫⁻ ξ, ENNReal.ofReal (∏ i, f i (ξ i))
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ENNReal.ofReal (∫ ξ, ∏ i, f i (ξ i)
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) :=
          (ofReal_integral_eq_lintegral_ofReal hprod hnonneg).symm
    _ = ∏ i, ENNReal.ofReal (∫ x, f i x) := by
          rw [integral_fintype_prod_eq_prod]
          exact ENNReal.ofReal_prod_of_nonneg fun i hi =>
            integral_nonneg (fun x => hn i x)

/-- Product Lebesgue measure weighted by the product Matérn density. -/
def tensorDensity {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (ξ : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (density (κ i) h (ξ i))

/-- The product of the one-dimensional Matérn spectral measures is Lebesgue
product measure with product density. We prove equality on measurable product
rectangles, reducing their weighted measure to finite-product Fubini. -/
theorem pi_spectralMeasure_eq_withDensity {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    Measure.pi (fun i => spectralMeasure (κ i) h) =
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).withDensity
        (tensorDensity κ h) := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs) (tensorDensity κ h)]
  have hf (i : Fin d) : Integrable ((s i).indicator (density (κ i) h)) volume :=
    (density_integrable (κ i) h (hκ i) hh).indicator (hs i)
  have hnonneg (i : Fin d) (x : ℝ) :
      0 ≤ (s i).indicator (density (κ i) h) x := by
    by_cases hx : x ∈ s i
    · simp [hx, le_of_lt (density_pos (κ i) h x (hκ i))]
    · simp [hx]
  have hfun : (fun ξ : Fin d → ℝ =>
      Set.indicator (Set.univ.pi s) (tensorDensity κ h) ξ) =
    fun ξ => ∏ i, ENNReal.ofReal ((s i).indicator (density (κ i) h) (ξ i)) := by
    funext ξ
    by_cases hx : ξ ∈ Set.univ.pi s
    · have hxi : ∀ i, ξ i ∈ s i := Set.mem_univ_pi.mp hx
      simp [tensorDensity, hxi]
    · obtain ⟨i, hi⟩ : ∃ i, ξ i ∉ s i := by
        by_contra! hn
        exact hx (Set.mem_univ_pi.mpr hn)
      have hzero : (s i).indicator (density (κ i) h) (ξ i) = 0 :=
        Set.indicator_of_notMem hi _
      have hfactor : ENNReal.ofReal ((s i).indicator (density (κ i) h) (ξ i)) = 0 := by
        rw [hzero]
        simp
      rw [Set.indicator_of_notMem hx]
      simpa using (Finset.prod_eq_zero (s := Finset.univ)
        (f := fun j => ENNReal.ofReal ((s j).indicator (density (κ j) h) (ξ j)))
        (Finset.mem_univ i) hfactor).symm
  rw [hfun, lintegral_fintype_prod_ofReal_eq_prod_integrals
    (fun i => (s i).indicator (density (κ i) h)) hf hnonneg]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    ENNReal.ofReal (∫ x, (s i).indicator (density (κ i) h) x) =
        ∫⁻ x, ENNReal.ofReal ((s i).indicator (density (κ i) h) x) ∂volume :=
      ofReal_integral_eq_lintegral_ofReal (hf i)
        (Filter.Eventually.of_forall fun x => hnonneg i x)
    _ = ∫⁻ x in s i, ENNReal.ofReal (density (κ i) h x) ∂volume := by
      rw [← lintegral_indicator (hs i)]
      apply lintegral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s i <;> simp [hx, density_pos (κ i) h x (hκ i)]
  rw [spectralMeasure, withDensity_apply _ (hs i)]

/-- The Lebesgue Fourier amplitude associated to an arbitrary product spectral
source. Its density factor is the product of the one-dimensional Matérn
spectral densities. -/
def rawTensorFourierAmplitude {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (g : ComplexProductL2 κ h) (ξ : Fin d → ℝ) : ℂ :=
  (∏ i, (density (κ i) h (ξ i) : ℂ)) * g ξ

/-- The L² norm of a representative is the integral of its pointwise squared
norm. -/
theorem l2_normSq_eq_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : Lp ℂ 2 μ) : ∫ ξ, ‖g ξ‖ ^ 2 ∂μ = ‖g‖ ^ 2 := by
  have hnorm : ‖g‖ = Real.sqrt (∫ ξ, ‖g ξ‖ ^ 2 ∂μ) := by
    rw [Lp.norm_def]
    rw [(Lp.memLp g).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · simp only [ENNReal.toReal_ofNat]
      rw [Real.sqrt_eq_rpow]
      norm_num [one_div]
    · positivity
  have hI : 0 ≤ ∫ ξ, ‖g ξ‖ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  rw [hnorm, Real.sq_sqrt hI]

/-- Coordinatewise Bessel weight times coordinate spectral density. Under the
product spectral measure this is the Fourier-side Sobolev energy weight of
the raw amplitude `((∏ density_i) * g)`. -/
def tensorMaternSourceEnergyWeight {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (ξ : Fin d → ℝ) : ℝ :=
  ∏ i, (besselPrecisionWeight (h + 1/2) (ξ i) * density (κ i) h (ξ i))

/-- Any source in the full product spectral L² space has bounded mixed
Sobolev Fourier energy. This is the tensorized reverse-source estimate for
arbitrary sources, rather than only products of one-dimensional sources. -/
theorem tensorSourceEnergy_le_normSq {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    ∫ ξ, tensorMaternSourceEnergyWeight κ h ξ * ‖g ξ‖ ^ 2
        ∂Measure.pi (fun i => spectralMeasure (κ i) h) ≤
      (∏ i, Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))) * ‖g‖ ^ 2 := by
  let μ := Measure.pi (fun i => spectralMeasure (κ i) h)
  let C : ℝ := ∏ i, Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.prod_nonneg fun i hi => le_of_lt (Real.rpow_pos_of_pos
      (lt_min (by norm_num) (sq_pos_of_pos (hκ i))) _)
  have hgInt : Integrable (fun ξ => ‖g ξ‖ ^ 2) μ :=
    (Lp.memLp g).integrable_norm_pow (p := 2) (by norm_num : (2 : ℕ) ≠ 0)
  have hcoord (i : Fin d) (x : ℝ) :
      besselPrecisionWeight (h + 1/2) x * density (κ i) h x ≤
        Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2)) := by
    let r : ℝ := h + 1/2
    let L : ℝ := Real.rpow (min 1 ((κ i) ^ 2)) r
    let M : ℝ := maternPrecisionWeight (κ i) r x
    have hr : 0 < r := by dsimp [r]; linarith
    have hL : 0 < L := by
      dsimp [L]
      exact Real.rpow_pos_of_pos
        (lt_min (by norm_num) (sq_pos_of_pos (hκ i))) _
    have hρ : 0 < density (κ i) h x := density_pos (κ i) h x (hκ i)
    have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
      have hkSq : 0 < (κ i) ^ 2 := sq_pos_of_pos (hκ i)
      nlinarith [sq_nonneg x]
    have hMDens : M * density (κ i) h x = 1 := by
      dsimp [M, density, maternPrecisionWeight, r]
      rw [← Real.rpow_add hbase]
      simp
    have hcomp :=
      (matern_precision_weight_comparable (κ i) r x (hκ i) hr).1
    have hmul : besselPrecisionWeight r x * density (κ i) h x * L ≤ 1 := by
      calc
        _ = (L * besselPrecisionWeight r x) * density (κ i) h x := by ring
        _ ≤ M * density (κ i) h x := mul_le_mul_of_nonneg_right hcomp hρ.le
        _ = 1 := hMDens
    have hprod : (besselPrecisionWeight r x * density (κ i) h x) * L ≤ 1 := by
      nlinarith [hmul]
    have hb : besselPrecisionWeight r x * density (κ i) h x ≤ L⁻¹ := by
      simpa [one_div] using (le_div_iff₀ hL).2 hprod
    have hLinv : L⁻¹ = Real.rpow (min 1 ((κ i) ^ 2)) (-r) := by
      dsimp [L]
      rw [← Real.rpow_neg (le_of_lt
        (lt_min (by norm_num) (sq_pos_of_pos (hκ i))))]
    simpa [r, hLinv] using hb
  have hweight : ∀ ξ, tensorMaternSourceEnergyWeight κ h ξ ≤ C := by
    intro ξ
    dsimp [tensorMaternSourceEnergyWeight, C]
    apply Finset.prod_le_prod₀
    · intro i hi
      have hb : 0 < besselPrecisionWeight (h + 1/2) (ξ i) := by
        dsimp [besselPrecisionWeight]
        exact Real.rpow_pos_of_pos (by positivity) _
      exact mul_nonneg hb.le (density_pos (κ i) h (ξ i) (hκ i)).le
    · intro i hi
      exact hcoord i (ξ i)
  have h := calc
    ∫ ξ, tensorMaternSourceEnergyWeight κ h ξ * ‖g ξ‖ ^ 2 ∂μ ≤
        ∫ ξ, C * ‖g ξ‖ ^ 2 ∂μ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun ξ => by
              have hw : 0 ≤ tensorMaternSourceEnergyWeight κ h ξ := by
                dsimp [tensorMaternSourceEnergyWeight]
                exact Finset.prod_nonneg fun i hi => mul_nonneg
                  (le_of_lt (by
                    dsimp [besselPrecisionWeight]
                    exact Real.rpow_pos_of_pos (by positivity) _))
                  (density_pos (κ i) h (ξ i) (hκ i)).le
              exact mul_nonneg hw (sq_nonneg (‖g ξ‖))
          · exact hgInt.const_mul C
          · exact Filter.Eventually.of_forall fun ξ =>
              mul_le_mul_of_nonneg_right (hweight ξ) (sq_nonneg (‖g ξ‖))
    _ = C * ∫ ξ, ‖g ξ‖ ^ 2 ∂μ := by rw [integral_const_mul]
  simpa [μ, C, l2_normSq_eq_integral] using h

/-- Every product spectral L² source, after multiplication by its full
Matérn density, has bounded Lebesgue mixed-Sobolev Fourier energy. -/
theorem rawTensorFourierAmplitude_energy_le_normSq {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    ∫ ξ, (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
        ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≤
      (∏ i, Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))) * ‖g‖ ^ 2 := by
  let μ := Measure.pi (fun i => spectralMeasure (κ i) h)
  let volPi := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let F : (Fin d → ℝ) → ℝ := fun ξ =>
    (∏ i, besselPrecisionWeight (h + 1/2) (ξ i)) *
      ‖rawTensorFourierAmplitude κ h g ξ‖ ^ 2
  let G : (Fin d → ℝ) → ℝ := fun ξ =>
    tensorMaternSourceEnergyWeight κ h ξ * ‖g ξ‖ ^ 2
  have hdensity (i : Fin d) : Continuous (density (κ i) h) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    unfold density
    have hb : ContinuousAt (fun y : ℝ => (κ i) ^ 2 + y ^ 2) x := by fun_prop
    have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
      have hk : 0 < κ i := hκ i
      positivity
    exact hb.rpow_const (Or.inl (ne_of_gt hbase))
  have hmeasD : Measurable (tensorDensity κ h) := by
    unfold tensorDensity
    apply Finset.measurable_prod
    intro i hi
    exact ((hdensity i).measurable.comp (measurable_pi_apply i)).ennreal_ofReal
  have hfiniteD : ∀ᵐ ξ ∂volPi, tensorDensity κ h ξ < ⊤ := by
    filter_upwards with ξ
    unfold tensorDensity
    exact ENNReal.prod_lt_top fun i hi => ENNReal.ofReal_lt_top
  have hconvert : ∫ ξ, G ξ ∂μ =
      ∫ ξ, G ξ ∂(volPi.withDensity (tensorDensity κ h)) := by
    rw [← pi_spectralMeasure_eq_withDensity κ h hκ hh]
  have hweighted :
      ∫ ξ, G ξ ∂(volPi.withDensity (tensorDensity κ h)) =
        ∫ ξ, (tensorDensity κ h ξ).toReal * G ξ ∂volPi := by
    rw [integral_withDensity_eq_integral_toReal_smul hmeasD hfiniteD]
    simp only [smul_eq_mul]
  have hpoint (ξ : Fin d → ℝ) : F ξ = (tensorDensity κ h ξ).toReal * G ξ := by
    have hρ (i : Fin d) : 0 < density (κ i) h (ξ i) := density_pos _ _ _ (hκ i)
    have htoReal (i : Fin d) :
        (ENNReal.ofReal (density (κ i) h (ξ i))).toReal = density (κ i) h (ξ i) :=
      ENNReal.toReal_ofReal (hρ i).le
    have hprodρ : 0 ≤ ∏ i, density (κ i) h (ξ i) :=
      Finset.prod_nonneg fun i hi => (hρ i).le
    simp only [F, G, tensorDensity, ENNReal.toReal_prod, htoReal,
      rawTensorFourierAmplitude, ← Complex.ofReal_prod,
      Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hprodρ]
    rw [tensorMaternSourceEnergyWeight, Finset.prod_mul_distrib]
    ring
  have hspec := tensorSourceEnergy_le_normSq κ h hκ hh g
  change (∫ ξ, F ξ ∂volPi) ≤ _
  calc
    _ = ∫ ξ, (tensorDensity κ h ξ).toReal * G ξ ∂volPi := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ ξ, G ξ ∂(volPi.withDensity (tensorDensity κ h)) := hweighted.symm
    _ = ∫ ξ, G ξ ∂μ := hconvert.symm
    _ ≤ (∏ i, Real.rpow (min 1 ((κ i) ^ 2)) (-(h + 1/2))) * ‖g‖ ^ 2 := by
      simpa [μ, G, tensorMaternSourceEnergyWeight] using hspec

/-- The raw tensor Fourier amplitude is genuinely L¹. This is the required
integrability for its inverse-Fourier integral: L² sources are L¹ under the
finite spectral measure, and the product withDensity identity transfers that
fact to Lebesgue after multiplication by the product density. -/
theorem rawTensorFourierAmplitude_integrable {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) :
    Integrable (rawTensorFourierAmplitude κ h g)
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) := by
  let μ := Measure.pi (fun i => spectralMeasure (κ i) h)
  let volPi := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  have hgμ : Integrable g μ :=
    (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdensity (i : Fin d) : Continuous (density (κ i) h) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    unfold density
    have hb : ContinuousAt (fun y : ℝ => (κ i) ^ 2 + y ^ 2) x := by fun_prop
    have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
      have hk : 0 < κ i := hκ i
      positivity
    exact hb.rpow_const (Or.inl (ne_of_gt hbase))
  have hmeasD : Measurable (tensorDensity κ h) := by
    unfold tensorDensity
    apply Finset.measurable_prod
    intro i hi
    exact ((hdensity i).measurable.comp (measurable_pi_apply i)).ennreal_ofReal
  have hfiniteD : ∀ᵐ ξ ∂volPi, tensorDensity κ h ξ < ⊤ := by
    filter_upwards with ξ
    unfold tensorDensity
    exact ENNReal.prod_lt_top fun i hi => ENNReal.ofReal_lt_top
  have hgDensity : Integrable g (volPi.withDensity (tensorDensity κ h)) := by
    rw [← pi_spectralMeasure_eq_withDensity κ h hκ hh]
    exact hgμ
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul' hmeasD hfiniteD).mp hgDensity
  have hD (ξ : Fin d → ℝ) :
      (tensorDensity κ h ξ).toReal = ∏ i, density (κ i) h (ξ i) := by
    rw [tensorDensity, ENNReal.toReal_prod]
    congr 1
    funext i
    exact ENNReal.toReal_ofReal (density_pos (κ i) h (ξ i) (hκ i)).le
  have heq (ξ : Fin d → ℝ) :
      (tensorDensity κ h ξ).toReal • g ξ = rawTensorFourierAmplitude κ h g ξ := by
    rw [hD ξ, rawTensorFourierAmplitude, ← Complex.ofReal_prod]
    rw [Complex.real_smul]
  exact hscaled.congr (Filter.Eventually.of_forall heq)

/-- The complex tensor feature evaluated against any L² spectral source is
the inverse-Fourier integral of its raw tensor density amplitude. The source
is integrable because the spectral measures are finite and the phase is
bounded; the density change of measure is the indexed product identity above. -/
theorem rawComplexSheetFeature_inner_eq_rawTensorFourierIntegral {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (t : Fin d → ℝ) (g : ComplexProductL2 κ h) :
    inner ℂ (rawComplexSheetFeature κ h hκ hh t) g =
      ∫ ξ, star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ
        ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  let μ := Measure.pi (fun i => spectralMeasure (κ i) h)
  let volPi := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let F : (Fin d → ℝ) → ℂ := fun ξ => star (complexSheetPhase t ξ) * g ξ
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  have hphase := complexSheetPhase_memLp κ h hκ hh t
  have hrep := hphase.coeFn_toLp
  have hinner : inner ℂ (rawComplexSheetFeature κ h hκ hh t) g = ∫ ξ, F ξ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep] with ξ hξ
    change inner ℂ ((hphase.toLp (complexSheetPhase t)) ξ) (g ξ) = F ξ
    rw [hξ, RCLike.inner_apply']
    rfl
  have hdensity (i : Fin d) : Continuous (density (κ i) h) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    unfold density
    have hb : ContinuousAt (fun y : ℝ => (κ i) ^ 2 + y ^ 2) x := by fun_prop
    have hbase : 0 < (κ i) ^ 2 + x ^ 2 := by
      have hk : 0 < κ i := hκ i
      positivity
    exact hb.rpow_const (Or.inl (ne_of_gt hbase))
  have hmeasD : Measurable (tensorDensity κ h) := by
    unfold tensorDensity
    apply Finset.measurable_prod
    intro i hi
    exact ((hdensity i).measurable.comp (measurable_pi_apply i)).ennreal_ofReal
  have hfiniteD : ∀ᵐ ξ ∂volPi, tensorDensity κ h ξ < ⊤ := by
    filter_upwards with ξ
    unfold tensorDensity
    exact ENNReal.prod_lt_top fun i hi => ENNReal.ofReal_lt_top
  have hchange : ∫ ξ, F ξ ∂μ =
      ∫ ξ, F ξ ∂(volPi.withDensity (tensorDensity κ h)) := by
    rw [← pi_spectralMeasure_eq_withDensity κ h hκ hh]
  have hweighted :
      ∫ ξ, F ξ ∂(volPi.withDensity (tensorDensity κ h)) =
        ∫ ξ, (tensorDensity κ h ξ).toReal • F ξ ∂volPi :=
    integral_withDensity_eq_integral_toReal_smul hmeasD hfiniteD F
  have hD (ξ : Fin d → ℝ) :
      (tensorDensity κ h ξ).toReal = ∏ i, density (κ i) h (ξ i) := by
    rw [tensorDensity, ENNReal.toReal_prod]
    congr 1
    funext i
    exact ENNReal.toReal_ofReal (density_pos (κ i) h (ξ i) (hκ i)).le
  have hpoint (ξ : Fin d → ℝ) :
      (tensorDensity κ h ξ).toReal • F ξ =
        star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ := by
    dsimp [F]
    rw [hD ξ, rawTensorFourierAmplitude]
    rw [← Complex.ofReal_prod]
    ring
  calc
    _ = ∫ ξ, F ξ ∂μ := hinner
    _ = ∫ ξ, F ξ ∂(volPi.withDensity (tensorDensity κ h)) := hchange
    _ = ∫ ξ, (tensorDensity κ h ξ).toReal • F ξ ∂volPi := hweighted
    _ = ∫ ξ, star (complexSheetPhase t ξ) * rawTensorFourierAmplitude κ h g ξ ∂volPi := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint

/-- The normalized continuous complex Matérn feature operator itself is the
real part of the inverse-Fourier integral, with the normalization scalar
shown explicitly. -/
theorem complexSheetFeature_operator_eq_fourierIntegral {d : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (g : ComplexProductL2 κ h) (t : HaarQuarter.BrownianCubeAnchor d) :
    AlignmentFractionalSheetRKHS.featureOperator
        (complexSheetFeature κ h hκ hh) g t =
      complexFeatureScale κ h hκ hh *
        (∫ ξ, star (complexSheetPhase t.val ξ) *
          rawTensorFourierAmplitude κ h g ξ
          ∂Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).re := by
  have hreal (x y : ComplexProductL2 κ h) :
      inner ℝ x y = (inner ℂ x y).re := by
    rw [L2.inner_def, L2.inner_def]
    simpa only [Complex.inner, RCLike.inner_apply, RCLike.re_to_complex] using
      (integral_re (L2.integrable_inner (𝕜 := ℂ) x y))
  rw [AlignmentFractionalSheetRKHS.featureOperator_apply]
  change inner ℝ (normalizedComplexFeatureFun κ h hκ hh t) g = _
  rw [normalizedComplexFeatureFun, real_inner_smul_left, hreal,
    rawComplexSheetFeature_inner_eq_rawTensorFourierIntegral]

/-- The Bessel Sobolev weight times the Matérn density is uniformly bounded.
The constant depends only on the fixed range parameter and smoothness. -/
theorem besselWeight_mul_density_le (κ h ξ : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) :
    besselPrecisionWeight (h + 1/2) ξ * density κ h ξ ≤
      Real.rpow (min 1 (κ ^ 2)) (-(h + 1/2)) := by
  let r : ℝ := h + 1/2
  let L : ℝ := Real.rpow (min 1 (κ ^ 2)) r
  let M : ℝ := maternPrecisionWeight κ r ξ
  have hr : 0 < r := by dsimp [r]; linarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos (lt_min (by norm_num) (sq_pos_of_pos hκ)) _
  have hρ : 0 < density κ h ξ := density_pos κ h ξ hκ
  have hbase : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  have hMDens : M * density κ h ξ = 1 := by
    dsimp [M, density, maternPrecisionWeight, r]
    rw [← Real.rpow_add hbase]
    simp
  have hcomp := (matern_precision_weight_comparable κ r ξ hκ hr).1
  have hmul : besselPrecisionWeight r ξ * density κ h ξ * L ≤ 1 := by
    calc
      besselPrecisionWeight r ξ * density κ h ξ * L =
          (L * besselPrecisionWeight r ξ) * density κ h ξ := by ring
      _ ≤ M * density κ h ξ :=
        mul_le_mul_of_nonneg_right hcomp hρ.le
      _ = 1 := hMDens
  have hprod : (besselPrecisionWeight r ξ * density κ h ξ) * L ≤ 1 := by
    nlinarith [hmul]
  have hbound : besselPrecisionWeight r ξ * density κ h ξ ≤ L⁻¹ := by
    simpa [one_div] using (le_div_iff₀ hL).2 hprod
  have hLinv : L⁻¹ = Real.rpow (min 1 (κ ^ 2)) (-r) := by
    dsimp [L]
    rw [← Real.rpow_neg (le_of_lt (lt_min (by norm_num) (sq_pos_of_pos hκ)))]
  simpa [r, hLinv] using hbound

end BrownianSharp.AlignmentPaperMaternSourceEnergy
