import BrownianSharp.TorusFoundations
import BrownianSharp.UnitTorusMeasure
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! L1 Fourier uniqueness helpers on the normalized product torus. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
open scoped ComplexConjugate

namespace BrownianSharp.AlignmentPeriodicL1Fourier

open BrownianSharp.Torus
open UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance (d : ℕ) : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin d))) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  infer_instance

/-- An integrable function whose torus Fourier coefficients vanish annihilates
every continuous test function. -/
theorem integral_mul_continuous_eq_zero_of_mFourierCoeff_eq_zero {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (hcoeff : ∀ k : Fin d → ℤ, mFourierCoeff f k = 0)
    (g : C(UnitAddTorus (Fin d), ℂ)) :
    ∫ x, f x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) = 0 := by
  classical
  let Llin : C(UnitAddTorus (Fin d), ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun h => ∫ x, f x * h x ∂(volume : Measure (UnitAddTorus (Fin d)))
    map_add' := by
      intro h j
      have h1 := hf.mul_bdd h.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => h.norm_coe_le_norm x)
      have h2 := hf.mul_bdd j.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => j.norm_coe_le_norm x)
      rw [← integral_add h1 h2]
      congr 1 <;> ext x <;> simp [mul_add]
    map_smul' := by
      intro c h
      have h1 := hf.mul_bdd h.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => h.norm_coe_le_norm x)
      change (∫ x, f x * (c * h x) ∂(volume : Measure (UnitAddTorus (Fin d)))) = _
      calc
        _ = ∫ x, c * (f x * h x) ∂(volume : Measure (UnitAddTorus (Fin d))) := by
          congr 1
          ext x
          ring
        _ = c * ∫ x, f x * h x ∂(volume : Measure (UnitAddTorus (Fin d))) := by
          rw [integral_const_mul]
  }
  have hbound : ∀ h, ‖Llin h‖ ≤ (∫ x, ‖f x‖ ∂(volume : Measure (UnitAddTorus (Fin d)))) * ‖h‖ := by
    intro h
    have hmul : Integrable (fun x => f x * h x) (volume : Measure (UnitAddTorus (Fin d))) :=
      hf.mul_bdd h.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => h.norm_coe_le_norm x)
    calc
      _ = ‖∫ x, f x * h x ∂(volume : Measure (UnitAddTorus (Fin d)))‖ := rfl
      _ ≤ ∫ x, ‖f x * h x‖ ∂(volume : Measure (UnitAddTorus (Fin d))) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖f x‖ * ‖h‖ ∂(volume : Measure (UnitAddTorus (Fin d))) := by
        apply integral_mono_ae hmul.norm (hf.norm.mul_const _)
        filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖f x‖ ∂(volume : Measure (UnitAddTorus (Fin d)))) * ‖h‖ := by
        rw [integral_mul_const]
  let L : C(UnitAddTorus (Fin d), ℂ) →L[ℂ] ℂ :=
    Llin.mkContinuous (∫ x, ‖f x‖ ∂(volume : Measure (UnitAddTorus (Fin d)))) hbound
  have hspan : Submodule.span ℂ (Set.range (mFourier (d := Fin d))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change ∫ x, f x * mFourier k x ∂(volume : Measure (UnitAddTorus (Fin d))) = 0
    have hc := hcoeff (-k)
    simp only [mFourierCoeff, neg_neg] at hc
    change (∫ x, mFourier k x • f x ∂(volume : Measure (UnitAddTorus (Fin d)))) = 0 at hc
    simpa [smul_eq_mul, mul_comm] using hc
  have hclosed : IsClosed (L.ker : Set C(UnitAddTorus (Fin d), ℂ)) :=
    ContinuousLinearMap.isClosed_ker L
  have hclosure := Submodule.topologicalClosure_minimal (Submodule.span ℂ
    (Set.range (mFourier (d := Fin d)))) hspan hclosed
  rw [UnitAddTorus.span_mFourier_closure_eq_top] at hclosure
  change ∫ x, f x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) = 0
  have hzero : L g = 0 := by
    have hmem : g ∈ L.ker := hclosure (by simp)
    exact hmem
  exact hzero

/-- An integrable real function on the product torus is determined almost
everywhere by all of its Fourier coefficients. -/
theorem ae_eq_zero_of_mFourierCoeff_eq_zero {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (hcoeff : ∀ k : Fin d → ℤ,
      mFourierCoeff (fun x => (f x : ℂ)) k = 0) : f =ᵐ[volume] 0 := by
  classical
  let fp : UnitAddTorus (Fin d) → ℝ := fun x => max (f x) 0
  let fn : UnitAddTorus (Fin d) → ℝ := fun x => max (-f x) 0
  have hfp : Integrable fp (volume : Measure (UnitAddTorus (Fin d))) := by
    apply hf.abs.mono'
    · dsimp [fp]
      exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
        hf.1
    · filter_upwards with x
      dsimp [fp]
      by_cases hx : 0 ≤ f x
      · simp [max_eq_left hx]
      · have hx' : f x < 0 := lt_of_not_ge hx
        simp [max_eq_right (le_of_lt hx')]
  have hfn : Integrable fn (volume : Measure (UnitAddTorus (Fin d))) := by
    apply hf.neg.abs.mono'
    · dsimp [fn]
      exact (continuous_neg.max continuous_const).comp_aestronglyMeasurable
        hf.1
    · filter_upwards with x
      dsimp [fn]
      by_cases hx : 0 ≤ -f x
      · simp [max_eq_left hx]
      · have hx' : -f x < 0 := lt_of_not_ge hx
        simp [max_eq_right (le_of_lt hx')]
  let μp : Measure (UnitAddTorus (Fin d)) :=
    volume.withDensity (fun x => ENNReal.ofReal (fp x))
  let μn : Measure (UnitAddTorus (Fin d)) :=
    volume.withDensity (fun x => ENNReal.ofReal (fn x))
  have hμp : IsFiniteMeasure μp := by
    dsimp [μp, fp]
    exact isFiniteMeasure_withDensity_ofReal hfp.hasFiniteIntegral
  have hμn : IsFiniteMeasure μn := by
    dsimp [μn, fn]
    exact isFiniteMeasure_withDensity_ofReal hfn.hasFiniteIntegral
  let νp : FiniteMeasure (UnitAddTorus (Fin d)) := ⟨μp, hμp⟩
  let νn : FiniteMeasure (UnitAddTorus (Fin d)) := ⟨μn, hμn⟩
  have hν : νp = νn := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro g
    have hgp : Integrable (fun x => fp x * g x) (volume : Measure (UnitAddTorus (Fin d))) :=
      hfp.mul_bdd g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
    have hgn : Integrable (fun x => fn x * g x) (volume : Measure (UnitAddTorus (Fin d))) :=
      hfn.mul_bdd g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
    have hfg : Integrable (fun x => f x * g x) (volume : Measure (UnitAddTorus (Fin d))) :=
      hf.mul_bdd g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
    have hcomplex : Integrable (fun x => (f x : ℂ))
        (volume : Measure (UnitAddTorus (Fin d))) :=
      Complex.ofRealCLM.integrable_comp hf
    let gc : C(UnitAddTorus (Fin d), ℂ) :=
      ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
    have hzero := integral_mul_continuous_eq_zero_of_mFourierCoeff_eq_zero
      (fun x => (f x : ℂ)) hcomplex hcoeff gc
    have hrealzero : ∫ x, f x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) = 0 := by
      have hmap := Complex.ofRealCLM.integral_comp_comm hfg
      apply Complex.ofReal_injective
      calc
        Complex.ofReal (∫ x, f x * g x ∂(volume : Measure (UnitAddTorus (Fin d)))) =
            ∫ x, ((f x * g x : ℝ) : ℂ) ∂(volume : Measure (UnitAddTorus (Fin d))) := hmap.symm
        _ = ∫ x, (f x : ℂ) * gc x ∂(volume : Measure (UnitAddTorus (Fin d))) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [gc]
        _ = 0 := hzero
    have hdecomp : (fun x => f x * g x) = fun x => fp x * g x - fn x * g x := by
      funext x
      dsimp [fp, fn]
      by_cases hx : 0 ≤ f x
      · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      · have hx' : f x < 0 := lt_of_not_ge hx
        simp [max_eq_right (le_of_lt hx'), max_eq_left (le_of_lt (neg_pos.mpr hx'))]
    have hsplit : ∫ x, f x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) =
        (∫ x, fp x * g x ∂(volume : Measure (UnitAddTorus (Fin d)))) -
          ∫ x, fn x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) := by
      rw [hdecomp, integral_sub hgp hgn]
    have hrealpair : ∫ x, fp x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) =
        ∫ x, fn x * g x ∂(volume : Measure (UnitAddTorus (Fin d))) := by
      linarith [hsplit, hrealzero]
    have hfpAEStr : AEStronglyMeasurable fp (volume : Measure (UnitAddTorus (Fin d))) := by
      dsimp [fp]
      exact (continuous_id.max continuous_const).comp_aestronglyMeasurable hf.1
    have hfnAEStr : AEStronglyMeasurable fn (volume : Measure (UnitAddTorus (Fin d))) := by
      dsimp [fn]
      exact (continuous_neg.max continuous_const).comp_aestronglyMeasurable hf.1
    have hdensp : AEMeasurable (fun x => ENNReal.ofReal (fp x))
        (volume : Measure (UnitAddTorus (Fin d))) :=
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable hfpAEStr.aemeasurable
    have hdensn : AEMeasurable (fun x => ENNReal.ofReal (fn x))
        (volume : Measure (UnitAddTorus (Fin d))) :=
      ENNReal.continuous_ofReal.measurable.comp_aemeasurable hfnAEStr.aemeasurable
    have hpint := integral_withDensity_eq_integral_toReal_smul₀ hdensp
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g
    have hnint := integral_withDensity_eq_integral_toReal_smul₀ hdensn
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g
    change ∫ x, g x ∂μp = ∫ x, g x ∂μn
    rw [hpint, hnint]
    have hpto : ∀ x, (ENNReal.ofReal (fp x)).toReal = fp x := by
      intro x
      exact ENNReal.toReal_ofReal (le_max_right (f x) 0)
    have hnto : ∀ x, (ENNReal.ofReal (fn x)).toReal = fn x := by
      intro x
      exact ENNReal.toReal_ofReal (le_max_right (-f x) 0)
    simp_rw [hpto, hnto, smul_eq_mul]
    exact hrealpair
  have hmeas : (νp : Measure (UnitAddTorus (Fin d))) = (νn : Measure (UnitAddTorus (Fin d))) :=
    congrArg (fun ν : FiniteMeasure (UnitAddTorus (Fin d)) =>
      (ν : Measure (UnitAddTorus (Fin d)))) hν
  change μp = μn at hmeas
  have hfpAEStr : AEStronglyMeasurable fp (volume : Measure (UnitAddTorus (Fin d))) := by
    dsimp [fp]
    exact (continuous_id.max continuous_const).comp_aestronglyMeasurable hf.1
  have hfnAEStr : AEStronglyMeasurable fn (volume : Measure (UnitAddTorus (Fin d))) := by
    dsimp [fn]
    exact (continuous_neg.max continuous_const).comp_aestronglyMeasurable hf.1
  have hmeas' : volume.withDensity (fun x => ENNReal.ofReal (fp x)) =
      volume.withDensity (fun x => ENNReal.ofReal (fn x)) := by
    simpa only [μp, μn] using hmeas
  have hden : (fun x => ENNReal.ofReal (fp x)) =ᵐ[volume]
      fun x => ENNReal.ofReal (fn x) :=
    (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (f := fun x => ENNReal.ofReal (fp x))
      (g := fun x => ENNReal.ofReal (fn x))
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hfpAEStr.aemeasurable)
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hfnAEStr.aemeasurable)
      ).mp hmeas'
  filter_upwards [hden] with x hx
  have hparts : fp x = fn x := by
    dsimp [fp, fn] at hx ⊢
    apply (ENNReal.ofReal_eq_ofReal_iff (le_max_right (f x) 0)
      (le_max_right (-f x) 0)).mp
    exact hx
  have hfx : f x = 0 := by
    dsimp [fp, fn] at hparts
    by_cases h : 0 ≤ f x
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)] at hparts
      linarith
    · have hn : f x < 0 := lt_of_not_ge h
      simp [max_eq_right (le_of_lt hn), max_eq_left (le_of_lt (neg_pos.mpr hn))] at hparts
      linarith
  exact hfx

/-- An integrable real source and a continuous function with the same torus
Fourier coefficients represent the same L1 equivalence class. -/
theorem ae_eq_continuous_of_mFourierCoeff_eq {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (g : RealPeriodic d)
    (hg : Integrable (fun x => g x) (volume : Measure (UnitAddTorus (Fin d))))
    (hcoeff : ∀ k : Fin d → ℤ,
      mFourierCoeff (fun x => (f x : ℂ)) k = realPeriodicFourierCoeff g k) :
    f =ᵐ[volume] fun x => g x := by
  have hfC : Integrable (fun x => (f x : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := Complex.ofRealCLM.integrable_comp hf
  have hgC : Integrable (fun x => (g x : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := Complex.ofRealCLM.integrable_comp hg
  have hdiff : Integrable (fun x => f x - g x)
      (volume : Measure (UnitAddTorus (Fin d))) := hf.sub hg
  have hdiffCoeff : ∀ k : Fin d → ℤ,
      mFourierCoeff (fun x => ((f x - g x : ℝ) : ℂ)) k = 0 := by
    intro k
    have hcharF : Integrable (fun x => mFourier (-k) x • (f x : ℂ))
        (volume : Measure (UnitAddTorus (Fin d))) :=
      hfC.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          calc
            ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
            _ = 1 := mFourier_norm)
    have hcharG : Integrable (fun x => mFourier (-k) x • (g x : ℂ))
        (volume : Measure (UnitAddTorus (Fin d))) :=
      hgC.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          calc
            ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
            _ = 1 := mFourier_norm)
    change ∫ x, mFourier (-k) x • ((f x - g x : ℝ) : ℂ) ∂
      (volume : Measure (UnitAddTorus (Fin d))) = 0
    have hpoint : (fun x => mFourier (-k) x • ((f x - g x : ℝ) : ℂ)) =
        fun x => mFourier (-k) x • (f x : ℂ) - mFourier (-k) x • (g x : ℂ) := by
      funext x
      simp only [Complex.ofReal_sub, smul_sub]
    rw [hpoint, integral_sub hcharF hcharG]
    change mFourierCoeff (fun x => (f x : ℂ)) k -
      mFourierCoeff (fun x => (g x : ℂ)) k = 0
    rw [hcoeff k]
    change realPeriodicFourierCoeff g k -
      mFourierCoeff (fun x => (g x : ℂ)) k = 0
    change mFourierCoeff (complexifyRealPeriodic g) k -
      mFourierCoeff (fun x => (g x : ℂ)) k = 0
    unfold complexifyRealPeriodic
    exact sub_self _
  have hzero := ae_eq_zero_of_mFourierCoeff_eq_zero (fun x => f x - g x) hdiff hdiffCoeff
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

private theorem mFourierCoeff_realPart_formula {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (k : Fin d → ℤ) :
    mFourierCoeff (fun x => ((f x).re : ℂ)) k =
      (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 := by
  have hreal : Integrable (fun x => ((f x).re : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact Complex.ofRealCLM.integrable_comp
      ((@RCLike.reCLM ℂ _).integrable_comp hf)
  have h1 : Integrable (fun x => mFourier (-k) x * f x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hf.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h2 : Integrable (fun x => mFourier k x * f x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hf.bdd_smul 1 (mFourier k).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier k x‖ ≤ ‖mFourier k‖ := (mFourier k).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h3 : Integrable (fun x => mFourier (-k) x * ((f x).re : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hreal.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have hrealFormula (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp <;> ring
  have hp : (fun x => mFourier (-k) x • ((f x).re : ℂ)) =
      fun x => (mFourier (-k) x * f x + conj (mFourier k x * f x)) / 2 := by
    funext x
    simp only [smul_eq_mul]
    rw [hrealFormula]
    simp only [map_mul, mFourier_neg]
    ring
  calc
    mFourierCoeff (fun x => ((f x).re : ℂ)) k =
        ∫ x, (mFourier (-k) x * f x + conj (mFourier k x * f x)) / 2 ∂
          (volume : Measure (UnitAddTorus (Fin d))) := by
      unfold mFourierCoeff
      rw [integral_congr_ae (Filter.Eventually.of_forall (congrFun hp))]
    _ = (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 := by
      have h2c : Integrable (fun x => conj (mFourier k x * f x))
          (volume : Measure (UnitAddTorus (Fin d))) := by
        exact h2.congr'_enorm
          (Complex.continuous_conj.comp_aestronglyMeasurable h2.1)
          (Filter.Eventually.of_forall fun x => by simp)
      have hsum : Integrable (fun x => mFourier (-k) x * f x +
          conj (mFourier k x * f x)) (volume : Measure (UnitAddTorus (Fin d))) := h1.add h2c
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add h1 h2c, integral_conj]
      simp only [mFourierCoeff, smul_eq_mul, neg_neg, div_eq_mul_inv]

/-- Complex-valued L1 Fourier coefficients also determine the function almost everywhere. -/
theorem ae_eq_zero_of_mFourierCoeff_eq_zero_complex {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (hcoeff : ∀ k : Fin d → ℤ, mFourierCoeff f k = 0) :
    f =ᵐ[volume] 0 := by
  have hReInt : Integrable (fun x => (f x).re)
      (volume : Measure (UnitAddTorus (Fin d))) := (@RCLike.reCLM ℂ _).integrable_comp hf
  have hImInt : Integrable (fun x => (f x).im)
      (volume : Measure (UnitAddTorus (Fin d))) := (@RCLike.imCLM ℂ _).integrable_comp hf
  have hReCoeff : ∀ k, mFourierCoeff (fun x => ((f x).re : ℂ)) k = 0 := by
    intro k
    rw [mFourierCoeff_realPart_formula f hf k, hcoeff k, hcoeff (-k)]
    simp
  have hRe := ae_eq_zero_of_mFourierCoeff_eq_zero (fun x => (f x).re) hReInt hReCoeff
  let fI : UnitAddTorus (Fin d) → ℂ := fun x => -Complex.I * f x
  have hfI : Integrable fI (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [fI] using hf.const_mul (-Complex.I)
  have hcoeffI : ∀ k, mFourierCoeff fI k = 0 := by
    intro k
    calc
      mFourierCoeff fI k =
        ∫ x, mFourier (-k) x • (-Complex.I * f x) ∂
          (volume : Measure (UnitAddTorus (Fin d))) := rfl
      _ =
        ∫ x, (-Complex.I) * (mFourier (-k) x • f x) ∂
          (volume : Measure (UnitAddTorus (Fin d))) := by
            congr 1
            funext x
            simp only [smul_eq_mul]
            ring
      _ = (-Complex.I) * mFourierCoeff f k := by
        rw [mFourierCoeff]
        exact integral_const_mul _ _
      _ = 0 := by rw [hcoeff k]; simp
  have hImCoeff : ∀ k, mFourierCoeff (fun x => ((fI x).re : ℂ)) k = 0 := by
    intro k
    rw [mFourierCoeff_realPart_formula fI hfI k, hcoeffI k, hcoeffI (-k)]
    simp
  have hImIntI : Integrable (fun x => (fI x).re)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [fI] using hImInt
  have hIm := ae_eq_zero_of_mFourierCoeff_eq_zero
    (fun x => (fI x).re) hImIntI hImCoeff
  filter_upwards [hRe, hIm] with x hxre hxim
  apply Complex.ext
  · simpa using hxre
  · have hi : (fI x).re = (f x).im := by
      simp [fI]
    rw [← hi]
    simpa using hxim

/-- An integrable complex source and a continuous complex function with matching
Fourier coefficients are equal almost everywhere. -/
theorem ae_eq_complex_continuous_of_mFourierCoeff_eq {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (g : C(UnitAddTorus (Fin d), ℂ))
    (hg : Integrable (fun x => g x) (volume : Measure (UnitAddTorus (Fin d))))
    (hcoeff : ∀ k : Fin d → ℤ, mFourierCoeff f k = mFourierCoeff g k) :
    f =ᵐ[volume] fun x => g x := by
  have hdiff : Integrable (fun x => f x - g x)
      (volume : Measure (UnitAddTorus (Fin d))) := hf.sub hg
  have hzeroCoeff : ∀ k, mFourierCoeff (fun x => f x - g x) k = 0 := by
    intro k
    have h1 : Integrable (fun x => mFourier (-k) x • f x)
        (volume : Measure (UnitAddTorus (Fin d))) :=
      hf.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          calc
            ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
            _ = 1 := mFourier_norm)
    have h2 : Integrable (fun x => mFourier (-k) x • g x)
        (volume : Measure (UnitAddTorus (Fin d))) :=
      hg.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          calc
            ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
            _ = 1 := mFourier_norm)
    change ∫ x, mFourier (-k) x • (f x - g x) ∂
      (volume : Measure (UnitAddTorus (Fin d))) = 0
    have hp : (fun x => mFourier (-k) x • (f x - g x)) =
        fun x => mFourier (-k) x • f x - mFourier (-k) x • g x := by
      funext x
      simp only [smul_sub]
    rw [integral_congr_ae (Filter.Eventually.of_forall (congrFun hp)), integral_sub h1 h2]
    exact sub_eq_zero.mpr (hcoeff k)
  have hz := ae_eq_zero_of_mFourierCoeff_eq_zero_complex (fun x => f x - g x) hdiff hzeroCoeff
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

/-- If continuous blocks have the expected scalar-multiplier coefficients and
the multipliers telescope to one at every frequency, their summable series has
the same Fourier coefficients as the original integrable source. -/
theorem tsum_fourierCoeff_eq_of_block_telescope {d : ℕ}
    (b : (Fin d → ℕ) → C(UnitAddTorus (Fin d), ℂ))
    (hb : Summable b)
    (sourceCoeff : (Fin d → ℤ) → ℂ)
    (mult : (Fin d → ℕ) → (Fin d → ℤ) → ℝ)
    (hblock : ∀ s k, mFourierCoeff (b s) k = (mult s k : ℂ) * sourceCoeff k)
    (hmult : ∀ k, HasSum (fun s => mult s k) 1) :
    ∀ k, mFourierCoeff (∑' s, b s : C(UnitAddTorus (Fin d), ℂ)) k = sourceCoeff k := by
  intro k
  have h1 := (BrownianSharp.AlignmentPeriodicFourierReconstruction.fourierCoefficientCLM k).hasSum
    hb.hasSum
  have h2 := (Complex.ofRealCLM.hasSum (hmult k)).mul_right (sourceCoeff k)
  simp only [BrownianSharp.AlignmentPeriodicFourierReconstruction.fourierCoefficientCLM_apply,
    hblock] at h1
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h2
  exact h1.unique h2

/-- A summable continuous block expansion with telescoping Fourier multipliers
is an almost-everywhere representative of its integrable complex source. -/
theorem ae_eq_complex_tsum_of_block_telescope {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (b : (Fin d → ℕ) → C(UnitAddTorus (Fin d), ℂ))
    (hb : Summable b)
    (sourceCoeff : (Fin d → ℤ) → ℂ)
    (mult : (Fin d → ℕ) → (Fin d → ℤ) → ℝ)
    (hsource : ∀ k, mFourierCoeff f k = sourceCoeff k)
    (hblock : ∀ s k, mFourierCoeff (b s) k = (mult s k : ℂ) * sourceCoeff k)
    (hmult : ∀ k, HasSum (fun s => mult s k) 1)
    (hint : Integrable (fun x => (∑' s, b s) x)
      (volume : Measure (UnitAddTorus (Fin d)))) :
    f =ᵐ[volume] fun x => (∑' s, b s) x := by
  have hcoeff : ∀ k, mFourierCoeff f k =
      mFourierCoeff ((∑' s, b s : C(UnitAddTorus (Fin d), ℂ)) :
        UnitAddTorus (Fin d) → ℂ) k := by
    intro k
    rw [hsource k]
    exact (tsum_fourierCoeff_eq_of_block_telescope b hb sourceCoeff mult hblock hmult k).symm
  exact ae_eq_complex_continuous_of_mFourierCoeff_eq f hf (∑' s, b s) hint hcoeff

end BrownianSharp.AlignmentPeriodicL1Fourier
