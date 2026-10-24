import BrownianSharp.SmoothCoefficientEvents
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-! Finite expected maxima of centered Gaussian variables without an
independence assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace BrownianSharp.AlignmentExponentialGaussianMaximum

private theorem gaussian_abs_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal (0:ℝ) v) P) : Integrable (fun ω => |X ω|) P := by
  have hm : MemLp (id : ℝ → ℝ) 1 (gaussianReal (0:ℝ) v) :=
    memLp_id_gaussianReal (μ := 0) (v := v) 1
  have hbase : Integrable (fun x : ℝ => |x|) (gaussianReal (0:ℝ) v) := by
    simpa [Real.norm_eq_abs] using (memLp_one_iff_integrable.mp hm).norm
  simpa [Function.comp_def] using hX.integrable_comp hbase

private theorem gaussian_max_abs_aemeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} (G : ι → Ω → ℝ) {v : ι → ℝ≥0}
    (hLaw : ∀ i, HasLaw (G i) (gaussianReal (0:ℝ) (v i)) P) :
    AEMeasurable (fun ω => ‖fun i => G i ω‖) P := by
  have hX : AEMeasurable (fun ω i => G i ω) P :=
    AEMeasurable.of_eval (fun i => (hLaw i).aemeasurable)
  exact continuous_norm.measurable.comp_aemeasurable hX

theorem gaussian_max_abs_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ)
    {v : ι → ℝ≥0} (hLaw : ∀ i, HasLaw (G i) (gaussianReal (0:ℝ) (v i)) P) :
    Integrable (fun ω => ‖fun i => G i ω‖) P := by
  classical
  let f : Ω → ℝ := fun ω => ‖fun i => G i ω‖
  have hmeas : AEMeasurable f P := by
    simpa [f] using gaussian_max_abs_aemeasurable G hLaw
  have hsum : Integrable (fun ω => ∑ i, |G i ω|) P := by
    apply integrable_finsetSum
    intro i hi
    exact gaussian_abs_integrable (hLaw i)
  have hdom : ∀ ω, ‖fun i => G i ω‖ ≤ ∑ i, |G i ω| := by
    intro ω
    have hsup : Finset.univ.sup (fun i => ‖G i ω‖₊) ≤
        ∑ j, ‖G j ω‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hcR : (‖G i ω‖₊ : ℝ) ≤ ∑ j, (‖G j ω‖₊ : ℝ) := by
        simpa [coe_nnnorm, Real.norm_eq_abs] using
          (Finset.single_le_sum (fun j hj => norm_nonneg (G j ω))
            (Finset.mem_univ i))
      have hcR' : (‖G i ω‖₊ : ℝ) ≤
          (↑(∑ j, ‖G j ω‖₊ : ℝ≥0) : ℝ) := by
        simpa only [NNReal.coe_sum] using hcR
      exact_mod_cast hcR' 
    change ((Finset.univ.sup fun i => ‖G i ω‖₊ : ℝ≥0) : ℝ) ≤ _
    calc
      _ ≤ ∑ j, (‖G j ω‖₊ : ℝ) := by exact_mod_cast hsup
      _ = ∑ j, |G j ω| := by simp [Real.norm_eq_abs]
  have hdom' : ∀ᵐ ω ∂P, ‖‖fun i => G i ω‖‖ ≤ ∑ i, |G i ω| := by
    filter_upwards with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdom ω
  exact hsum.mono' hmeas.aestronglyMeasurable hdom'


private theorem exp_pi_norm_le_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (t : ℝ) :
    Real.exp (t * ‖x‖) ≤ ∑ i, (Real.exp (t * x i) + Real.exp (-t * x i)) := by
  classical
  have hmax : ∃ i, ‖x‖ = |x i| := by
    have hs := Finset.exists_mem_eq_sup (Finset.univ : Finset ι)
      Finset.univ_nonempty (fun i => ‖x i‖₊)
    rcases hs with ⟨i, hi, heq⟩
    refine ⟨i, ?_⟩
    change ((↑(Finset.univ.sup fun j => ‖x j‖₊ : ℝ≥0) : ℝ)) = |x i|
    rw [heq, coe_nnnorm, Real.norm_eq_abs]
  rcases hmax with ⟨i, hi⟩
  have hterm : Real.exp (t * ‖x‖) ≤
      Real.exp (t * x i) + Real.exp (-t * x i) := by
    by_cases hx : 0 ≤ x i
    · rw [hi, abs_of_nonneg hx]
      exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))
    · have hx' : x i < 0 := lt_of_not_ge hx
      rw [hi, abs_of_neg hx']
      have heq : t * (-x i) = -t * x i := by ring
      rw [heq]
      exact le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (t * x i) + Real.exp (-t * x i) ≤
      ∑ j, (Real.exp (t * x j) + Real.exp (-t * x j)) := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j => Real.exp (t * x j) + Real.exp (-t * x j))
      (fun j hj => add_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
      (Finset.mem_univ i)
  exact hterm.trans hsum

/-- The expected maximum of finitely many centered Gaussian marginals is
controlled by the sum of their exponential moments. No independence is used. -/
theorem expected_max_le_of_variance_parameter
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ)
    {v : ι → ℝ≥0} (hLaw : ∀ i, HasLaw (G i) (gaussianReal (0:ℝ) (v i)) P)
    {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hvar : ∀ i, ((v i : ℝ)) ≤ σ^2) :
    (∫ ω, ‖fun i => G i ω‖ ∂P) ≤
      Real.log (2 * Fintype.card ι) / t + σ^2 * t / 2 := by
  classical
  let Y : Ω → ℝ := fun ω => ‖fun i => G i ω‖
  have hYint : Integrable Y P := by
    simpa [Y] using gaussian_max_abs_integrable G hLaw
  have hsumInt : Integrable
      (fun ω => ∑ i, (Real.exp (t * G i ω) + Real.exp (-t * G i ω))) P := by
    apply integrable_finsetSum
    intro i hi
    have hp := (hLaw i).integrable_comp
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) t)
    have hm := (hLaw i).integrable_comp
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) (-t))
    change Integrable ((fun ω => Real.exp (t * G i ω)) +
      (fun ω => Real.exp (-t * G i ω))) P
    exact hp.add hm
  have hYae : AEMeasurable Y P := by
    simpa [Y] using gaussian_max_abs_aemeasurable G hLaw
  have hExpInt : Integrable (fun ω => Real.exp (t * Y ω)) P := by
    have hm : AEMeasurable (fun ω => Real.exp (t * Y ω)) P :=
      Real.measurable_exp.comp_aemeasurable
        ((measurable_const_mul t).comp_aemeasurable hYae)
    have hdom : ∀ᵐ ω ∂P,
        ‖Real.exp (t * Y ω)‖ ≤
          ∑ i, (Real.exp (t * G i ω) + Real.exp (-t * G i ω)) := by
      filter_upwards with ω
      have h := exp_pi_norm_le_sum (fun i => G i ω) t
      simpa [Y, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
    exact hsumInt.mono' hm.aestronglyMeasurable hdom
  have hdom : ∀ ω,
      Real.exp (t * Y ω) ≤
        ∑ i, (Real.exp (t * G i ω) + Real.exp (-t * G i ω)) := by
    intro ω
    have h := exp_pi_norm_le_sum (fun i => G i ω) t
    simpa [Y] using h
  have hmoment : ∫ ω, Real.exp (t * Y ω) ∂P ≤
      (Fintype.card ι : ℝ) * 2 * Real.exp (σ^2*t^2/2) := by
    calc
      _ ≤ ∫ ω, ∑ i, (Real.exp (t * G i ω) + Real.exp (-t * G i ω)) ∂P :=
        integral_mono hExpInt hsumInt hdom
      _ = ∑ i, (∫ ω, Real.exp (t * G i ω) ∂P +
          ∫ ω, Real.exp (-t * G i ω) ∂P) := by
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro i hi
          exact integral_add
            ((hLaw i).integrable_comp
              (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) t))
            ((hLaw i).integrable_comp
              (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) (-t)) )
        · intro i hi
          exact ((hLaw i).integrable_comp
              (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) t)).add
              ((hLaw i).integrable_comp
              (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v i) (-t)))
      _ ≤ ∑ i, (Real.exp (σ^2*t^2/2) + Real.exp (σ^2*t^2/2)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hm₁ := ProbabilityTheory.mgf_gaussianReal (hLaw i) t
        have hm₂ := ProbabilityTheory.mgf_gaussianReal (hLaw i) (-t)
        have hm₁' : (∫ ω, Real.exp (t * G i ω) ∂P) =
            Real.exp ((v i : ℝ) * t^2 / 2) := by
          simpa [ProbabilityTheory.mgf, mul_comm, mul_left_comm, mul_assoc] using hm₁
        have hm₂' : (∫ ω, Real.exp (-t * G i ω) ∂P) =
            Real.exp ((v i : ℝ) * t^2 / 2) := by
          simpa [ProbabilityTheory.mgf, mul_comm, mul_left_comm, mul_assoc] using hm₂
        rw [hm₁', hm₂']
        have hv := hvar i
        have ht2 : 0 ≤ t^2 := sq_nonneg t
        have hbound : ((v i : ℝ) * t^2 / 2) ≤ σ^2*t^2/2 := by nlinarith
        exact add_le_add (Real.exp_le_exp.mpr hbound) (Real.exp_le_exp.mpr hbound)
      _ = (Fintype.card ι : ℝ) * 2 * Real.exp (σ^2*t^2/2) := by
        simp [Finset.sum_add_distrib, mul_assoc]
        ring
  have hJensen := convexOn_exp.map_integral_le
      (s := Set.univ) (f := fun ω => t * Y ω) Real.continuousOn_exp isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      (hYint.const_mul t) (by simpa [Function.comp_def] using hExpInt)
  have hJ : Real.exp (t * ∫ ω, Y ω ∂P) ≤ ∫ ω, Real.exp (t * Y ω) ∂P := by
    simpa [average_eq_integral, Function.comp_def, integral_const_mul] using hJensen
  have hcardpos : 0 < (2 * (Fintype.card ι : ℝ)) := by positivity
  have hlog : t * ∫ ω, Y ω ∂P ≤ Real.log (2 * Fintype.card ι) + σ^2*t^2/2 := by
    have hle := hJ.trans hmoment
    have hlogle := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hlogle
    have hsplit : Real.log ((Fintype.card ι : ℝ) * 2 * Real.exp (σ^2*t^2/2)) =
        Real.log (2 * Fintype.card ι) + σ^2*t^2/2 := by
      rw [show (Fintype.card ι : ℝ) * 2 = 2 * Fintype.card ι by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
    rw [hsplit] at hlogle
    exact hlogle
  have hdivide : (t * ∫ ω, Y ω ∂P) / t ≤
      (Real.log (2 * Fintype.card ι) + σ^2*t^2/2) / t :=
    div_le_div_of_nonneg_right hlog (le_of_lt ht)
  have hleft : (t * ∫ ω, Y ω ∂P) / t = ∫ ω, Y ω ∂P := by
    field_simp [ne_of_gt ht]
  have hright : (Real.log (2 * Fintype.card ι) + σ^2*t^2/2) / t =
      Real.log (2 * Fintype.card ι) / t + σ^2*t/2 := by
    field_simp [ne_of_gt ht]
  dsimp [Y] at hleft hdivide ⊢
  rw [hleft, hright] at hdivide
  exact hdivide


/-- The expected supremum of a finite family of centered Gaussian variables
with marginal variances at most `σ²`. The bound makes no independence
assumption. -/
theorem expected_max_le_sqrt_log
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ)
    {v : ι → ℝ≥0} (hLaw : ∀ i, HasLaw (G i) (gaussianReal (0:ℝ) (v i)) P)
    {σ : ℝ} (hσ : 0 ≤ σ) (hvar : ∀ i, ((v i : ℝ)) ≤ σ^2) :
    (∫ ω, ‖fun i => G i ω‖ ∂P) ≤
      2 * σ * Real.sqrt (Real.log (2 * Fintype.card ι + 2)) := by
  classical
  let cardR : ℝ := Fintype.card ι
  let L : ℝ := Real.log (2 * cardR + 2)
  have hcard : 0 < cardR := by
    dsimp [cardR]
    exact_mod_cast Fintype.card_pos
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    linarith
  by_cases hσ0 : σ = 0
  · have hvar0 : ∀ i, v i = 0 := by
      intro i
      have hvR : (v i : ℝ) ≤ 0 := by simpa [hσ0] using hvar i
      have hv0 : (v i : ℝ) = 0 := le_antisymm hvR (by positivity)
      exact_mod_cast hv0
    have hzero : ∀ i, G i =ᵐ[P] (fun _ => 0) := by
      intro i
      have hLaw0 : HasLaw (G i) (Measure.dirac (0:ℝ)) P := by
        simpa [hvar0 i] using hLaw i
      exact hLaw0.ae_eq_of_dirac
    have hzeroall : ∀ᵐ ω ∂P, ∀ i, G i ω = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      exact hzero i
    have hmaxzero : (fun ω => ‖fun i => G i ω‖) =ᵐ[P] 0 := by
      filter_upwards [hzeroall] with ω hω
      simp [hω]
    have hmaxint := gaussian_max_abs_integrable G hLaw
    rw [integral_congr_ae hmaxzero]
    simpa [hσ0]
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
    have hlogcard : Real.log (2*cardR) ≤ L := by
      dsimp [L]
      apply Real.log_le_log
      · positivity
      · linarith
    let t : ℝ := Real.sqrt L / σ
    have ht : 0 < t := div_pos (Real.sqrt_pos.mpr hL) hσpos
    have hfirst := expected_max_le_of_variance_parameter G hLaw hσ ht hvar
    have htval : t = Real.sqrt L / σ := rfl
    have hLroot : Real.sqrt L * Real.sqrt L = L := by
      nlinarith [Real.sq_sqrt hL.le]
    have hterm₁ : Real.log (2*cardR) / t ≤ σ * Real.sqrt L := by
      have hnum : Real.log (2*cardR) ≤ L := hlogcard
      rw [htval]
      have hsquare : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
      field_simp [hsquare, hσ0]
      nlinarith [Real.sqrt_nonneg L]
    have hterm₂ : σ^2 * t / 2 ≤ σ * Real.sqrt L := by
      rw [htval]
      field_simp [ne_of_gt hσpos]
      nlinarith [Real.sqrt_nonneg L]
    have hbound : Real.log (2 * Fintype.card ι) / t + σ^2*t/2 ≤
        2*σ*Real.sqrt L := by
      dsimp [L, cardR]
      nlinarith [hterm₁, hterm₂]
    rw [show Real.log (2 * Fintype.card ι + 2) = L by rfl]
    exact hfirst.trans hbound

end BrownianSharp.AlignmentExponentialGaussianMaximum
