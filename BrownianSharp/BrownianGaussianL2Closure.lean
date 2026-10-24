import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HaarQuarter

theorem integral_abs_le_l2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ ‖hf.toLp f‖ := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) P := by simpa using hf
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) P := by
    exact memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := f) (g := fun _ : Ω => (1 : ℝ))
    (by norm_num [Real.holderConjugate_iff]) hf' h1
  have hnorm : (∫ ω, |f ω| ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) = ‖hf.toLp f‖ := by
    rw [Lp.norm_toLp]
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num [Real.norm_eq_abs]
    · positivity
  have hone : (∫ ω, |(1 : ℝ)| ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) = 1 := by
    simp [integral_const]
  calc
    ∫ ω, |f ω| ∂P ≤ (∫ ω, |f ω| ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
      simpa [Real.norm_eq_abs, hone] using hholder
    _ = ‖hf.toLp f‖ := hnorm

theorem l2_norm_sq_eq_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  have hinner : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ ω, f ω ^ 2 ∂P := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω]
    simp
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) := by simp
    _ = ∫ ω, f ω ^ 2 ∂P := hinner

private theorem norm_exp_diff_le (t x y : ℝ) :
    ‖Complex.exp (t * x * Complex.I) - Complex.exp (t * y * Complex.I)‖ ≤
      |t| * |x - y| := by
  have hphase : t * x - t * y = t * (x - y) := by ring
  have hexp : Complex.exp ((t * x - t * y) * Complex.I) *
      Complex.exp (t * y * Complex.I) = Complex.exp (t * x * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    ‖Complex.exp (t * x * Complex.I) - Complex.exp (t * y * Complex.I)‖ =
        ‖Complex.exp (t * y * Complex.I) *
          (Complex.exp ((t * x - t * y) * Complex.I) - 1)‖ := by
            calc
              _ = ‖Complex.exp ((t * x - t * y) * Complex.I) *
                    Complex.exp (t * y * Complex.I) - Complex.exp (t * y * Complex.I)‖ := by
                    rw [hexp]
              _ = _ := by ring
    _ = ‖Complex.exp ((t * x - t * y) * Complex.I) - 1‖ := by
          rw [norm_mul]
          have : ‖Complex.exp (t * y * Complex.I)‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [this]
          simp
    _ = ‖2 * Real.sin ((t * x - t * y) / 2)‖ := by
          have hcast : ((t * x - t * y : ℝ) : ℂ) =
              (t : ℂ) * (x : ℂ) - (t : ℂ) * (y : ℂ) := by push_cast; ring
          rw [← hcast, show (↑(t * x - t * y : ℝ) : ℂ) * Complex.I =
            Complex.I * (↑(t * x - t * y : ℝ) : ℂ) by ring,
            Complex.norm_exp_I_mul_ofReal_sub_one]
    _ = 2 * |Real.sin ((t * x - t * y) / 2)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    _ ≤ 2 * |(t * x - t * y) / 2| := by
          exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |t| * |x - y| := by
          rw [hphase, abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ)), abs_mul]
          ring

theorem charFun_map_tendsto_of_l2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hX : MemLp X 2 P) (hXn : ∀ n, MemLp (Xn n) 2 P)
    (hconv : Tendsto (fun n => (hXn n).toLp (Xn n)) atTop (𝓝 (hX.toLp X)))
    (t : ℝ) :
    Tendsto (fun n => charFun (P.map (Xn n)) t) atTop
      (𝓝 (charFun (P.map X) t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hconv (ε / (|t| + 1)) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  have hmem : MemLp (fun ω => Xn n ω - X ω) 2 P := (hXn n).sub hX
  have hclass : hmem.toLp (fun ω => Xn n ω - X ω) =
      (hXn n).toLp (Xn n) - hX.toLp X := by
    exact MemLp.toLp_sub (hXn n) hX
  have hI₁ : Integrable (fun ω => Complex.exp (t * Xn n ω * Complex.I)) P := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · have hm : Measurable (fun z : ℝ => Complex.exp (t * z * Complex.I)) := by fun_prop
      exact (hm.comp_aemeasurable (hXn n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with ω
      rw [Complex.norm_exp]
      simp
  have hI₂ : Integrable (fun ω => Complex.exp (t * X ω * Complex.I)) P := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · have hm : Measurable (fun z : ℝ => Complex.exp (t * z * Complex.I)) := by fun_prop
      exact (hm.comp_aemeasurable hX.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with ω
      rw [Complex.norm_exp]
      simp
  have hchar₁ : charFun (P.map (Xn n)) t =
      ∫ ω, Complex.exp (t * Xn n ω * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map (hXn n).aemeasurable (by fun_prop)]
  have hchar₂ : charFun (P.map X) t =
      ∫ ω, Complex.exp (t * X ω * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]
  have hdiffInt := norm_integral_le_integral_norm
      (μ := P)
      (fun ω => Complex.exp (t * Xn n ω * Complex.I) -
        Complex.exp (t * X ω * Complex.I))
  have hdiffEq :
      (∫ ω, Complex.exp (t * Xn n ω * Complex.I) -
        Complex.exp (t * X ω * Complex.I) ∂P) =
      (∫ ω, Complex.exp (t * Xn n ω * Complex.I) ∂P) -
        (∫ ω, Complex.exp (t * X ω * Complex.I) ∂P) := by
    rw [integral_sub hI₁ hI₂]
  have hmono :
      ∫ ω, ‖Complex.exp (t * Xn n ω * Complex.I) -
          Complex.exp (t * X ω * Complex.I)‖ ∂P ≤
        |t| * ∫ ω, |Xn n ω - X ω| ∂P := by
    have hpoint : ∀ᵐ ω ∂P,
        ‖Complex.exp (t * Xn n ω * Complex.I) -
          Complex.exp (t * X ω * Complex.I)‖ ≤ |t| * |Xn n ω - X ω| :=
      Eventually.of_forall fun ω => norm_exp_diff_le t (Xn n ω) (X ω)
    have hrhsInt : Integrable (fun ω => |t| * |Xn n ω - X ω|) P := by
      have : Integrable (fun ω => Xn n ω - X ω) P := hmem.integrable (by norm_num)
      exact this.norm.const_mul _
    calc
      _ ≤ ∫ ω, |t| * |Xn n ω - X ω| ∂P :=
        integral_mono_ae (hI₁.sub hI₂).norm hrhsInt hpoint
      _ = |t| * ∫ ω, |Xn n ω - X ω| ∂P := by rw [integral_const_mul]
  have habs := integral_abs_le_l2 hmem
  have hbound :
      ‖charFun (P.map (Xn n)) t - charFun (P.map X) t‖ ≤
        |t| * dist ((hXn n).toLp (Xn n)) (hX.toLp X) := by
    rw [hchar₁, hchar₂, ← hdiffEq]
    calc
      _ ≤ ∫ ω, ‖Complex.exp (t * Xn n ω * Complex.I) -
            Complex.exp (t * X ω * Complex.I)‖ ∂P := hdiffInt
      _ ≤ |t| * ∫ ω, |Xn n ω - X ω| ∂P := hmono
      _ ≤ |t| * ‖hmem.toLp (fun ω => Xn n ω - X ω)‖ := by
            gcongr
      _ = |t| * dist ((hXn n).toLp (Xn n)) (hX.toLp X) := by rw [hclass, dist_eq_norm]
  have hsmall := hn₀ n hn
  have hscale : |t| * dist ((hXn n).toLp (Xn n)) (hX.toLp X) < ε := by
    calc
      |t| * dist _ _ ≤ (|t| + 1) * dist _ _ := by
        exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) dist_nonneg
      _ < (|t| + 1) * (ε / (|t| + 1)) := by
        exact mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = ε := by field_simp
  simpa [dist_eq_norm] using lt_of_le_of_lt hbound hscale

/-- Gaussianity is closed under convergence in `L²`, provided the Gaussian means and variances
converge.  The proof is by convergence of characteristic functions: the exponentials are
Lipschitz in the underlying scalar, and on a probability space `L²` convergence implies the
needed `L¹` convergence. -/
theorem hasGaussianLaw_of_l2_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hX : MemLp X 2 P) (hXn : ∀ n, MemLp (Xn n) 2 P)
    (hconv : Tendsto (fun n => (hXn n).toLp (Xn n)) atTop (𝓝 (hX.toLp X)))
    (variance : ℕ → NNReal) (v : NNReal)
    (hmap : ∀ n, P.map (Xn n) = gaussianReal 0 (variance n))
    (hvariance_tendsto : Tendsto (fun n => (variance n : ℝ)) atTop (𝓝 (v : ℝ))) :
    HasGaussianLaw X P := by
  have hchar : ∀ t, charFun (P.map X) t = charFun (gaussianReal 0 v) t := by
    intro t
    have hlim₁ := charFun_map_tendsto_of_l2 hX hXn hconv t
    let φ : ℝ → ℂ := fun r => Complex.exp (-(r : ℂ) * (t : ℂ) ^ 2 / 2)
    have hlim₂ : Tendsto (fun n => charFun (P.map (Xn n)) t) atTop
        (𝓝 (charFun (gaussianReal 0 v) t)) := by
      have hφ : Continuous φ := by fun_prop
      have hφlim : Tendsto (fun n => φ (variance n : ℝ)) atTop (𝓝 (φ (v : ℝ))) :=
        hφ.continuousAt.tendsto.comp hvariance_tendsto
      convert hφlim using 1
      · funext n
        rw [hmap n, charFun_gaussianReal]
        simp [φ]
        ring
      · rw [charFun_gaussianReal]
        simp [φ]
        ring
    exact tendsto_nhds_unique hlim₁ hlim₂
  have hmapX : P.map X = gaussianReal 0 v :=
    Measure.ext_of_charFun (funext hchar)
  exact ⟨hX.aestronglyMeasurable.aemeasurable, by rw [hmapX]; infer_instance⟩

/-- A centered sequence of Gaussian variables that converges in `L²` has a Gaussian limit.
The limiting variance is the squared `L²` norm of the limit, so no separate variance
convergence premise is needed. -/
theorem hasGaussianLaw_of_centered_l2_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hX : MemLp X 2 P) (hXn : ∀ n, MemLp (Xn n) 2 P)
    (hconv : Tendsto (fun n => (hXn n).toLp (Xn n)) atTop (𝓝 (hX.toLp X)))
    (hGaussian : ∀ n, HasGaussianLaw (Xn n) P)
    (hcenter : ∀ n, ∫ ω, Xn n ω ∂P = 0) :
    HasGaussianLaw X P := by
  let variance : ℕ → NNReal := fun n => (ProbabilityTheory.variance (Xn n) P).toNNReal
  let limitVariance : NNReal := ⟨‖hX.toLp X‖ ^ 2, sq_nonneg _⟩
  have hvarEq (n : ℕ) : ProbabilityTheory.variance (Xn n) P =
      ‖(hXn n).toLp (Xn n)‖ ^ 2 := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero
      (hXn n).aemeasurable (hcenter n), l2_norm_sq_eq_integral_sq]
  have hnormConv : Tendsto (fun n => ‖(hXn n).toLp (Xn n)‖) atTop
      (𝓝 ‖hX.toLp X‖) :=
    continuous_norm.continuousAt.tendsto.comp hconv
  have hsqConv : Tendsto (fun n => ‖(hXn n).toLp (Xn n)‖ ^ 2) atTop
      (𝓝 (‖hX.toLp X‖ ^ 2)) :=
    (continuous_pow 2).continuousAt.tendsto.comp hnormConv
  have hvariance : Tendsto (fun n => (variance n : ℝ)) atTop
      (𝓝 (limitVariance : ℝ)) := by
    convert hsqConv using 1
    · funext n
      simp only [variance]
      rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _), hvarEq]
    · congr 1
  have hmap : ∀ n, P.map (Xn n) = gaussianReal 0 (variance n) := by
    intro n
    rw [(hGaussian n).map_eq_gaussianReal, hcenter n]
  exact hasGaussianLaw_of_l2_tendsto hX hXn hconv variance limitVariance hmap hvariance

/-- A vector-valued random variable is Gaussian when every continuous linear projection is an
`L²` limit of centered Gaussian random variables. The approximating sequence may depend on the
projection. The proof uses the scalar closure theorem and the StrongDual characterization of
Gaussian measures. -/
theorem hasGaussianLaw_of_dual_centered_l2_limits
    {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    {X : Ω → E} (hX : AEMeasurable X P)
    (hdual : ∀ L : StrongDual ℝ E, ∃ Xn : ℕ → Ω → ℝ,
      ∃ hXn : ∀ n, MemLp (Xn n) 2 P,
      ∃ hL : MemLp (fun ω => L (X ω)) 2 P,
        Tendsto (fun n => (hXn n).toLp (Xn n)) atTop
          (𝓝 (hL.toLp (fun ω => L (X ω)))) ∧
        (∀ n, HasGaussianLaw (Xn n) P) ∧
        (∀ n, ∫ ω, Xn n ω ∂P = 0)) :
    HasGaussianLaw X P := by
  classical
  have hgaussian : IsGaussian (P.map X) := by
    apply isGaussian_of_isGaussian_map
    intro L
    obtain ⟨Xn, hXn, hL, hconv, hXnGaussian, hcenter⟩ := hdual L
    have hscalar : HasGaussianLaw (fun ω => L (X ω)) P :=
      hasGaussianLaw_of_centered_l2_tendsto hL hXn hconv hXnGaussian hcenter
    have hmap : P.map (fun ω => L (X ω)) = (P.map X).map L := by
      let X' : Ω → E := AEMeasurable.mk X hX
      have hX'meas : Measurable X' := hX.measurable_mk
      have hXlaw : P.map X = P.map X' := Measure.map_congr hX.ae_eq_mk
      have hprojectedLaw : P.map (fun ω => L (X ω)) =
          P.map (fun ω => L (X' ω)) :=
        Measure.map_congr (hX.ae_eq_mk.fun_comp (fun e => L e))
      calc
        P.map (fun ω => L (X ω)) = P.map (fun ω => L (X' ω)) := hprojectedLaw
        _ = (P.map X').map L := (Measure.map_map L.measurable hX'meas).symm
        _ = (P.map X).map L := by rw [← hXlaw]
    rw [← hmap]
    exact hscalar.isGaussian_map
  exact ⟨hX, hgaussian⟩

/-- Gaussianity extends from a centered Gaussian submodule of `L²` to its norm closure. In
applications, the submodule can be the algebraic span of jointly Gaussian centered coordinates;
the preceding dual-projection theorem supplies Gaussianity of each finite linear combination. -/
theorem hasGaussianLaw_of_mem_topologicalClosure_gaussianSubmodule
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (S : Submodule ℝ (Lp ℝ 2 P))
    (hGaussian : ∀ y : Lp ℝ 2 P, y ∈ S → HasGaussianLaw (fun ω => y ω) P)
    (hcenter : ∀ y : Lp ℝ 2 P, y ∈ S → ∫ ω, y ω ∂P = 0)
    (x : Lp ℝ 2 P) (hx : x ∈ S.topologicalClosure) :
    HasGaussianLaw (fun ω => x ω) P := by
  change x ∈ closure (S : Set (Lp ℝ 2 P)) at hx
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  let hX : MemLp (fun ω => x ω) 2 P := Lp.memLp x
  let hXn : ∀ n, MemLp (fun ω => u n ω) 2 P := fun n => Lp.memLp (u n)
  have hseq : (fun n => (hXn n).toLp (fun ω => u n ω)) = u := by
    funext n
    exact Lp.toLp_coeFn (u n) (hXn n)
  have hlimit : hX.toLp (fun ω => x ω) = x := Lp.toLp_coeFn x hX
  have hconv : Tendsto (fun n => (hXn n).toLp (fun ω => u n ω)) atTop
      (𝓝 (hX.toLp (fun ω => x ω))) := by
    rw [hseq, hlimit]
    exact hlim
  exact hasGaussianLaw_of_centered_l2_tendsto hX hXn hconv
    (fun n => hGaussian (u n) (hu n)) (fun n => hcenter (u n) (hu n))

end HaarQuarter
