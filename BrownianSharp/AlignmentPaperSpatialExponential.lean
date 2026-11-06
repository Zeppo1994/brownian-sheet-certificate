import BrownianSharp.AlignmentExponential
import BrownianSharp.GaussianGridStatistics
import Mathlib.MeasureTheory.Integral.Prod

/-! Concrete spatial integration layer for the normalized hyperbolic-cosine
observable in Lemma 2.4. The pointwise Gaussian expectation and covariance are
proved from the product standard Gaussian law; later declarations can integrate
these identities over a spatial probability measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open BrownianSharp

namespace BrownianSharp.AlignmentPaperSpatialExponential

/-- A scalar Gaussian has every exponential absolute moment. Split at zero and
dominate `exp(b|x|)` by the sum of the two ordinary Gaussian exponentials. -/
theorem gaussianReal_exp_abs_integrable {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun x : ℝ => Real.exp (b * |x|)) (gaussianReal 0 1) := by
  have hplus : Integrable (fun x : ℝ => Real.exp (b * x)) (gaussianReal 0 1) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) b
  have hminus : Integrable (fun x : ℝ => Real.exp (-b * x)) (gaussianReal 0 1) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-b)
  have hsum : Integrable (fun x : ℝ => Real.exp (b * x) + Real.exp (-b * x))
      (gaussianReal 0 1) := hplus.add hminus
  apply Integrable.mono' hsum (by fun_prop)
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hx : 0 ≤ x
  · have habs : |x| = x := abs_of_nonneg hx
    rw [habs]
    have hp : 0 < Real.exp (-b * x) := Real.exp_pos _
    nlinarith [Real.exp_pos (b * x)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have habs : |x| = -x := abs_of_nonpos hx'
    rw [habs]
    have hp : 0 < Real.exp (b * x) := Real.exp_pos _
    have hp' : 0 < Real.exp (-b * x) := Real.exp_pos _
    have heq : b * -x = -b * x := by ring
    rw [heq]
    nlinarith

/-- The absolute-coordinate exponential envelope is integrable under every
finite product standard Gaussian, by finite-product factorization. -/
theorem productGaussian_exp_abs_sum_integrable
    {κ : Type*} [Fintype κ] (b : ℝ) (hb : 0 ≤ b) :
    Integrable (fun z : κ → ℝ => Real.exp (b * ∑ i, |z i|))
      (productStandardGaussian κ) := by
  have hprod : Integrable (fun z : κ → ℝ => ∏ i, Real.exp (b * |z i|))
      (productStandardGaussian κ) := by
    rw [show productStandardGaussian κ = Measure.pi (fun _ : κ => gaussianReal 0 1) by rfl]
    exact Integrable.fintype_prod (fun i => gaussianReal_exp_abs_integrable hb)
  apply hprod.congr
  filter_upwards with z
  have harg : b * ∑ i, |z i| = ∑ i, b * |z i| := Finset.mul_sum _ _ _
  rw [harg, ← Real.exp_sum]

/-- Normalized cosh feature at a spatial point, before spatial integration. -/
def spatialCoshFeature {κ : Type*} [Fintype κ] (τ : ℝ) (a : κ → ℝ)
    (z : κ → ℝ) : ℝ :=
  Real.exp (-τ / 2) * Real.cosh (Real.sqrt τ * ∑ i, a i * z i)

/-- The spatially averaged normalized cosh feature. -/
def spatialCoshAverage {α κ : Type*} [MeasurableSpace α] [Fintype κ] (μ : Measure α)
    (τ : ℝ) (a : α → κ → ℝ) (z : κ → ℝ) : ℝ :=
  Real.exp (-τ / 2) * ∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i * z i) ∂μ

/-- Pointwise absolute-coordinate bound for a unit-row feature. -/
theorem spatialCoshFeature_norm_le_envelope
    {κ : Type*} [Fintype κ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : κ → ℝ) (ha : ∑ i, a i ^ 2 = 1) (z : κ → ℝ) :
    ‖spatialCoshFeature τ a z‖ ≤
      Real.exp (-τ / 2) * Real.exp (Real.sqrt τ * ∑ i, |z i|) := by
  have hcoef (i : κ) : |a i| ≤ 1 := by
    have hterm : a i ^ 2 ≤ 1 := by
      calc
        a i ^ 2 ≤ ∑ j, a j ^ 2 := Finset.single_le_sum
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 1 := ha
    nlinarith [sq_abs (a i)]
  have hsum : |∑ i, a i * z i| ≤ ∑ i, |z i| := by
    calc
      |∑ i, a i * z i| ≤ ∑ i, |a i * z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |z i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hcoef i)
  have hsqrt : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have harg : |Real.sqrt τ * ∑ i, a i * z i| ≤
      Real.sqrt τ * ∑ i, |z i| := by
    rw [abs_mul, abs_of_nonneg hsqrt]
    exact mul_le_mul_of_nonneg_left hsum hsqrt
  have hcoshAbs (v : ℝ) : Real.cosh v ≤ Real.exp |v| := by
    rw [Real.cosh_eq]
    have hp : Real.exp v ≤ Real.exp |v| := Real.exp_le_exp.mpr (le_abs_self v)
    have hn : Real.exp (-v) ≤ Real.exp |v| := by
      apply Real.exp_le_exp.mpr
      simpa using le_abs_self (-v)
    nlinarith
  have hcosh := hcoshAbs (Real.sqrt τ * ∑ i, a i * z i)
  have hexp := Real.exp_le_exp.mpr harg
  have hpref : 0 < Real.exp (-τ / 2) := Real.exp_pos _
  have hnonneg : 0 ≤ Real.cosh (Real.sqrt τ * ∑ i, a i * z i) := by
    rw [Real.cosh_eq]
    positivity
  change |Real.exp (-τ / 2) * Real.cosh
    (Real.sqrt τ * ∑ i, a i * z i)| ≤ _
  rw [abs_of_nonneg (mul_nonneg hpref.le hnonneg)]
  exact mul_le_mul_of_nonneg_left (hcosh.trans hexp) hpref.le

/-- Joint integrability follows from the uniform coefficient bound `|a_i|≤1`:
the feature is dominated by its Gaussian exponential envelope. The envelope's
integrability is kept as the analytic input here so it can be proved once from
coordinate Gaussian exponential moments. -/
theorem spatialCoshFeature_joint_integrable_of_expEnvelope
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 ≤ τ) (a : α → κ → ℝ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i))
    (hEnvelope : Integrable (fun z : κ → ℝ =>
      Real.exp (Real.sqrt τ * ∑ i, |z i|)) (productStandardGaussian κ)) :
    Integrable (fun p : α × (κ → ℝ) =>
      spatialCoshFeature τ (a p.1) p.2)
      (μ.prod (productStandardGaussian κ)) := by
  let P := productStandardGaussian κ
  let F : α × (κ → ℝ) → ℝ := fun p => spatialCoshFeature τ (a p.1) p.2
  let H : α × (κ → ℝ) → ℝ := fun p => Real.exp (-τ / 2) *
    Real.exp (Real.sqrt τ * ∑ i, |p.2 i|)
  have hH : Integrable H (μ.prod P) := by
    have h := hEnvelope.comp_snd μ
    simpa [H, P] using h.const_mul (Real.exp (-τ / 2))
  have hFmeas : Measurable F := by
    dsimp [F, spatialCoshFeature]
    fun_prop (disch := exact haMeas _)
  have hcoef (x : α) (i : κ) : |a x i| ≤ 1 := by
    have hterm : a x i ^ 2 ≤ 1 := by
      calc
        a x i ^ 2 ≤ ∑ j, a x j ^ 2 := Finset.single_le_sum
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 1 := ha x
    nlinarith [sq_abs (a x i)]
  have hcoshAbs (v : ℝ) : Real.cosh v ≤ Real.exp |v| := by
    rw [Real.cosh_eq]
    have hp : Real.exp v ≤ Real.exp |v| := Real.exp_le_exp.mpr (le_abs_self v)
    have hn : Real.exp (-v) ≤ Real.exp |v| := by
      apply Real.exp_le_exp.mpr
      simpa using le_abs_self (-v)
    nlinarith
  have hbound (p : α × (κ → ℝ)) : ‖F p‖ ≤ H p := by
    change ‖Real.exp (-τ / 2) * Real.cosh
      (Real.sqrt τ * ∑ i, a p.1 i * p.2 i)‖ ≤ _
    have hsum : |∑ i, a p.1 i * p.2 i| ≤ ∑ i, |p.2 i| := by
      calc
        |∑ i, a p.1 i * p.2 i| ≤ ∑ i, |a p.1 i * p.2 i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |p.2 i| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hcoef p.1 i)
    have hsqrt : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
    have harg : |Real.sqrt τ * ∑ i, a p.1 i * p.2 i| ≤
        Real.sqrt τ * ∑ i, |p.2 i| := by
      rw [abs_mul, abs_of_nonneg hsqrt]
      exact mul_le_mul_of_nonneg_left hsum hsqrt
    have hcosh := hcoshAbs (Real.sqrt τ * ∑ i, a p.1 i * p.2 i)
    have hexp := Real.exp_le_exp.mpr harg
    have hpref : 0 < Real.exp (-τ / 2) := Real.exp_pos _
    have hnonneg : 0 ≤ Real.cosh
        (Real.sqrt τ * ∑ i, a p.1 i * p.2 i) := by
      rw [Real.cosh_eq]
      positivity
    rw [Real.norm_of_nonneg (mul_nonneg hpref.le hnonneg)]
    dsimp [F, H, spatialCoshFeature]
    exact mul_le_mul_of_nonneg_left (hcosh.trans hexp) hpref.le
  apply Integrable.mono' hH hFmeas.aestronglyMeasurable
  filter_upwards with p
  exact hbound p

/-- The joint-integrability envelope is itself integrable for every finite
product standard Gaussian, so no moment premise remains in the feature layer. -/
theorem spatialCoshFeature_joint_integrable
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 ≤ τ) (a : α → κ → ℝ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    Integrable (fun p : α × (κ → ℝ) =>
      spatialCoshFeature τ (a p.1) p.2)
      (μ.prod (productStandardGaussian κ)) := by
  exact spatialCoshFeature_joint_integrable_of_expEnvelope μ τ hτ a ha haMeas
    (productGaussian_exp_abs_sum_integrable (Real.sqrt τ) (Real.sqrt_nonneg τ))

/-- The two-spatial-point product is jointly integrable by the squared
absolute-coordinate envelope. -/
theorem spatialCoshFeature_pair_joint_integrable
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 ≤ τ) (a : α → κ → ℝ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    Integrable (fun p : (α × α) × (κ → ℝ) =>
      spatialCoshFeature τ (a p.1.1) p.2 * spatialCoshFeature τ (a p.1.2) p.2)
      ((μ.prod μ).prod (productStandardGaussian κ)) := by
  let P := productStandardGaussian κ
  let F : (α × α) × (κ → ℝ) → ℝ := fun p =>
    spatialCoshFeature τ (a p.1.1) p.2 * spatialCoshFeature τ (a p.1.2) p.2
  let H : (α × α) × (κ → ℝ) → ℝ := fun p => Real.exp (-τ) *
    Real.exp (2 * Real.sqrt τ * ∑ i, |p.2 i|)
  have hH : Integrable H ((μ.prod μ).prod P) := by
    have h := (productGaussian_exp_abs_sum_integrable (κ := κ) (2 * Real.sqrt τ)
      (by positivity)).comp_snd (μ.prod μ)
    simpa [H, P] using h.const_mul (Real.exp (-τ))
  have hFmeas : Measurable F := by
    dsimp [F, spatialCoshFeature]
    fun_prop (disch := exact haMeas _)
  have hbound (p : (α × α) × (κ → ℝ)) : ‖F p‖ ≤ H p := by
    have h₁ := spatialCoshFeature_norm_le_envelope τ hτ (a p.1.1) (ha p.1.1) p.2
    have h₂ := spatialCoshFeature_norm_le_envelope τ hτ (a p.1.2) (ha p.1.2) p.2
    have hnonneg₁ : 0 ≤ Real.exp (-τ / 2) * Real.exp
        (Real.sqrt τ * ∑ i, |p.2 i|) := by positivity
    have hprod := mul_le_mul h₁ h₂
      (norm_nonneg (spatialCoshFeature τ (a p.1.2) p.2)) hnonneg₁
    have hcancel : (Real.exp (-τ / 2) * Real.exp
        (Real.sqrt τ * ∑ i, |p.2 i|)) ^ 2 =
        Real.exp (-τ) * Real.exp (2 * Real.sqrt τ * ∑ i, |p.2 i|) := by
      rw [mul_pow, pow_two, pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring
    calc
      ‖F p‖ = ‖spatialCoshFeature τ (a p.1.1) p.2‖ *
          ‖spatialCoshFeature τ (a p.1.2) p.2‖ := by simp [F]
      _ ≤ (Real.exp (-τ / 2) * Real.exp
          (Real.sqrt τ * ∑ i, |p.2 i|)) ^ 2 := by nlinarith
      _ = H p := by simpa [H] using hcancel
  apply Integrable.mono' hH hFmeas.aestronglyMeasurable
  filter_upwards with p
  exact hbound p

/-- For a unit coefficient vector, the normalized cosh feature has exact
standard Gaussian mean one. -/
theorem productGaussian_spatialCoshFeature_mean
    {κ : Type*} [Fintype κ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : κ → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    ∫ z : κ → ℝ, spatialCoshFeature τ a z ∂(productStandardGaussian κ) = 1 := by
  let G : κ → (κ → ℝ) → ℝ := fun i z => z i
  have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hLaw : ∀ i, (productStandardGaussian κ).map (G i) = gaussianReal 0 1 := by
    intro i
    exact productStandardGaussian_coordinate_law i
  have hIndep : iIndepFun G (productStandardGaussian κ) :=
    productStandardGaussian_coordinates_independent κ
  have hrow : HasLaw (GaussianRows.row G a) (gaussianReal 0 1)
      (productStandardGaussian κ) := by
    refine ⟨(GaussianRows.row_gaussian G hG hLaw hIndep a).aemeasurable, ?_⟩
    rw [GaussianRows.row_law G hG hLaw hIndep a, ha]
    norm_num
  have hcosh := AlignmentExponential.integral_cosh_of_hasLaw
    (productStandardGaussian κ) hrow (Real.sqrt τ)
  calc
    ∫ z : κ → ℝ, spatialCoshFeature τ a z ∂productStandardGaussian κ =
        ∫ z, Real.exp (-τ / 2) *
          Real.cosh (Real.sqrt τ * GaussianRows.row G a z) ∂productStandardGaussian κ := by
            apply integral_congr_ae
            filter_upwards with z
            simp [spatialCoshFeature, GaussianRows.row, G]
    _ = Real.exp (-τ / 2) * ∫ z, Real.cosh
          (Real.sqrt τ * GaussianRows.row G a z) ∂productStandardGaussian κ :=
        integral_const_mul _ _
    _ = 1 := by
      rw [hcosh, Real.sq_sqrt hτ]
      norm_num
      rw [← Real.exp_add]
      rw [show -τ / 2 + τ / 2 = 0 by ring, Real.exp_zero]

/-- Exact spatial-point covariance kernel for two unit rows. The normalized
product expectation is `cosh(τ〈a,b〉)`, so subtracting the two unit means gives
`cosh(τρ) - 1`. -/
theorem productGaussian_spatialCoshFeature_pair_covariance
    {κ : Type*} [Fintype κ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a b : κ → ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (rho : ℝ) (hab : ∑ i, a i * b i = rho) (hrho : |rho| ≤ 1) :
    (∫ z : κ → ℝ, spatialCoshFeature τ a z * spatialCoshFeature τ b z ∂
        productStandardGaussian κ) - 1 = Real.cosh (τ * rho) - 1 := by
  let G : κ → (κ → ℝ) → ℝ := fun i z => z i
  have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hLaw : ∀ i, (productStandardGaussian κ).map (G i) = gaussianReal 0 1 := by
    intro i
    exact productStandardGaussian_coordinate_law i
  have hIndep : iIndepFun G (productStandardGaussian κ) :=
    productStandardGaussian_coordinates_independent κ
  have hcov := AlignmentExponential.gaussianRows_normalizedCoshCovariance G hG hLaw hIndep
    a b ha hb rho hab hrho (Real.sqrt τ)
  have hsquare : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ
  have hfun : (fun z : κ → ℝ => spatialCoshFeature τ a z *
      spatialCoshFeature τ b z) = fun z => Real.exp (-τ) *
        (Real.cosh (Real.sqrt τ * GaussianRows.row G a z) *
          Real.cosh (Real.sqrt τ * GaussianRows.row G b z)) := by
    funext z
    calc
      spatialCoshFeature τ a z * spatialCoshFeature τ b z =
          (Real.exp (-τ / 2) * Real.exp (-τ / 2)) *
            (Real.cosh (Real.sqrt τ * GaussianRows.row G a z) *
              Real.cosh (Real.sqrt τ * GaussianRows.row G b z)) := by
            simp [spatialCoshFeature, GaussianRows.row, G]
            ring
      _ = Real.exp (-τ) *
          (Real.cosh (Real.sqrt τ * GaussianRows.row G a z) *
            Real.cosh (Real.sqrt τ * GaussianRows.row G b z)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  rw [hfun]
  simpa [hsquare, mul_assoc] using hcov

/-- The spatially averaged observable has exact mean one whenever the product
integrand is integrable. This is the first Fubini step in the manuscript's
spatial-average argument. -/
theorem productGaussian_spatialCoshAverage_mean
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (hJoint : Integrable (fun p : α × (κ → ℝ) =>
      spatialCoshFeature τ (a p.1) p.2)
      (μ.prod (productStandardGaussian κ))) :
    ∫ z : κ → ℝ, spatialCoshAverage μ τ a z ∂productStandardGaussian κ = 1 := by
  let P := productStandardGaussian κ
  let g : α → (κ → ℝ) → ℝ := fun x z => spatialCoshFeature τ (a x) z
  have hSwap : Integrable (fun p : (κ → ℝ) × α => g p.2 p.1) (P.prod μ) := by
    change Integrable (fun p : (κ → ℝ) × α =>
      spatialCoshFeature τ (a p.2) p.1) (P.prod μ)
    exact hJoint.swap
  have hAvg : ∀ z, spatialCoshAverage μ τ a z = ∫ x, g x z ∂μ := by
    intro z
    rw [spatialCoshAverage]
    calc
      Real.exp (-τ / 2) * ∫ x, Real.cosh
          (Real.sqrt τ * ∑ i, a x i * z i) ∂μ =
        ∫ x, Real.exp (-τ / 2) * Real.cosh
          (Real.sqrt τ * ∑ i, a x i * z i) ∂μ := (integral_const_mul _ _).symm
      _ = ∫ x, g x z ∂μ := by
        congr 1
  calc
    ∫ z, spatialCoshAverage μ τ a z ∂P = ∫ z, ∫ x, g x z ∂μ ∂P := by
      apply integral_congr_ae
      filter_upwards with z
      exact hAvg z
    _ = ∫ p : α × (κ → ℝ), g p.1 p.2 ∂(μ.prod P) := by
      rw [MeasureTheory.integral_integral_symm hSwap]
    _ = ∫ x, ∫ z, g x z ∂P ∂μ := MeasureTheory.integral_prod _ hJoint
    _ = ∫ x, 1 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact productGaussian_spatialCoshFeature_mean τ hτ (a x) (ha x)
    _ = 1 := by simp

/-- Unconditional spatial-average mean-one identity for a probability spatial
measure and measurable unit coefficient rows. Integrability is discharged by
the finite-product absolute-exponential envelope above. -/
theorem productGaussian_spatialCoshAverage_mean_actual
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    ∫ z : κ → ℝ, spatialCoshAverage μ τ a z ∂productStandardGaussian κ = 1 := by
  apply productGaussian_spatialCoshAverage_mean μ a τ hτ ha
  exact spatialCoshFeature_joint_integrable μ τ hτ a ha haMeas

/-- Exact second moment of the spatial average. The proof uses the actual
two-point Gaussian covariance and Fubini, rather than a finite empirical
surrogate. -/
theorem productGaussian_spatialCoshAverage_second_moment
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    Integrable (fun z : κ → ℝ => (spatialCoshAverage μ τ a z) ^ 2)
      (productStandardGaussian κ) ∧
    (∫ z : κ → ℝ, (spatialCoshAverage μ τ a z) ^ 2
      ∂productStandardGaussian κ) =
      ∫ x, ∫ y, Real.cosh (τ * ∑ i, a x i * a y i) ∂μ ∂μ := by
  let P := productStandardGaussian κ
  let g : α → (κ → ℝ) → ℝ := fun x z => spatialCoshFeature τ (a x) z
  let F : (α × α) × (κ → ℝ) → ℝ := fun p =>
    g p.1.1 p.2 * g p.1.2 p.2
  have hJoint := spatialCoshFeature_joint_integrable μ τ hτ a ha haMeas
  have hPair := spatialCoshFeature_pair_joint_integrable μ τ hτ a ha haMeas
  have hPairSwap : Integrable (Function.uncurry
      (fun z : κ → ℝ => fun p : α × α => F (p, z))) (P.prod (μ.prod μ)) := by
    exact hPair.swap
  have hPairMeanInt : Integrable
      (fun z : κ → ℝ => ∫ p : α × α, F (p, z) ∂(μ.prod μ)) P :=
    hPairSwap.integral_prod_left
  have hU2Int : Integrable
      (fun z : κ → ℝ => (spatialCoshAverage μ τ a z) ^ 2) P := by
    apply hPairMeanInt.congr
    filter_upwards with z
    have hAvg : spatialCoshAverage μ τ a z = ∫ x, g x z ∂μ := by
      rw [spatialCoshAverage]
      simp [g, spatialCoshFeature, integral_const_mul]
    rw [hAvg]
    change (∫ p : α × α, g p.1 z * g p.2 z ∂(μ.prod μ)) = _
    rw [MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
      (f := fun x => g x z) (g := fun y => g y z)]
    ring
  have hExchange :
      (∫ z : κ → ℝ, ∫ p : α × α, F (p, z) ∂(μ.prod μ) ∂P) =
        ∫ p : α × α, ∫ z : κ → ℝ, F (p, z) ∂P ∂(μ.prod μ) := by
    exact (MeasureTheory.integral_integral_swap hPair).symm
  constructor
  · exact hU2Int
  · calc
      ∫ z : κ → ℝ, (spatialCoshAverage μ τ a z) ^ 2 ∂P =
          ∫ z, ∫ p : α × α, F (p, z) ∂(μ.prod μ) ∂P := by
            apply integral_congr_ae
            filter_upwards with z
            have hAvg : spatialCoshAverage μ τ a z = ∫ x, g x z ∂μ := by
              rw [spatialCoshAverage]
              simp [g, spatialCoshFeature, integral_const_mul]
            rw [hAvg]
            symm
            change (∫ p : α × α, g p.1 z * g p.2 z ∂(μ.prod μ)) = _
            rw [MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
              (f := fun x => g x z) (g := fun y => g y z)]
            ring
      _ = ∫ p : α × α, ∫ z : κ → ℝ, F (p, z) ∂P ∂(μ.prod μ) := hExchange
      _ = ∫ x, ∫ y, ∫ z : κ → ℝ,
          spatialCoshFeature τ (a x) z * spatialCoshFeature τ (a y) z ∂P ∂μ ∂μ := by
            have hOuter : Integrable
                (fun p : α × α => ∫ z : κ → ℝ, F (p, z) ∂P) (μ.prod μ) :=
              hPair.integral_prod_left
            rw [MeasureTheory.integral_prod _ hOuter]
      _ = ∫ x, ∫ y, Real.cosh (τ * ∑ i, a x i * a y i) ∂μ ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            apply integral_congr_ae
            filter_upwards with y
            have hrho : |∑ i, a x i * a y i| ≤ 1 := by
              have hxy := Finset.abs_sum_le_sum_abs
                (fun i => a x i * a y i) Finset.univ
              have hterm (i : κ) : |a x i * a y i| ≤
                  (a x i ^ 2 + a y i ^ 2) / 2 := by
                rw [abs_mul]
                nlinarith [sq_nonneg (|a x i| - |a y i|), sq_abs (a x i), sq_abs (a y i)]
              calc
                |∑ i, a x i * a y i| ≤ ∑ i, |a x i * a y i| := hxy
                _ ≤ ∑ i, (a x i ^ 2 + a y i ^ 2) / 2 := Finset.sum_le_sum (fun i _ => hterm i)
                _ = 1 := by
                  rw [← Finset.sum_div, Finset.sum_add_distrib, ha x, ha y]
                  norm_num
            have hcov := productGaussian_spatialCoshFeature_pair_covariance
              τ hτ (a x) (a y) (ha x) (ha y) (∑ i, a x i * a y i) rfl hrho
            linarith

/-- Exact variance identity for the spatial-average observable. In particular,
the variance is computed from its actual Gaussian law and spatial covariance
kernel. -/
theorem productGaussian_spatialCoshAverage_variance
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    ProbabilityTheory.variance (spatialCoshAverage μ τ a)
      (productStandardGaussian κ) =
      (∫ x, ∫ y, Real.cosh (τ * ∑ i, a x i * a y i) ∂μ ∂μ) - 1 := by
  let P := productStandardGaussian κ
  let U : (κ → ℝ) → ℝ := spatialCoshAverage μ τ a
  have hJoint := spatialCoshFeature_joint_integrable μ τ hτ a ha haMeas
  have hUInt : Integrable U P := by
    have h := hJoint.swap.integral_prod_left
    apply h.congr
    filter_upwards with z
    change (∫ x, spatialCoshFeature τ (a x) z ∂μ) = spatialCoshAverage μ τ a z
    rw [spatialCoshAverage]
    simp [spatialCoshFeature, integral_const_mul]
  have hU2 := productGaussian_spatialCoshAverage_second_moment
    μ a τ hτ ha haMeas
  have hmean : ∫ z, U z ∂P = 1 := by
    exact productGaussian_spatialCoshAverage_mean_actual μ a τ hτ ha haMeas
  have hvariance := ProbabilityTheory.variance_eq_integral hUInt.aemeasurable
  rw [hvariance, hmean]
  have hcenter : (fun z : κ → ℝ => (U z - 1) ^ 2) =
      fun z => U z ^ 2 - 2 * U z + 1 := by
    funext z
    ring
  rw [hcenter]
  have hsub : Integrable (fun z : κ → ℝ => U z ^ 2 - 2 * U z) P :=
    hU2.1.sub (hUInt.const_mul 2)
  rw [integral_add hsub (integrable_const (1 : ℝ))]
  rw [integral_sub hU2.1 (hUInt.const_mul 2), integral_const_mul, hmean]
  simp only [integral_const, Measure.real, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, one_mul]
  rcases hU2 with ⟨_, hsecond⟩
  rw [hsecond]
  ring

/-- The global cosh remainder estimate specialized to the overlap kernel of
two unit coefficient rows. -/
theorem spatialOverlap_cosh_remainder_le
    {τ rho : ℝ} (hτ : 0 ≤ τ) :
    Real.cosh (τ * rho) - 1 ≤
      τ ^ 2 * rho ^ 2 / 2 * Real.exp (τ * |rho|) := by
  have h := AlignmentExponential.cosh_sub_one_le_sq_exp_abs (τ * rho)
  have habs : |τ * rho| = τ * |rho| := by rw [abs_mul, abs_of_nonneg hτ]
  simpa [habs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

end BrownianSharp.AlignmentPaperSpatialExponential
