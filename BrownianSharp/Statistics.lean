import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import BrownianSharp.GaussianDensity

/-!
# Finite-grid Gaussian statistics

A finite deterministic layer for the Brownian sharp-certificate project.  The coefficient vector
is arbitrary here (and can later be evaluated under a Gaussian law).  The normalized p-statistic
is the uniform average of the p-th powers of linear row evaluations; its p-root is represented by
a rescaled `PiLp` norm.  Thus convexity is deterministic and does not assume concentration.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter ProbabilityTheory

namespace BrownianSharp

/-- An L² random variable with positive mean and no atom at its mean has strictly positive
variance. This is useful for invoking convex lower-tail inequalities, which require a nonzero
variance scale. -/
theorem variance_pos_of_positive_mean_and_null_mean_level
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MeasureTheory.MemLp X 2 μ) (hXm : Measurable X)
    (hmean : 0 < μ[X])
    (hlevel : ∀ r, 0 < r → μ {ω | X ω = r} = 0) :
    ProbabilityTheory.variance X μ > 0 := by
  by_contra hpos
  have hle : ProbabilityTheory.variance X μ ≤ 0 := le_of_not_gt hpos
  have hzero : ProbabilityTheory.variance X μ = 0 :=
    le_antisymm hle (ProbabilityTheory.variance_nonneg X μ)
  have hae : ∀ᵐ ω ∂μ, X ω = μ[X] :=
    ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hX hzero
  have hprob : μ {ω | X ω = μ[X]} = 1 :=
    (MeasureTheory.ae_iff_prob_eq_one (hXm.eq measurable_const)).1 hae
  rw [hlevel (μ[X]) hmean] at hprob
  norm_num at hprob

/-- A finite matrix acting on a coefficient vector by row evaluation. -/
def rowEvaluation {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : ι → κ → ℝ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := ∑ k, A i k * x k
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    simp [Finset.mul_sum, mul_left_comm]

/-- The same row evaluation, regarded as a vector in the finite-dimensional `Lᵖ` product. -/
def rowEvaluationLp {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : ENNReal) (A : ι → κ → ℝ) : (κ → ℝ) →ₗ[ℝ] PiLp p (fun _ : ι => ℝ) :=
  ((WithLp.linearEquiv p ℝ (ι → ℝ)).symm.toLinearMap).comp (rowEvaluation A)

/-- The normalized p-root of the uniform p-statistic on a nonempty finite grid. -/
def finiteGridRoot {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (A : ι → κ → ℝ) (x : κ → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) ^ (-(1 / (p : ℝ))) *
    ‖rowEvaluationLp (p : ENNReal) A x‖

/-- The normalized uniform average of the absolute p-th powers of the row evaluations. -/
def finiteGridMoment {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (A : ι → κ → ℝ) (x : κ → ℝ) : ℝ :=
  (∑ i, |rowEvaluation A x i| ^ p) / Fintype.card ι

/-- The normalized finite-grid p-root is convex for `p ≥ 2`. -/
theorem finiteGridRoot_convexOn {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    ConvexOn ℝ Set.univ (finiteGridRoot p A) := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  have hnorm : ConvexOn ℝ Set.univ (fun x => ‖rowEvaluationLp (p : ENNReal) A x‖) := by
    simpa only [Set.preimage_univ, Function.comp_def] using
      (convexOn_univ_norm.comp_linearMap (rowEvaluationLp (p : ENNReal) A))
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hscale : 0 ≤ (Fintype.card ι : ℝ) ^ (-(1 / (p : ℝ))) :=
    Real.rpow_nonneg (le_of_lt hcard) _
  change ConvexOn ℝ Set.univ
    (fun x => (Fintype.card ι : ℝ) ^ (-(1 / (p : ℝ))) *
      ‖rowEvaluationLp (p : ENNReal) A x‖)
  simpa only [smul_eq_mul] using hnorm.smul hscale

/-- The finite-grid root to the p-th power is exactly the uniform p-th moment.  The proof
uses the defining finite-product formula for `PiLp`; it is the bridge between the norm and the
statistic rather than an additional probabilistic hypothesis. -/
theorem finiteGridRoot_pow_eq_moment {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (x : κ → ℝ) :
    finiteGridRoot p A x ^ p = finiteGridMoment p A x := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 0 < p by omega)
  have hpcast : 0 < ((p : ENNReal)).toReal := by
    simpa using hpReal
  let S : ℝ := ∑ i, |rowEvaluation A x i| ^ p
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hnorm : ‖rowEvaluationLp ((p : ENNReal)) A x‖ = S ^ (1 / (p : ℝ)) := by
    rw [PiLp.norm_eq_sum hpcast]
    dsimp [S]
    simp [rowEvaluationLp]
  have hroot : finiteGridRoot p A x = (S / (Fintype.card ι : ℝ)) ^ (1 / (p : ℝ)) := by
    rw [finiteGridRoot, hnorm, Real.rpow_neg_eq_inv_rpow,
      Real.inv_rpow (le_of_lt hcard)]
    calc
      ((Fintype.card ι : ℝ) ^ (1 / (p : ℝ)))⁻¹ * S ^ (1 / (p : ℝ)) =
          S ^ (1 / (p : ℝ)) / (Fintype.card ι : ℝ) ^ (1 / (p : ℝ)) := by
            rw [div_eq_mul_inv]
            ring
      _ = (S / (Fintype.card ι : ℝ)) ^ (1 / (p : ℝ)) :=
        (Real.div_rpow hS (le_of_lt hcard) (1 / (p : ℝ))).symm
  rw [hroot, one_div, Real.rpow_inv_natCast_pow
    (div_nonneg hS (le_of_lt hcard)) (by omega : p ≠ 0)]
  simp [finiteGridMoment, S, div_eq_mul_inv]

/-- Any finite Lᵖ bound on the coefficient vector transports to the finite-grid root. -/
theorem finiteGridRoot_memLp_of_coeff_memLp
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    [FiniteDimensional ℝ (κ → ℝ)]
    {μ : MeasureTheory.Measure (κ → ℝ)}
    (q : ENNReal) (hcoeff : MeasureTheory.MemLp (id : (κ → ℝ) → (κ → ℝ)) q μ)
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    MeasureTheory.MemLp (fun x => finiteGridRoot p A x) q μ := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  let L : (κ → ℝ) →L[ℝ] PiLp (p : ENNReal) (fun _ : ι => ℝ) :=
    ⟨rowEvaluationLp (p : ENNReal) A,
      (rowEvaluationLp (p : ENNReal) A).continuous_of_finiteDimensional⟩
  have hrows : MeasureTheory.MemLp (fun x => L x) q μ :=
    hcoeff.continuousLinearMap_comp L
  have hnorm : MeasureTheory.MemLp (fun x => ‖L x‖) q μ := hrows.norm
  simpa [finiteGridRoot, L] using
    hnorm.const_mul ((Fintype.card ι : ℝ) ^ (-(1 / (p : ℝ))))

/-- A finite-dimensional Gaussian coefficient vector has every finite-moment finite-grid
p-root in `L^q`.  This is the direct random-variable form of the bounded linear-map transport
above; all dependence on the Gaussian law is isolated in `HasGaussianLaw.memLp`. -/
theorem finiteGridRoot_memLp_of_hasGaussianLaw
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι] [Nonempty ι]
    [FiniteDimensional ℝ (κ → ℝ)]
    {μ : MeasureTheory.Measure Ω} {G : Ω → κ → ℝ}
    (hG : ProbabilityTheory.HasGaussianLaw G μ)
    (q : ENNReal) (hq : q ≠ ⊤)
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    MeasureTheory.MemLp (fun ω => finiteGridRoot p A (G ω)) q μ := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  let L : (κ → ℝ) →L[ℝ] PiLp (p : ENNReal) (fun _ : ι => ℝ) :=
    ⟨rowEvaluationLp (p : ENNReal) A,
      (rowEvaluationLp (p : ENNReal) A).continuous_of_finiteDimensional⟩
  have hrows : MeasureTheory.MemLp (fun ω => L (G ω)) q μ :=
    (hG.memLp hq).continuousLinearMap_comp L
  have hnorm : MeasureTheory.MemLp (fun ω => ‖L (G ω)‖) q μ := hrows.norm
  simpa [finiteGridRoot, L] using
    hnorm.const_mul ((Fintype.card ι : ℝ) ^ (-(1 / (p : ℝ))))

/-- In particular, the p-root is square-integrable whenever the coefficients are. -/
theorem finiteGridRoot_memLp_two_of_coeff_memLp
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    [FiniteDimensional ℝ (κ → ℝ)]
    {μ : MeasureTheory.Measure (κ → ℝ)}
    (hcoeff : MeasureTheory.MemLp (id : (κ → ℝ) → (κ → ℝ)) 2 μ)
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    MeasureTheory.MemLp (fun x => finiteGridRoot p A x) 2 μ :=
  finiteGridRoot_memLp_of_coeff_memLp 2 hcoeff p hp A

/-- The normalized p-th moment is in L² if the p-root lies in L^{2p}. -/
theorem finiteGridMoment_memLp_two_of_root_memLp
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι] [Nonempty ι]
    {μ : MeasureTheory.Measure Ω} {G : Ω → κ → ℝ}
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ)
    (hroot : MeasureTheory.MemLp (fun ω => finiteGridRoot p A (G ω)) (2 * p) μ) :
    MeasureTheory.MemLp (fun ω => finiteGridMoment p A (G ω)) 2 μ := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  have hpow := hroot.norm_rpow_div (p : ENNReal)
  have hroot_nonneg : ∀ ω, 0 ≤ finiteGridRoot p A (G ω) := by
    intro ω
    unfold finiteGridRoot
    positivity
  have hmoment : (fun ω => finiteGridMoment p A (G ω)) =
      (fun ω => ‖finiteGridRoot p A (G ω)‖ ^ (p : ENNReal).toReal) := by
    funext ω
    have hcast : (p : ENNReal).toReal = (p : ℝ) := by simp
    rw [Real.norm_of_nonneg (hroot_nonneg ω), hcast, Real.rpow_natCast]
    exact (finiteGridRoot_pow_eq_moment p hp A (G ω)).symm
  have hpne : (p : ENNReal) ≠ 0 := by
    exact_mod_cast (by omega : p ≠ 0)
  have hexp : (2 * p : ENNReal) / (p : ENNReal) = 2 := by
    rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hpne ENNReal.coe_ne_top,
      mul_one]
  rw [hexp] at hpow
  simpa only [hmoment] using hpow

/-- The Gaussian finite-grid p-statistic is square-integrable.  The input Gaussian vector has
all finite moments, so the preceding `L^{2p}` transport supplies the moment needed for the
p-th-power statistic. -/
theorem finiteGridMoment_memLp_two_of_hasGaussianLaw
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι] [Nonempty ι]
    [FiniteDimensional ℝ (κ → ℝ)]
    {μ : MeasureTheory.Measure Ω} {G : Ω → κ → ℝ}
    (hG : ProbabilityTheory.HasGaussianLaw G μ)
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    MeasureTheory.MemLp (fun ω => finiteGridMoment p A (G ω)) 2 μ := by
  have hroot : MeasureTheory.MemLp (fun ω => finiteGridRoot p A (G ω))
      (2 * (p : ENNReal)) μ := by
    apply finiteGridRoot_memLp_of_hasGaussianLaw hG (2 * (p : ENNReal)) ?_ p hp A
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  exact finiteGridMoment_memLp_two_of_root_memLp p hp A hroot

/-- The same Gaussian-ready estimate in integral form. -/
theorem finiteGridRoot_sq_integrable_of_coeff_memLp
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    [FiniteDimensional ℝ (κ → ℝ)]
    {μ : MeasureTheory.Measure (κ → ℝ)}
    (hcoeff : MeasureTheory.MemLp (id : (κ → ℝ) → (κ → ℝ)) 2 μ)
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    MeasureTheory.Integrable (fun x => finiteGridRoot p A x ^ 2) μ := by
  exact (finiteGridRoot_memLp_two_of_coeff_memLp hcoeff p hp A).integrable_sq

/-- The normalized finite-grid p-statistic is convex for `p ≥ 2`. -/
theorem finiteGridMoment_convexOn {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) :
    ConvexOn ℝ Set.univ (finiteGridMoment p A) := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  have hroot := finiteGridRoot_convexOn p hp A
  have hroot_nonneg : ∀ ⦃x : κ → ℝ⦄, x ∈ Set.univ → 0 ≤ finiteGridRoot p A x := by
    intro x hx
    unfold finiteGridRoot
    apply mul_nonneg
    · exact Real.rpow_nonneg (by positivity) _
    · exact norm_nonneg (rowEvaluationLp ((p : ENNReal)) A x)
  have hpow : ConvexOn ℝ Set.univ (fun x => finiteGridRoot p A x ^ p) :=
    hroot.pow hroot_nonneg p
  have heq : (fun x => finiteGridMoment p A x) =
      (fun x => finiteGridRoot p A x ^ p) := by
    funext x
    symm
    exact finiteGridRoot_pow_eq_moment p hp A x
  change ConvexOn ℝ Set.univ (fun x => finiteGridMoment p A x)
  rw [heq]
  exact hpow

/-- If `p` is even, each row's p-th power is the usual nonnegative absolute p-th power. -/
theorem rowEvaluation_even_power {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : ℕ) (hp : Even p) (A : ι → κ → ℝ) (x : κ → ℝ) (i : ι) :
    (rowEvaluation A x i) ^ p = |rowEvaluation A x i| ^ p := by
  by_cases hx : 0 ≤ rowEvaluation A x i
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    symm
    exact hp.neg_pow (rowEvaluation A x i)

/-- Positive scaling is exact for the normalized p-root, as for any seminorm. -/
theorem finiteGridRoot_smul {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (x : κ → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    finiteGridRoot p A (c • x) = c * finiteGridRoot p A x := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by
    have hp1 : 1 ≤ p := by omega
    exact_mod_cast hp1⟩
  unfold finiteGridRoot
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

/-- Every positive level of a nonnegative homogeneous convex statistic lies on the frontier
of its sublevel set. -/
theorem finiteGridRoot_level_subset_frontier {κ ι : Type*} [Fintype κ] [Fintype ι]
    [Nonempty ι] (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (r : ℝ) (hr : 0 < r) :
    {x | finiteGridRoot p A x = r} ⊆
      frontier {x | finiteGridRoot p A x ≤ r} := by
  intro x hx
  have hxsub : x ∈ {y | finiteGridRoot p A y ≤ r} := by simp [hx.le]
  rw [mem_frontier_iff_notMem_interior hxsub]
  intro hxint
  let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hc_tendsto : Tendsto c atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hrecip : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [c] using hconst.add hrecip
  have hscale_tendsto : Tendsto (fun n => c n • x) atTop (𝓝 x) := by
    have hconstx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hpair : Tendsto (fun n => (c n, x)) atTop (𝓝 (1, x)) := by
      simpa only [nhds_prod_eq] using hc_tendsto.prodMk hconstx
    have h := (continuous_smul.tendsto (1, x)).comp hpair
    simpa [Function.comp_def] using h
  have hevent : ∀ᶠ n in atTop, c n • x ∈ interior {y | finiteGridRoot p A y ≤ r} :=
    hscale_tendsto.eventually (isOpen_interior.mem_nhds hxint)
  obtain ⟨n, hn⟩ := hevent.exists
  have hc_nonneg : 0 ≤ c n := by positivity
  have hc_gt : 1 < c n := by
    dsimp [c]
    have : 0 < (n : ℝ) + 1 := by positivity
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hscaled := finiteGridRoot_smul p hp A x (c n) hc_nonneg
  have hnot : ¬ c n • x ∈ {y | finiteGridRoot p A y ≤ r} := by
    simp only [Set.mem_setOf_eq]
    rw [hscaled, hx]
    nlinarith
  exact hnot (interior_subset hn)

/-- Under any measure absolutely continuous with respect to Lebesgue/Haar volume, the positive
levels of the finite-grid p-root have zero measure. This isolates the geometric no-atoms step from
the Gaussian density calculation. -/
theorem finiteGridRoot_level_measure_zero_of_ac {κ ι : Type*} [Fintype κ] [Fintype ι]
    [Nonempty ι] (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (r : ℝ) (hr : 0 < r)
    (μ : MeasureTheory.Measure (κ → ℝ))
    (hac : μ ≪ (MeasureTheory.volume : MeasureTheory.Measure (κ → ℝ))) :
    μ {x | finiteGridRoot p A x = r} = 0 := by
  apply hac
  apply measure_mono_null (finiteGridRoot_level_subset_frontier p hp A r hr)
  have hconvex : Convex ℝ {x : κ → ℝ | finiteGridRoot p A x ≤ r} := by
    simpa using (finiteGridRoot_convexOn p hp A).convex_le r
  exact Convex.addHaar_frontier (μ := (MeasureTheory.volume : MeasureTheory.Measure (κ → ℝ)))
    hconvex

/-- The positive levels of any finite-grid p-root have no atoms under the full-rank standard
Gaussian coefficient law.  The statistic itself may have a kernel: the frontier argument only
uses convexity and positive homogeneity, while absolute continuity is applied in the original
coefficient space. -/
theorem finiteGridRoot_level_standardGaussian_measure_zero {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (r : ℝ) (hr : 0 < r) :
    (MeasureTheory.Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1))
      {x | finiteGridRoot p A x = r} = 0 := by
  exact finiteGridRoot_level_measure_zero_of_ac p hp A r hr _
    BrownianSharp.GaussianDensity.standardGaussian_absolutelyContinuous

/-- For even `p`, the absolute-power average defining `finiteGridMoment` is the usual
uniform average of the signed row p-th powers. -/
theorem finiteGridMoment_eq_raw_average_of_even {κ ι : Type*} [Fintype κ] [Fintype ι]
    [Nonempty ι] (p : ℕ) (hp : Even p) (A : ι → κ → ℝ) (x : κ → ℝ) :
    finiteGridMoment p A x = (∑ i, rowEvaluation A x i ^ p) / Fintype.card ι := by
  unfold finiteGridMoment
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  symm
  exact rowEvaluation_even_power p hp A x i


end BrownianSharp
