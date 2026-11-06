import BrownianSharp.AlignmentPaperContinuumGenericBump
import BrownianSharp.AlignmentPaperGenericContinuumConfinement

/-! The actual Gaussian hyperbolic sum for every admissible bump.  The
normalization and continuum variance are proved before the confinement
endpoint, rather than assumed from a finite-grid surrogate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperGenericBumpCertified
open AlignmentPaperContinuumGenericBump AlignmentPaperContinuumGoodRegion
open AlignmentPaperGenericContinuumVariance AlignmentPaperGenericContinuumConfinement

/-- The manuscript's Gaussian synthesis on the real cube. -/
def bumpSynthesis {d n : ℕ} (ψ : AdmissibleBump)
    (z : LayerIndex d n → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ a : LayerIndex d n, cubeBumpAtom ψ x a * z a

/-- The lower energy bound on the genuine good region converts a uniform
bound for the original field into the corresponding normalized-row bound. -/
theorem bump_event_subset_rows {d n : ℕ} (hd : 0 < d)
    (ψ : AdmissibleBump) {c : ℝ} (hc : 0 ≤ c) :
    {z : LayerIndex d n → ℝ | ∀ x ∈ cubeSet d,
      |bumpSynthesis ψ z x| ≤
        (c * Real.sqrt (ψ.squareIntegral ^ d / 2)) *
          Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ⊆
    {z | ∀ x ∈ cubeBumpGoodSet (d := d) (n := n) ψ,
      |∑ a : LayerIndex d n, cubeBumpGoodRow ψ x a * z a| ≤
        c * Real.sqrt (n : ℝ)} := by
  intro z hz x hx
  let q : ℝ := ψ.squareIntegral ^ d / 2
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (pow_pos ψ.squareIntegral_pos d) (by norm_num)
  have hS : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
  have hfloor : hyperbolicCount d n * q ≤ cubeBumpEnergy (d := d) (n := n) ψ x := by
    have h := hx.2
    rw [cubeBumpEnergyMean_eq_layerCount_mass_pow ψ hd] at h
    simpa [q, mul_div_assoc] using h
  have hE : 0 < cubeBumpEnergy (d := d) (n := n) ψ x := (mul_pos hS hq).trans_le hfloor
  have hsqrt : 0 < Real.sqrt (cubeBumpEnergy (d := d) (n := n) ψ x) := Real.sqrt_pos.mpr hE
  have heval : (∑ a : LayerIndex d n, cubeBumpGoodRow ψ x a * z a) =
      bumpSynthesis ψ z x / Real.sqrt (cubeBumpEnergy (d := d) (n := n) ψ x) := by
    unfold cubeBumpGoodRow bumpSynthesis
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [heval, abs_div, abs_of_pos hsqrt]
  apply (div_le_iff₀ hsqrt).2
  calc
    |bumpSynthesis ψ z x| ≤
        (c * Real.sqrt q) * Real.sqrt ((n : ℝ) * hyperbolicCount d n) :=
      hz x hx.1
    _ = (c * Real.sqrt (n : ℝ)) *
        Real.sqrt (hyperbolicCount d n * q) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ)), Real.sqrt_mul hS.le]
      ring
    _ ≤ (c * Real.sqrt (n : ℝ)) * Real.sqrt (cubeBumpEnergy (d := d) (n := n) ψ x) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfloor) (mul_nonneg hc (Real.sqrt_nonneg _))

/-- The literal uniform confinement theorem for every continuous admissible
bump, with constants chosen before the hyperbolic level and coefficients. -/
theorem eventually_bumpSynthesis_confinement {d : ℕ} (hd : 2 ≤ d)
    (ψ : AdmissibleBump) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {z | ∀ x ∈ cubeSet d, |bumpSynthesis ψ z x| ≤
          a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
        Real.exp (-b * nativeDimension d n) := by
  have hq : 0 < ψ.squareIntegral ^ d / 2 :=
    div_pos (pow_pos ψ.squareIntegral_pos d) (by norm_num)
  have hL : 0 < 2 / ψ.squareIntegral ^ d :=
    div_pos (by norm_num) (pow_pos ψ.squareIntegral_pos d)
  obtain ⟨c, b, hc, hb, N, hN⟩ := eventually_regionRows_confinement hd hq hL
    (fun n => cubeBumpRegionRows (d := d) (n := n) ψ hd)
  refine ⟨c * Real.sqrt (ψ.squareIntegral ^ d / 2), b,
    mul_pos hc (Real.sqrt_pos.mpr hq), hb, N, ?_⟩
  intro n hn
  apply (measureReal_mono (bump_event_subset_rows (by omega) ψ hc.le)).trans
  exact hN n hn

theorem bumpSynthesis_event_measurable {d n : ℕ} (ψ : AdmissibleBump) (r : ℝ) :
    MeasurableSet {z : LayerIndex d n → ℝ | ∀ x ∈ cubeSet d,
      |bumpSynthesis ψ z x| ≤ r} := by
  apply IsClosed.measurableSet
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _hx
  apply isClosed_le _ continuous_const
  apply Continuous.abs
  unfold bumpSynthesis
  apply continuous_finsetSum
  intro a _ha
  exact continuous_const.mul (continuous_apply a)

/-- The same constants work on every probability space carrying independent
standard Gaussian coefficients. Joint-law identification uses Mathlib's
`iIndepFun.hasLaw_pi`, and no law of a surrogate field is substituted. -/
theorem eventually_bumpSynthesis_confinement_iid.{u} {d : ℕ} (hd : 2 ≤ d)
    (ψ : AdmissibleBump) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (G : LayerIndex d n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∀ x ∈ cubeSet d,
          |bumpSynthesis ψ (fun i => G i ω) x| ≤
            a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
          Real.exp (-b * nativeDimension d n) := by
  obtain ⟨a, b, ha, hb, N, hN⟩ := eventually_bumpSynthesis_confinement hd ψ
  refine ⟨a, b, ha, hb, N, ?_⟩
  intro n hn Ω _mΩ P G hG hInd
  have hLaw : HasLaw (fun ω i => G i ω)
      (productStandardGaussian (LayerIndex d n)) P := hInd.hasLaw_pi hG
  rw [hLaw.measureReal_eq (bumpSynthesis_event_measurable ψ _)]
  exact hN n hn

/-- Realization-independent version of the manuscript confinement statement. -/
def AdmissibleBumpIidConfinementStatement.{u} : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ψ : AdmissibleBump,
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (G : LayerIndex d n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∀ x ∈ cubeSet d,
          |bumpSynthesis ψ (fun i => G i ω) x| ≤
            a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
          Real.exp (-b * nativeDimension d n)

theorem admissibleBumpIidConfinement_certified.{u} :
    AdmissibleBumpIidConfinementStatement.{u} := by
  intro d hd ψ
  exact eventually_bumpSynthesis_confinement_iid hd ψ

/-- Lemma 2.3, (2.14): the correlation cap, including the unit bound. -/
theorem bumpRowCorrelation_abs_le_min {d n h : ℕ} (hd : 0 < d)
    (ψ : AdmissibleBump) (x y : Fin d → ℝ)
    (hx : x ∈ cubeBumpGoodSet (d := d) (n := n) ψ)
    (hy : y ∈ cubeBumpGoodSet (d := d) (n := n) ψ)
    (u : Fin d → ℕ)
    (hu : (fun i => (x i, y i)) ∈ AlignmentPaperContinuumHulls.tensorOppositeHullShell u)
    (hgrade : (∑ i, u i) = n + h) :
    |rowCorrelation (cubeBumpGoodRow (d := d) (n := n) ψ) x y| ≤
      min 1 ((2 / ψ.squareIntegral ^ d) * hyperbolicCount d h / hyperbolicCount d n) := by
  apply le_min
  · exact AlignmentPaperSpatialVariance.row_overlap_abs_le_one
      (cubeBumpGoodRow ψ x) (cubeBumpGoodRow ψ y)
      (cubeBumpGoodRow_unit_on_goodSet ψ hd x hx)
      (cubeBumpGoodRow_unit_on_goodSet ψ hd y hy)
  · apply (cubeBumpRowCorrelation_abs_le_of_hullShell ψ hd x y hx hy u hu hgrade).trans
    unfold shapeOverlapCap
    apply div_le_div_of_nonneg_right _ (hyperbolicCount_pos (by omega)).le
    exact mul_le_mul_of_nonneg_left (min_le_right _ _)
      (div_nonneg (by norm_num) (pow_pos ψ.squareIntegral_pos d).le)

/-- Lemma 2.4, (2.18): the variance bound on the good region. -/
theorem bumpSpatial_variance_le {d n : ℕ} (hd : 2 ≤ d)
    (ψ : AdmissibleBump) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτbound : τ ≤
      (Real.log 2 / (4 * (2 / ψ.squareIntegral ^ d) * (Nat.factorial (d - 1) : ℝ))) *
        ((n : ℝ) + 1)) :
    variance (AlignmentPaperSpatialExponential.spatialCoshAverage
      (normalizedRegionProbability (cubeBumpGoodSet (d := d) (n := n) ψ))
      τ (cubeBumpGoodRow (d := d) (n := n) ψ))
      (productStandardGaussian (LayerIndex d n)) ≤
      (((ψ.squareIntegral ^ d / 2)⁻¹ ^ 2 *
        AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d
          (2 / ψ.squareIntegral ^ d)) * τ ^ 2) / nativeDimension d n := by
  exact regionRows_variance_le_uniform hd
    (div_pos (pow_pos ψ.squareIntegral_pos d) (by norm_num))
    (div_pos (by norm_num) (pow_pos ψ.squareIntegral_pos d)) hτ hτbound
    (cubeBumpRegionRows ψ hd)

end BrownianSharp.AlignmentPaperGenericBumpCertified
