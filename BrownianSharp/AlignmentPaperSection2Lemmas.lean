import BrownianSharp.AlignmentPaperGenericBumpCertified
import BrownianSharp.AlignmentPaperSpatialConvexity

/-! Literal statements of Lemma 2.3, Lemma 2.4 and Proposition 2.6 of the
manuscript, packaged from the certified hull, correlation, soft-maximum and
convex lower-tail results. -/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianSharp BrownianSharp.Concentration
open BrownianSharp.AlignmentPaperContinuumHulls
open BrownianSharp.AlignmentPaperContinuumGoodRegion
open BrownianSharp.AlignmentPaperContinuumGenericBump
open BrownianSharp.AlignmentPaperGenericContinuumVariance

namespace BrownianSharp.AlignmentPaperSection2Lemmas

/-! ### Lemma 2.3 -/

private theorem floor_of_mem_cell {j c : ℕ} {x : ℝ}
    (hx : x ∈ HaarQuarter.realDyadicCell j c) : 0 ≤ x ∧ ⌊x * 2 ^ j⌋₊ = c := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  simp only [HaarQuarter.realDyadicCell, Set.mem_Ico] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [div_le_iff₀ hp] at h1
  rw [lt_div_iff₀ hp] at h2
  have hx0 : 0 ≤ x := by
    by_contra hn
    nlinarith [not_le.mp hn, (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  refine ⟨hx0, (Nat.floor_eq_iff (by positivity)).2 ⟨h1, ?_⟩⟩
  push_cast at h2
  exact h2

private theorem floor_succ {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ⌊x * 2 ^ j⌋₊ = ⌊x * 2 ^ (j + 1)⌋₊ / 2 := by
  have e : x * 2 ^ (j + 1) = 2 * (x * 2 ^ j) := by ring
  have h1 := Nat.floor_le (by positivity : 0 ≤ x * 2 ^ (j + 1))
  have h2 := Nat.lt_floor_add_one (x * 2 ^ (j + 1))
  set n := ⌊x * 2 ^ (j + 1)⌋₊
  have hm : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
  have hm2 : (n : ℝ) + 1 ≤ 2 * ((n / 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * (n / 2) + 2)
  rw [e] at h1 h2
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> linarith

private theorem shell_floor {k : ℕ} {p : ℝ × ℝ} (hp : p ∈ oneDyadicOppositeHalfShell k) :
    ⌊p.1 * 2 ^ (k + 1)⌋₊ / 2 = ⌊p.2 * 2 ^ (k + 1)⌋₊ / 2 ∧
      ⌊p.1 * 2 ^ (k + 1)⌋₊ ≠ ⌊p.2 * 2 ^ (k + 1)⌋₊ := by
  simp only [oneDyadicOppositeHalfShell, oneDyadicOppositeHalfPair, Set.mem_iUnion,
    Set.mem_union, Set.mem_prod] at hp
  obtain ⟨c, -, ⟨hl, hr⟩ | ⟨hr, hl⟩⟩ := hp
  · have h1 := floor_of_mem_cell (j := k + 1) (c := 2 * c) hl
    have h2 := floor_of_mem_cell (j := k + 1) (c := 2 * c + 1) hr
    rw [h1.2, h2.2]; omega
  · have h1 := floor_of_mem_cell (j := k + 1) (c := 2 * c + 1) hr
    have h2 := floor_of_mem_cell (j := k + 1) (c := 2 * c) hl
    rw [h1.2, h2.2]; omega

private theorem shell_nonneg {k : ℕ} {p : ℝ × ℝ} (hp : p ∈ oneDyadicOppositeHalfShell k) :
    0 ≤ p.1 ∧ 0 ≤ p.2 := by
  simp only [oneDyadicOppositeHalfShell, oneDyadicOppositeHalfPair, Set.mem_iUnion,
    Set.mem_union, Set.mem_prod] at hp
  obtain ⟨c, -, ⟨hl, hr⟩ | ⟨hr, hl⟩⟩ := hp
  · exact ⟨(floor_of_mem_cell (j := k + 1) (c := 2 * c) hl).1,
      (floor_of_mem_cell (j := k + 1) (c := 2 * c + 1) hr).1⟩
  · exact ⟨(floor_of_mem_cell (j := k + 1) (c := 2 * c + 1) hr).1,
      (floor_of_mem_cell (j := k + 1) (c := 2 * c) hl).1⟩

/-- Opposite-half shells of different depths are disjoint. -/
private theorem shell_disjoint {k k' : ℕ} (h : k < k') :
    Disjoint (oneDyadicOppositeHalfShell k) (oneDyadicOppositeHalfShell k') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨h0, h0'⟩ := shell_nonneg hp
  obtain ⟨e, ne⟩ := shell_floor hp
  obtain ⟨e', -⟩ := shell_floor hp'
  have hdown : ∀ m, k + 1 ≤ m → ⌊p.1 * 2 ^ m⌋₊ = ⌊p.2 * 2 ^ m⌋₊ →
      ⌊p.1 * 2 ^ (k + 1)⌋₊ = ⌊p.2 * 2 ^ (k + 1)⌋₊ := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact id
    | succ m _ ih =>
      intro hE
      apply ih
      rw [floor_succ h0, floor_succ h0', hE]
  apply ne
  apply hdown k' (by omega)
  rw [floor_succ h0, floor_succ h0']
  exact e'

/-- Lemma 2.3. (2.13): `λ^{2d}{Hull(x,y) ∈ 𝒟_u} = 2^{-u-d} S_u`, where the event is the
union over the profiles of total grade `u` of the first-separation shells; and
(2.14): for pairs of good points whose hull has profile `w`, the correlation vanishes
if the hull volume `2^{-|w|}` exceeds `2^{-n}`, and `|ρ| ≤ min {1, c⁻¹ S_h / S_n}` if the
hull lies in `𝒟_{n+h}`, with `c⁻¹ = 2/‖ψ‖₂^{2d}`. -/
theorem lemma_2_3 {d : ℕ} (hd : 0 < d) :
    (∀ u : ℕ, ((cubeLebesgue d).prod (cubeLebesgue d)).real
        (⋃ w : ContinuumHullProfile d u, spatialPairHullShell w.1) =
      (1 / 2 : ℝ) ^ (u + d) * hyperbolicCount d u) ∧
    ∀ (ψ : AdmissibleBump) (n : ℕ), ∀ x ∈ cubeBumpGoodSet (d := d) (n := n) ψ,
      ∀ y ∈ cubeBumpGoodSet (d := d) (n := n) ψ, ∀ w : Fin d → ℕ,
      (x, y) ∈ spatialPairHullShell w →
      ((∑ i, w i) < n →
        rowCorrelation (cubeBumpGoodRow (d := d) (n := n) ψ) x y = 0) ∧
      ∀ h : ℕ, (∑ i, w i) = n + h →
        |rowCorrelation (cubeBumpGoodRow (d := d) (n := n) ψ) x y| ≤
          min 1 ((2 / ψ.squareIntegral ^ d) * hyperbolicCount d h / hyperbolicCount d n) := by
  refine ⟨fun u => ?_, fun ψ n x hx y hy w hw => ⟨fun hlt => ?_, fun h hgrade => ?_⟩⟩
  · have hdisj : Pairwise (Function.onFun Disjoint
        (fun w : ContinuumHullProfile d u => spatialPairHullShell w.1)) := by
      intro w w' hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (fun h => hne (Subtype.ext h))
      rw [Function.onFun, Set.disjoint_left]
      intro p h1 h2
      have h1' := Set.mem_univ_pi.mp h1 i
      have h2' := Set.mem_univ_pi.mp h2 i
      rcases lt_or_gt_of_ne hi with hlt | hlt
      · exact Set.disjoint_left.mp (shell_disjoint hlt) h1' h2'
      · exact Set.disjoint_left.mp (shell_disjoint hlt) h2' h1'
    rw [measureReal_iUnion_fintype hdisj
      (fun w => spatialPairHullShell_measurable w.1) (fun w => measure_ne_top _ _)]
    have hone : ∀ w : ContinuumHullProfile d u,
        ((cubeLebesgue d).prod (cubeLebesgue d)).real (spatialPairHullShell w.1) =
          (1 / 2 : ℝ) ^ (u + d) := by
      intro w
      rw [Measure.real_def, spatialPairHullShell_measure, tensorOppositeHullShell_measure_eq,
        ENNReal.toReal_ofReal (by positivity), w.2]
    simp_rw [hone]
    rw [Finset.sum_const, Finset.card_univ, continuumHullProfile_card d u hd]
    simp [hyperbolicCount, nsmul_eq_mul, mul_comm]
  · exact cubeBumpRowCorrelation_eq_zero_of_lowHullShell ψ x y w hw hlt
  · exact AlignmentPaperGenericBumpCertified.bumpRowCorrelation_abs_le_min hd ψ x y hx hy w hw
      hgrade

/-! ### Lemma 2.4 -/

/-- The soft maximum `U_τ` of (2.17), on the good region `A_n`. -/
def goodRegionU {d n : ℕ} (ψ : AdmissibleBump) (τ : ℝ) : (LayerIndex d n → ℝ) → ℝ :=
  AlignmentPaperSpatialExponential.spatialCoshAverage
    (normalizedRegionProbability (cubeBumpGoodSet (d := d) (n := n) ψ)) τ
    (cubeBumpGoodRow (d := d) (n := n) ψ)

private theorem goodRegionU_eq_unit {d n : ℕ} (hd : 2 ≤ d) (ψ : AdmissibleBump) :
    ∃ a : (Fin d → ℝ) → LayerIndex d n → ℝ, (∀ x, ∑ i, a x i ^ 2 = 1) ∧
      (∀ i, Measurable fun x => a x i) ∧
      ∀ τ, goodRegionU (d := d) (n := n) ψ τ =
        AlignmentPaperSpatialExponential.spatialCoshAverage
          (normalizedRegionProbability (cubeBumpGoodSet (d := d) (n := n) ψ)) τ a := by
  classical
  let s := cubeBumpRegionRows (d := d) (n := n) ψ hd
  have hm : 0 < cubeLebesgue d s.region :=
    (ENNReal.ofReal_pos.mpr (div_pos (pow_pos ψ.squareIntegral_pos d)
      (by norm_num))).trans_le s.mass_lower
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hm.ne'
  refine ⟨fun x => if x ∈ s.region then s.rows x else s.rows x₀,
    fun x => ?_, fun i => ?_, fun τ => ?_⟩
  · by_cases hx : x ∈ s.region <;> simp [hx, s.unit x₀ hx₀, s.unit x]
  · have : (fun x => (if x ∈ s.region then s.rows x else s.rows x₀) i) =
        fun x => if x ∈ s.region then s.rows x i else s.rows x₀ i := by
      ext x; by_cases hx : x ∈ s.region <;> simp [hx]
    rw [this]
    exact Measurable.ite s.region_measurable (s.rows_measurable i) measurable_const
  · funext z
    unfold goodRegionU AlignmentPaperSpatialExponential.spatialCoshAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [normalizedRegion_ae_mem s.region s.region_measurable] with x hx
    simp [hx]
    rfl

/-- Lemma 2.4. For every `τ > 0`, `E[U_τ] = 1`, `log U_τ` is a convex function of the
coefficients, and `E[U_τ^p] < ∞` for every `p > 0`; moreover there are `κ, C > 0`
(depending only on `d` and `ψ`) with `Var(U_τ) ≤ C τ² / |𝒟_n|`, `|𝒟_n| = 2^n S_n`,
for all `n` and all `0 < τ ≤ κ (n + 1)`. -/
theorem lemma_2_4 {d : ℕ} (hd : 2 ≤ d) (ψ : AdmissibleBump) :
    (∀ (n : ℕ) (τ : ℝ), 0 < τ →
      ∫ z, goodRegionU (d := d) (n := n) ψ τ z ∂productStandardGaussian (LayerIndex d n) = 1 ∧
      ConvexOn ℝ Set.univ (fun z => Real.log (goodRegionU (d := d) (n := n) ψ τ z)) ∧
      ∀ p : ℝ, 0 < p →
        Integrable (fun z => goodRegionU (d := d) (n := n) ψ τ z ^ p)
          (productStandardGaussian (LayerIndex d n))) ∧
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ (n : ℕ) (τ : ℝ), 0 < τ → τ ≤ κ * ((n : ℝ) + 1) →
      variance (goodRegionU (d := d) (n := n) ψ τ) (productStandardGaussian (LayerIndex d n)) ≤
        C * τ ^ 2 / nativeDimension d n := by
  have hq : 0 < ψ.squareIntegral ^ d / 2 := div_pos (pow_pos ψ.squareIntegral_pos d) (by norm_num)
  have hL : 0 < 2 / ψ.squareIntegral ^ d := div_pos (by norm_num) (pow_pos ψ.squareIntegral_pos d)
  refine ⟨fun n τ hτ => ?_, ⟨Real.log 2 / (4 * (2 / ψ.squareIntegral ^ d) *
      (Nat.factorial (d - 1) : ℝ)),
    (ψ.squareIntegral ^ d / 2)⁻¹ ^ 2 *
      AlignmentPaperContinuumShellBudgetScale.continuumShellConstant d (2 / ψ.squareIntegral ^ d),
    by positivity, mul_pos (by positivity)
      (AlignmentPaperContinuumShellBudgetScale.continuumShellConstant_pos d hL),
    fun n τ hτ hb => ?_⟩⟩
  · obtain ⟨a, ha, hmeas, hU⟩ := goodRegionU_eq_unit (n := n) hd ψ
    have := normalizedRegion_isProbability (cubeBumpGoodSet (d := d) (n := n) ψ)
      ((ENNReal.ofReal_pos.mpr hq).trans_le (cubeBumpRegionRows (d := d) (n := n) ψ hd).mass_lower)
    have hU' : goodRegionU (d := d) (n := n) ψ τ = _ := hU τ
    rw [hU']
    refine ⟨AlignmentPaperSpatialExponential.productGaussian_spatialCoshAverage_mean_actual _ a τ
      hτ.le ha hmeas, AlignmentPaperSpatialConvexity.spatialCoshAverage_log_convexOn _ τ a ha hmeas,
      fun p hp => AlignmentPaperSpatialConvexity.spatialCoshAverage_rpow_integrable _ τ hτ.le a ha
        hmeas p hp⟩
  · have := AlignmentPaperGenericBumpCertified.bumpSpatial_variance_le hd ψ hτ.le hb
    simpa only [goodRegionU, mul_div_assoc] using this

/-! ### Proposition 2.6 -/

/-- Proposition 2.6 (lower tail of a convex logarithm), with `q = Φ⁻¹(3/4)`:
`ℙ{f(G) ≤ -t} ≤ Φ(-q(t-1)/(3σ)) ≤ exp(-q²(t-1)²/(18σ²))` for all `t ≥ 1`. -/
theorem proposition_2_6 {κ : Type*} [Fintype κ]
    (f : (κ → ℝ) → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (hY : MemLp (fun x => Real.exp (f x)) 2 (productStandardGaussian κ))
    (hmean : (productStandardGaussian κ)[fun x => Real.exp (f x)] = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1 / 4)
    (hvar : variance (fun x => Real.exp (f x)) (productStandardGaussian κ) ≤ σ ^ 2) :
    ∀ t : ℝ, 1 ≤ t →
      (productStandardGaussian κ).real {x | f x ≤ -t} ≤
        standardGaussianCDF (-(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ))) ∧
      standardGaussianCDF (-(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ))) ≤
        Real.exp (-(standardGaussianQuantile (3 / 4) ^ 2 * (t - 1) ^ 2 / (18 * σ ^ 2))) := by
  intro t ht
  have hfcont : Continuous f := continuousOn_univ.mp (hfconv.continuousOn isOpen_univ)
  have hYmeas : Measurable (fun x => Real.exp (f x)) :=
    (Real.continuous_exp.comp hfcont).measurable
  have hq : 0 < standardGaussianQuantile (3 / 4) := by
    have hqcdf := standardGaussianCDF_standardGaussianQuantile (u := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)
    by_contra hn
    have h := standardGaussianCDF_strictMono.monotone (le_of_not_gt hn)
    rw [hqcdf, standardGaussianCDF_zero] at h
    norm_num at h
  have ha : 0 ≤ standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ) :=
    div_nonneg (mul_nonneg hq.le (by linarith)) (by positivity)
  have hexp : standardGaussianCDF (-(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ))) ≤
      Real.exp (-(standardGaussianQuantile (3 / 4) ^ 2 * (t - 1) ^ 2 / (18 * σ ^ 2))) := by
    have h := gaussianReal_lower_tail_exp ha
    refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
    · simp only [standardGaussianCDF]
    · congr 1
      field_simp
      ring
  refine ⟨?_, hexp⟩
  by_cases htail : 0 < (productStandardGaussian κ).real {x | f x ≤ -t}
  · have hnonconst : ∃ x y, f x < f y := by
      by_contra hnot
      simp only [not_exists, not_lt] at hnot
      have hconst : ∀ x, f x = f 0 := fun x => le_antisymm (hnot 0 x) (hnot x 0)
      have hzero : f 0 = 0 := by
        have hfun : (fun x : κ → ℝ => Real.exp (f x)) = fun _ => Real.exp (f 0) :=
          funext fun x => by rw [hconst x]
        rw [hfun] at hmean
        exact Real.exp_injective (by simpa using hmean)
      have hempty : {x : κ → ℝ | f x ≤ -t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
        have hx : f x ≤ -t := hx
        rw [hconst x, hzero] at hx; linarith
      rw [hempty] at htail
      simp at htail
    have hrange := AlignmentPaperConvexTail.finiteProductGaussian_closedSublevel_range f hfcont
      htail (AlignmentPaperConvexTail.finiteConvex_unboundedAbove f hfconv hnonconst)
    have := AlignmentPaperConvexTail.convex_exp_lower_tail_of_closed_sublevel_range
      (productStandardGaussian κ) f hfconv finiteProductGaussianEhrhard_certified ht hrange hY
      hYmeas hmean hσ hσ₄ hvar
    rwa [neg_mul, neg_div] at this
  · refine le_trans (le_of_eq ?_) (show 0 ≤ standardGaussianCDF _ from measureReal_nonneg)
    exact le_antisymm (le_of_not_gt htail) measureReal_nonneg

end BrownianSharp.AlignmentPaperSection2Lemmas
