import BrownianSharp.AlignmentPaperGenericBumpCertified
import BrownianSharp.PeriodicEntropy
import BrownianSharp.EventualRates
import BrownianSharp.LayerIndex

/-! Remark 2.2: the lower bound (2.6), `n^{(d-2)/2} ‖Σ λ_R a_R‖_∞ ≥ c 2^{-n} Σ |λ_R|`,
holds for all coefficient vectors outside a set of standard Gaussian measure
`≤ exp(-c'' |D_n|)`.  The Gaussian `ℓ¹` tail is a Chernoff bound; `‖·‖_∞ < r` is
expressed as the existence of a uniform bound `s < r` (equivalent), matching the
form of Theorem 2.1. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperDeterministicExceptionalSet
open AlignmentPaperGenericBumpCertified AlignmentPaperContinuumGenericBump
  AlignmentPaperContinuumGoodRegion

private theorem exp_abs_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (h : HasLaw X (gaussianReal 0 1) P) :
    Integrable (fun ω => Real.exp (1 * |X ω|)) P ∧
      mgf (fun ω => |X ω|) P 1 ≤ Real.exp (3 / 2) := by
  have hi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := fun t => by
    have := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
    rw [← h.map_eq] at this
    exact (integrable_map_measure this.aestronglyMeasurable h.aemeasurable).1 this
  have hle : ∀ ω, Real.exp (1 * |X ω|) ≤ Real.exp (1 * X ω) + Real.exp (-1 * X ω) := by
    intro ω
    rcases abs_cases (X ω) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
      simp [Real.exp_nonneg]
  have hI := (hi 1).add (hi (-1))
  have hm : AEStronglyMeasurable (fun ω => Real.exp (1 * |X ω|)) P :=
    (Real.measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable h.aemeasurable).const_mul 1)).aestronglyMeasurable
  have hint : Integrable (fun ω => Real.exp (1 * |X ω|)) P :=
    hI.mono' hm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact hle ω)
  refine ⟨hint, ?_⟩
  calc mgf (fun ω => |X ω|) P 1 ≤ ∫ ω, (Real.exp (1 * X ω) + Real.exp (-1 * X ω)) ∂P :=
        integral_mono hint hI hle
    _ = mgf X P 1 + mgf X P (-1) := integral_add (hi 1) (hi (-1))
    _ ≤ Real.exp (3 / 2) := by
        rw [mgf_gaussianReal h 1, mgf_gaussianReal h (-1)]
        have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
          rw [← Real.exp_add]; norm_num
        norm_num [this]
        nlinarith [Real.exp_pos (1 / 2)]

/-- Chernoff bound for the Gaussian `ℓ¹` norm: `P{Σ|G_R| ≥ 2 |D_n|} ≤ exp(-|D_n|/2)`. -/
private theorem gaussian_l1_tail {ι : Type*} [Fintype ι] :
    (productStandardGaussian ι).real {z | 2 * (Fintype.card ι : ℝ) ≤ ∑ i, |z i|} ≤
      Real.exp (-(Fintype.card ι : ℝ) / 2) := by
  set μ := productStandardGaussian ι
  have hX : ∀ i : ι, HasLaw (fun z : ι → ℝ => z i) (gaussianReal 0 1) μ := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, productStandardGaussian_coordinate_law i⟩
  have hInd : iIndepFun (fun i : ι => fun z : ι → ℝ => |z i|) μ :=
    (productStandardGaussian_coordinates_independent ι).comp (fun _ => abs) (fun _ => continuous_abs.measurable)
  have hmeas : ∀ i : ι, Measurable (fun z : ι → ℝ => |z i|) := fun i =>
    continuous_abs.measurable.comp (measurable_pi_apply i)
  have hint := hInd.integrable_exp_mul_sum (t := 1) hmeas (s := Finset.univ)
    (fun i _ => (exp_abs_gauss (hX i)).1)
  have hsum : (∑ i : ι, fun z : ι → ℝ => |z i|) = fun z => ∑ i, |z i| := by
    ext z; simp
  have hmgf : mgf (fun z : ι → ℝ => ∑ i, |z i|) μ 1 ≤ Real.exp (3 / 2) ^ Fintype.card ι := by
    rw [← hsum, hInd.mgf_sum hmeas]
    calc ∏ i : ι, mgf (fun z : ι → ℝ => |z i|) μ 1 ≤ ∏ _i : ι, Real.exp (3 / 2) := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
          · exact mgf_nonneg
          · exact (exp_abs_gauss (hX i)).2
      _ = _ := by simp
  rw [hsum] at hint
  refine (measure_ge_le_exp_mul_mgf (2 * (Fintype.card ι : ℝ)) zero_le_one hint).trans ?_
  calc _ ≤ Real.exp (-1 * (2 * (Fintype.card ι : ℝ))) * Real.exp (3 / 2) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

private theorem key_ineq {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    2 * (a / (2 * ((d : ℝ) + 1) ^ (((d : ℝ) - 1) / 2))) * hyperbolicCount d n ≤
      (n : ℝ) ^ (((d : ℝ) - 2) / 2) * (a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hS := hyperbolicCount_pos (d := d) (n := n) (by omega)
  set p : ℝ := ((d : ℝ) - 1) / 2
  set S := hyperbolicCount d n
  have hx : (0 : ℝ) ≤ ((d : ℝ) + 1) * n := by positivity
  have hsq : Real.sqrt S ≤ ((d : ℝ) + 1) ^ p * (n : ℝ) ^ p := by
    have h := hyperbolicCount_upper hd hn
    have h2 : (((d + 1 : ℕ) : ℝ) * (n : ℝ)) ^ (d - 1) = ((((d : ℝ) + 1) * n) ^ p) ^ 2 := by
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2] at h
    calc Real.sqrt S ≤ Real.sqrt (((((d : ℝ) + 1) * n) ^ p) ^ 2) := Real.sqrt_le_sqrt h
      _ = _ := by rw [Real.sqrt_sq (by positivity), Real.mul_rpow (by positivity) hnr.le]
  have hq : (n : ℝ) ^ (((d : ℝ) - 2) / 2) * Real.sqrt n = (n : ℝ) ^ p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnr]; congr 1; ring
  have hdp : (0 : ℝ) < ((d : ℝ) + 1) ^ p := by positivity
  calc 2 * (a / (2 * ((d : ℝ) + 1) ^ p)) * S
      = (a / ((d : ℝ) + 1) ^ p) * (Real.sqrt S * Real.sqrt S) := by
        rw [Real.mul_self_sqrt hS.le]; field_simp
    _ ≤ (a / ((d : ℝ) + 1) ^ p) * (((d : ℝ) + 1) ^ p * (n : ℝ) ^ p * Real.sqrt S) := by
        gcongr
    _ = _ := by
        rw [Real.sqrt_mul hnr.le, ← hq]; field_simp

/-- Remark 2.2, consequence (2.7): for every admissible bump `ψ` there are constants
`c, c'' > 0` such that, for large `n`, the lower bound (2.6) holds for all coefficient
vectors outside a set of Gaussian measure `≤ exp(-c'' |D_n|)`.  The failure of (2.6)
for `λ = G(ω)` is written as: some uniform bound `s` on `|Σ_R G_R a_R|` over the cube
satisfies `n^{(d-2)/2} s < c 2^{-n} Σ_R |G_R|`. -/
theorem deterministic_exceptional_set_small.{u} {d : ℕ} (hd : 2 ≤ d) (ψ : AdmissibleBump) :
    ∃ c c'' : ℝ, 0 < c ∧ 0 < c'' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : LayerIndex d n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∃ s : ℝ, (∀ x ∈ cubeSet d, |bumpSynthesis ψ (fun i => G i ω) x| ≤ s) ∧
          (n : ℝ) ^ (((d : ℝ) - 2) / 2) * s < c / 2 ^ n * ∑ i, |G i ω|} ≤
          Real.exp (-c'' * nativeDimension d n) := by
  obtain ⟨a, b, ha, hb, N0, hN0⟩ := admissibleBumpIidConfinement_certified.{u} d hd ψ
  set c : ℝ := a / (2 * ((d : ℝ) + 1) ^ (((d : ℝ) - 1) / 2)) with hc
  have hcpos : 0 < c := by positivity
  set m : ℝ := min (1 / 2) b
  have hm : 0 < m := lt_min (by norm_num) hb
  obtain ⟨N1, hN1⟩ := pow_unbounded_of_one_lt (2 / m) (one_lt_two (α := ℝ))
  refine ⟨c, m / 2, hcpos, half_pos hm, max (max N0 N1) 1, ?_⟩
  intro n hn Ω _ P _ G hG hInd
  have hn0 : N0 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N1 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnpos : 0 < n := (le_max_right _ _).trans hn
  set D := nativeDimension d n
  have hcard : (Fintype.card (LayerIndex d n) : ℝ) = D := by
    rw [layerIndex_card d n (by omega)]; simp [D, nativeDimension, hyperbolicCount]
  have hD : (2 : ℝ) ^ n ≤ D := nativeDimension_ge_dyadic d n (by omega)
  have hLaw : HasLaw (fun ω i => G i ω) (productStandardGaussian (LayerIndex d n)) P :=
    hInd.hasLaw_pi hG
  have hT : P.real {ω | 2 * D ≤ ∑ i, |G i ω|} ≤ Real.exp (-D / 2) := by
    rw [← hcard]
    have hms : MeasurableSet {z : LayerIndex d n → ℝ |
        2 * (Fintype.card (LayerIndex d n) : ℝ) ≤ ∑ i, |z i|} :=
      measurableSet_le measurable_const (by fun_prop)
    exact (hLaw.measureReal_eq hms).le.trans gaussian_l1_tail
  have hsub : {ω | ∃ s : ℝ, (∀ x ∈ cubeSet d, |bumpSynthesis ψ (fun i => G i ω) x| ≤ s) ∧
        (n : ℝ) ^ (((d : ℝ) - 2) / 2) * s < c / 2 ^ n * ∑ i, |G i ω|} ⊆
      {ω | 2 * D ≤ ∑ i, |G i ω|} ∪ {ω | ∀ x ∈ cubeSet d,
        |bumpSynthesis ψ (fun i => G i ω) x| ≤ a * Real.sqrt ((n : ℝ) * hyperbolicCount d n)} := by
    rintro ω ⟨s, hs, hlt⟩
    by_cases h2 : 2 * D ≤ ∑ i, |G i ω|
    · exact Or.inl h2
    refine Or.inr fun x hx => (hs x hx).trans ?_
    replace h2 := not_le.mp h2
    have hq : (0 : ℝ) < (n : ℝ) ^ (((d : ℝ) - 2) / 2) := by
      have : (0 : ℝ) < n := by exact_mod_cast hnpos
      positivity
    refine le_of_lt (lt_of_mul_lt_mul_left ?_ hq.le)
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    calc (n : ℝ) ^ (((d : ℝ) - 2) / 2) * s < c / 2 ^ n * ∑ i, |G i ω| := hlt
      _ ≤ c / 2 ^ n * (2 * (2 ^ n * hyperbolicCount d n)) := by
          gcongr; simpa [D, nativeDimension] using h2.le
      _ = 2 * c * hyperbolicCount d n := by field_simp
      _ ≤ _ := key_ineq hd hnpos ha
  have hC := hN0 n hn0 Ω P G hG hInd
  have hmD : 2 ≤ m * D := by
    have : 2 / m ≤ D := ((hN1.le.trans (pow_le_pow_right₀ one_le_two hn1)).trans hD)
    rwa [div_le_iff₀ hm, mul_comm] at this
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have e1 : Real.exp (-D / 2) ≤ Real.exp (-m * D) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left (1 / 2 : ℝ) b])
  have e2 : Real.exp (-b * D) ≤ Real.exp (-m * D) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right (1 / 2 : ℝ) b])
  have e3 : 2 * Real.exp (-m * D) ≤ Real.exp (-(m / 2) * D) := by
    have : Real.exp (-(m / 2) * D) = Real.exp (-m * D) * Real.exp (m * D / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    have : (2 : ℝ) ≤ Real.exp (m * D / 2) := by
      linarith [Real.add_one_le_exp (m * D / 2)]
    nlinarith [Real.exp_pos (-m * D)]
  calc _ ≤ P.real ({ω | 2 * D ≤ ∑ i, |G i ω|} ∪ _) := measureReal_mono hsub
    _ ≤ P.real {ω | 2 * D ≤ ∑ i, |G i ω|} + _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end BrownianSharp.AlignmentPaperDeterministicExceptionalSet
