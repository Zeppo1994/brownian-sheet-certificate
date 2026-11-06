import BrownianSharp.SmoothPeriodicConditional
import BrownianSharp.CameronMartin
import BrownianSharp.NativeProjection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import BrownianSharp.GaussianGridStatistics
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Actual finite product-Gaussian coefficient cutoffs for the smooth
periodic atoms. The expectations are computed from Gaussian laws; all
class-facing assumptions are kept as explicit deterministic atom-norm data. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace BrownianSharp

/-- The absolute `p`th moment of one standard Gaussian coefficient. -/
def gaussianAbsoluteMoment (p : ℝ) : ℝ :=
  ∫ t : ℝ, |t| ^ p ∂gaussianReal 0 1

theorem gaussianAbsoluteMoment_integrable {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ => |t| ^ p) (gaussianReal 0 1) := by
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hq0 : q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hqtop : q ≠ ∞ := by simp [q]
  have hmem : MemLp (id : ℝ → ℝ) q (gaussianReal 0 1) :=
    memLp_id_gaussianReal' q hqtop
  have hint := hmem.integrable_norm_rpow hq0 hqtop
  simpa [q, Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using hint

theorem gaussianAbsoluteMoment_nonneg (p : ℝ) : 0 ≤ gaussianAbsoluteMoment p := by
  unfold gaussianAbsoluteMoment
  exact integral_nonneg (fun t => by positivity)

/-- Markov's inequality for a nonnegative integrable observable. A positive
upper bound `M` on its expectation gives at least half the probability to the
sublevel set at `2M`. -/
theorem gaussian_nonneg_energy_cutoff_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → ℝ) (hEmeas : Measurable E) (hEint : Integrable E μ)
    (hEpos : ∀ ω, 0 ≤ E ω) {M : ℝ} (hM : 0 < M)
    (hmean : ∫ ω, E ω ∂μ ≤ M) :
    (1 / 2 : ℝ≥0∞) ≤ μ {ω | E ω ≤ 2 * M} := by
  let bad : Set Ω := {ω | 2 * M < E ω}
  let scaled : Ω → ℝ := fun ω => E ω / (2 * M)
  have hscaledInt : Integrable scaled μ := by
    simpa [scaled, div_eq_mul_inv, mul_comm] using hEint.const_mul (2 * M)⁻¹
  have hscaledNonneg : 0 ≤ᵐ[μ] scaled := by
    filter_upwards with ω
    exact div_nonneg (hEpos ω) (le_of_lt (by positivity : 0 < 2 * M))
  have hmarkov := hscaledInt.measure_le_integral hscaledNonneg
    (s := bad) (by
      intro ω hω
      change 2 * M < E ω at hω
      dsimp [scaled]
      rw [one_le_div (by positivity : 0 < 2 * M)]
      linarith)
  have hscaledMean : ∫ ω, scaled ω ∂μ ≤ 1 / 2 := by
    dsimp [scaled]
    rw [show (fun ω => E ω / (2 * M)) = fun ω => (2 * M)⁻¹ * E ω by
      funext ω
      ring, integral_const_mul]
    have hmul := mul_le_mul_of_nonneg_left hmean
      (inv_nonneg.mpr (le_of_lt (by positivity : 0 < 2 * M)))
    calc
      (2 * M)⁻¹ * ∫ ω, E ω ∂μ ≤ (2 * M)⁻¹ * M := hmul
      _ = 1 / 2 := by field_simp
  have hbad : μ bad ≤ (1 / 2 : ℝ≥0∞) := by
    calc
      μ bad ≤ ENNReal.ofReal (∫ ω, scaled ω ∂μ) := hmarkov
      _ ≤ (1 / 2 : ℝ≥0∞) := by
        have hcast : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num
        rw [← hcast]
        exact ENNReal.ofReal_le_ofReal hscaledMean
  have hbadMeas : MeasurableSet bad := by
    apply measurableSet_lt measurable_const hEmeas
  have hgood : {ω | E ω ≤ 2 * M} = badᶜ := by
    ext ω
    simp [bad]
  have hbad_ne : μ bad ≠ ∞ := ne_of_lt (lt_of_le_of_lt hbad (by norm_num))
  have hbad_le_one : μ bad ≤ 1 := hbad.trans (by norm_num)
  rw [hgood, measure_compl hbadMeas hbad_ne, measure_univ]
  apply (ENNReal.le_sub_iff_add_le_right hbad_ne hbad_le_one).2
  calc
    (1 / 2 : ℝ≥0∞) + μ bad ≤ (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) :=
      add_le_add_right hbad (1 / 2 : ℝ≥0∞)
    _ = 1 := ENNReal.add_halves 1

/-- Address tuples within one fixed tensor shape. -/
abbrev SmoothShapeCells {d n : ℕ} (r : Shape d n) :=
  ∀ i : Fin d, Fin (2 ^ r.1 i)

/-- The sum of absolute `p`th powers of the actual Gaussian coefficients in
one fixed tensor shape. -/
def smoothShapeCoefficientEnergy {d n : ℕ} (r : Shape d n) (p : ℝ)
    (x : LayerIndex d n → ℝ) : ℝ :=
  ∑ j : SmoothShapeCells r, |x (⟨r, j⟩ : LayerIndex d n)| ^ p

theorem smoothShapeCoefficientEnergy_nonneg {d n : ℕ} (r : Shape d n)
    (p : ℝ) (x : LayerIndex d n → ℝ) :
    0 ≤ smoothShapeCoefficientEnergy r p x := by
  unfold smoothShapeCoefficientEnergy
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem smoothShapeCoefficientEnergy_integrable {d n : ℕ} (r : Shape d n)
    {p : ℝ} (hp : 0 < p) :
    Integrable (smoothShapeCoefficientEnergy r p)
      (productStandardGaussian (LayerIndex d n)) := by
  unfold smoothShapeCoefficientEnergy
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact integrable_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
    (i := (⟨r, j⟩ : LayerIndex d n)) (gaussianAbsoluteMoment_integrable hp)

theorem smoothShapeCoefficientEnergy_mean {d n : ℕ} (r : Shape d n)
    {p : ℝ} (hp : 0 < p) :
    (∫ x : LayerIndex d n → ℝ, smoothShapeCoefficientEnergy r p x
        ∂productStandardGaussian (LayerIndex d n)) =
      (Fintype.card (SmoothShapeCells r) : ℝ) * gaussianAbsoluteMoment p := by
  unfold smoothShapeCoefficientEnergy productStandardGaussian
  have hp0 : 0 ≤ p := le_of_lt hp
  have hcont : Continuous (fun t : ℝ => |t| ^ p) := by fun_prop
  rw [integral_finsetSum Finset.univ (fun j hj => by
    exact integrable_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
      (i := (⟨r, j⟩ : LayerIndex d n)) (gaussianAbsoluteMoment_integrable hp))]
  calc
    (∑ j : SmoothShapeCells r,
        ∫ x : LayerIndex d n → ℝ, |x (⟨r, j⟩ : LayerIndex d n)| ^ p
          ∂(Measure.pi fun _ : LayerIndex d n => gaussianReal 0 1))
        = ∑ _j : SmoothShapeCells r, gaussianAbsoluteMoment p := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
        (i := (⟨r, j⟩ : LayerIndex d n)) (f := fun t => |t| ^ p)
        hcont.aestronglyMeasurable
    _ = (Fintype.card (SmoothShapeCells r) : ℝ) * gaussianAbsoluteMoment p := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Every individual shape cutoff retains at least half the actual
product-Gaussian mass. -/
theorem smoothShapeCoefficientCutoff_mass {d n : ℕ} (r : Shape d n)
    {p : ℝ} (hp : 0 < p) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (LayerIndex d n))
        {x | smoothShapeCoefficientEnergy r p x ≤
          2 * (Fintype.card (SmoothShapeCells r) : ℝ) *
            (1 + gaussianAbsoluteMoment p)} := by
  have hmean := smoothShapeCoefficientEnergy_mean r hp
  have hcard : 0 < (Fintype.card (SmoothShapeCells r) : ℝ) := by
    have hn : Nonempty (SmoothShapeCells r) := ⟨fun i => ⟨0, by positivity⟩⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr hn)
  have hmoment : 0 ≤ gaussianAbsoluteMoment p := gaussianAbsoluteMoment_nonneg p
  have hM : 0 < (Fintype.card (SmoothShapeCells r) : ℝ) *
      (1 + gaussianAbsoluteMoment p) := by positivity
  have hmean_le :
      ∫ x : LayerIndex d n → ℝ, smoothShapeCoefficientEnergy r p x
        ∂productStandardGaussian (LayerIndex d n) ≤
        (Fintype.card (SmoothShapeCells r) : ℝ) *
          (1 + gaussianAbsoluteMoment p) := by
    rw [hmean]
    exact mul_le_mul_of_nonneg_left (by linarith) hcard.le
  have hmass := gaussian_nonneg_energy_cutoff_mass
    (productStandardGaussian (LayerIndex d n)) (smoothShapeCoefficientEnergy r p)
    (by fun_prop [smoothShapeCoefficientEnergy])
    (smoothShapeCoefficientEnergy_integrable r hp)
    (smoothShapeCoefficientEnergy_nonneg r p) hM hmean_le
  simpa [mul_assoc] using hmass

/-- A positive deterministic expectation budget for one tensor shape. -/
def smoothShapeCoefficientBudget {d n : ℕ} (p : ℝ) (r : Shape d n) : ℝ :=
  (Fintype.card (SmoothShapeCells r) : ℝ) * (1 + gaussianAbsoluteMoment p)

theorem smoothShapeCoefficientEnergy_measurable {d n : ℕ} (r : Shape d n)
    {p : ℝ} (hp : 0 < p) :
    Measurable (smoothShapeCoefficientEnergy r p) := by
  unfold smoothShapeCoefficientEnergy
  have hp0 : 0 ≤ p := le_of_lt hp
  fun_prop

/-- Coordinate extension by zero from a finite coordinate block. -/
noncomputable def smoothCoefficientBlockExtend {κ : Type*} [Fintype κ] (S : Finset κ)
    (y : {a // a ∈ S} → ℝ) : κ → ℝ := by
  classical
  exact fun a => if h : a ∈ S then y ⟨a, h⟩ else 0

theorem smoothCoefficientBlockExtend_measurable {κ : Type*} [Fintype κ]
    (S : Finset κ) : Measurable (smoothCoefficientBlockExtend S) := by
  apply measurable_pi_iff.2
  intro a
  by_cases ha : a ∈ S
  · simpa [smoothCoefficientBlockExtend, ha] using
      (measurable_pi_apply (⟨a, ha⟩ : {a // a ∈ S}))
  · simp [smoothCoefficientBlockExtend, ha]

theorem smoothCoefficientBlockExtend_restrict {κ : Type*} [Fintype κ]
    (S : Finset κ) (x : κ → ℝ) (a : κ) (ha : a ∈ S) :
    smoothCoefficientBlockExtend S (fun i : {a // a ∈ S} => x i.1) a = x a := by
  classical
  simp [smoothCoefficientBlockExtend, ha]

/-- The coordinates belonging to one fixed tensor shape. -/
def smoothShapeBlock {d n : ℕ} (r : Shape d n) : Finset (LayerIndex d n) :=
  Finset.univ.filter fun a => a.1 = r

/-- The union of the coefficient blocks indexed by a finite set of shapes. -/
def smoothShapeBlocks {d n : ℕ} (S : Finset (Shape d n)) : Finset (LayerIndex d n) :=
  Finset.univ.filter fun a => a.1 ∈ S

theorem smoothShapeBlock_disjoint_blocks {d n : ℕ} (r : Shape d n)
    (S : Finset (Shape d n)) (hr : r ∉ S) :
    Disjoint (smoothShapeBlock r) (smoothShapeBlocks S) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have ha' : a.1 = r := (Finset.mem_filter.mp ha).2
  have hb' : a.1 ∈ S := (Finset.mem_filter.mp hb).2
  exact hr (ha' ▸ hb')

theorem smoothShapeBlock_subset_blocks {d n : ℕ} (r : Shape d n)
    (S : Finset (Shape d n)) (hr : r ∈ S) :
    smoothShapeBlock r ⊆ smoothShapeBlocks S := by
  intro a ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (Finset.mem_filter.mp ha).2 ▸ hr

theorem smoothShapeCoefficientEnergy_blockExtend {d n : ℕ} (r : Shape d n)
    (S : Finset (LayerIndex d n)) (hS : smoothShapeBlock r ⊆ S)
    {p : ℝ} (x : LayerIndex d n → ℝ) :
    smoothShapeCoefficientEnergy r p (smoothCoefficientBlockExtend S
      (fun i : {a // a ∈ S} => x i.1)) = smoothShapeCoefficientEnergy r p x := by
  unfold smoothShapeCoefficientEnergy
  apply Finset.sum_congr rfl
  intro j hj
  have haddr : (⟨r, j⟩ : LayerIndex d n) ∈ smoothShapeBlock r := by
    apply Finset.mem_filter.mpr
    simp
  have hmem := hS haddr
  rw [smoothCoefficientBlockExtend_restrict S x ⟨r, j⟩ hmem]

/-- The shape-wise coefficient event. -/
def smoothShapeGoodEvent {d n : ℕ} (p : ℝ) (r : Shape d n) :
    Set (LayerIndex d n → ℝ) :=
  {x | smoothShapeCoefficientEnergy r p x ≤ 2 * smoothShapeCoefficientBudget p r}

/-- Simultaneous coefficient events over an arbitrary finite set of shapes. -/
def smoothShapeJointGoodEvent {d n : ℕ} (p : ℝ) (S : Finset (Shape d n)) :
    Set (LayerIndex d n → ℝ) :=
  {x | ∀ r ∈ S,
    smoothShapeCoefficientEnergy r p x ≤ 2 * smoothShapeCoefficientBudget p r}

theorem smoothShapeJointGoodEvent_block_factor {d n : ℕ} (p : ℝ)
    (r : Shape d n) (S : Finset (Shape d n)) (hr : r ∉ S)
    {hp : 0 < p} :
    (productStandardGaussian (LayerIndex d n))
        (smoothShapeGoodEvent p r ∩ smoothShapeJointGoodEvent p S) =
      (productStandardGaussian (LayerIndex d n)) (smoothShapeGoodEvent p r) *
        (productStandardGaussian (LayerIndex d n)) (smoothShapeJointGoodEvent p S) := by
  classical
  let U := smoothShapeBlock r
  let V := smoothShapeBlocks S
  let f : (LayerIndex d n → ℝ) → (∀ a : {a // a ∈ U}, ℝ) := fun x i => x i.1
  let g : (LayerIndex d n → ℝ) → (∀ a : {a // a ∈ V}, ℝ) := fun x i => x i.1
  have hdisj : Disjoint U V := by
    exact smoothShapeBlock_disjoint_blocks r S hr
  have hcoords := productStandardGaussian_coordinates_independent (LayerIndex d n)
  have hindep : IndepFun f g (productStandardGaussian (LayerIndex d n)) := by
    exact hcoords.indepFun_finset U V hdisj (fun a => measurable_pi_apply a)
  let A : Set (∀ a : {a // a ∈ U}, ℝ) :=
    {y | smoothShapeCoefficientEnergy r p (smoothCoefficientBlockExtend U y) ≤
      2 * smoothShapeCoefficientBudget p r}
  let B : Set (∀ a : {a // a ∈ V}, ℝ) :=
    {z | ∀ s ∈ S,
      smoothShapeCoefficientEnergy s p (smoothCoefficientBlockExtend V z) ≤
        2 * smoothShapeCoefficientBudget p s}
  have hA : MeasurableSet A := by
    apply measurableSet_le
      ((smoothShapeCoefficientEnergy_measurable r hp).comp
        (smoothCoefficientBlockExtend_measurable U)) measurable_const
  have hB : MeasurableSet B := by
    rw [show B = ⋂ s ∈ S,
      {z | smoothShapeCoefficientEnergy s p (smoothCoefficientBlockExtend V z) ≤
        2 * smoothShapeCoefficientBudget p s} by
      ext z
      simp [B]]
    exact Finset.measurableSet_biInter S fun s hs =>
      measurableSet_le
        ((smoothShapeCoefficientEnergy_measurable s hp).comp
          (smoothCoefficientBlockExtend_measurable V)) measurable_const
  have hApre : f ⁻¹' A = smoothShapeGoodEvent p r := by
    ext x
    change smoothShapeCoefficientEnergy r p
        (smoothCoefficientBlockExtend U (fun i => x i.1)) ≤
          2 * smoothShapeCoefficientBudget p r ↔
        smoothShapeCoefficientEnergy r p x ≤ 2 * smoothShapeCoefficientBudget p r
    rw [smoothShapeCoefficientEnergy_blockExtend r U (by intro a ha; exact ha) x]
  have hBpre : g ⁻¹' B = smoothShapeJointGoodEvent p S := by
    ext x
    change (∀ s ∈ S,
        smoothShapeCoefficientEnergy s p
          (smoothCoefficientBlockExtend V (fun i => x i.1)) ≤
            2 * smoothShapeCoefficientBudget p s) ↔
      (∀ s ∈ S, smoothShapeCoefficientEnergy s p x ≤
        2 * smoothShapeCoefficientBudget p s)
    constructor
    · intro h s hs
      have hsub : smoothShapeBlock s ⊆ V :=
        smoothShapeBlock_subset_blocks s S hs
      rw [← smoothShapeCoefficientEnergy_blockExtend s V hsub x]
      exact h s hs
    · intro h s hs
      have hsub : smoothShapeBlock s ⊆ V :=
        smoothShapeBlock_subset_blocks s S hs
      rw [smoothShapeCoefficientEnergy_blockExtend s V hsub x]
      exact h s hs
  have hfactor := hindep.measure_inter_preimage_eq_mul A B hA hB
  rw [hApre, hBpre] at hfactor
  simpa [Set.inter_comm] using hfactor

/-- For every finite set of shapes, the good coefficient event has exactly
the product of the individual shape probabilities. This is actual block
independence of disjoint Gaussian coordinates, not pairwise independence. -/
theorem smoothShapeJointGoodEvent_measure_eq_prod {d n : ℕ} (p : ℝ)
    (S : Finset (Shape d n)) {hp : 0 < p} :
    (productStandardGaussian (LayerIndex d n)) (smoothShapeJointGoodEvent p S) =
      ∏ r ∈ S, (productStandardGaussian (LayerIndex d n)) (smoothShapeGoodEvent p r) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [smoothShapeJointGoodEvent]
  | @insert r S hr ih =>
      rw [show smoothShapeJointGoodEvent p (insert r S) =
        smoothShapeGoodEvent p r ∩ smoothShapeJointGoodEvent p S by
          ext x
          change (∀ q ∈ insert r S,
            smoothShapeCoefficientEnergy q p x ≤
              2 * smoothShapeCoefficientBudget p q) ↔
            (smoothShapeCoefficientEnergy r p x ≤
              2 * smoothShapeCoefficientBudget p r) ∧
            (∀ q ∈ S, smoothShapeCoefficientEnergy q p x ≤
              2 * smoothShapeCoefficientBudget p q)
          constructor
          · intro h
            exact ⟨h r (Finset.mem_insert_self r S), fun q hq =>
              h q (Finset.mem_insert_of_mem hq)⟩
          · rintro ⟨hrgood, hs⟩ q hq
            rcases Finset.mem_insert.mp hq with hqr | hqS
            · subst q
              exact hrgood
            · exact hs q hqS]
      rw [smoothShapeJointGoodEvent_block_factor p r S hr (hp := hp)]
      rw [ih]
      simp [hr, Finset.prod_insert, mul_comm]

/-- The independent shape cutoffs have the manuscript's product lower bound. -/
theorem smoothShapeJointGoodEvent_measure_lower {d n : ℕ} (p : ℝ)
    (S : Finset (Shape d n)) {hp : 0 < p} :
    (1 / 2 : ℝ≥0∞) ^ S.card ≤
      (productStandardGaussian (LayerIndex d n)) (smoothShapeJointGoodEvent p S) := by
  rw [smoothShapeJointGoodEvent_measure_eq_prod p S (hp := hp)]
  calc
    (1 / 2 : ℝ≥0∞) ^ S.card = ∏ r ∈ S, (1 / 2 : ℝ≥0∞) := by
      simp [Finset.prod_const]
    _ ≤ ∏ r ∈ S,
        (productStandardGaussian (LayerIndex d n)) (smoothShapeGoodEvent p r) := by
      apply Finset.prod_le_prod
      intro r hr
      have hcut := smoothShapeCoefficientCutoff_mass r hp
      have hthreshold :
          2 * (Fintype.card (SmoothShapeCells r) : ℝ) *
            (1 + gaussianAbsoluteMoment p) =
          2 * smoothShapeCoefficientBudget p r := by
        simp [smoothShapeCoefficientBudget, mul_assoc]
      rw [hthreshold] at hcut
      exact hcut

/-- All shape-wise Gaussian `ℓᵖ` cutoffs hold simultaneously with mass at
least `2^{-S_n}`, where `S_n` is the number of weak-composition shapes. -/
theorem smoothAllShapesCoefficientCutoff_mass {d n : ℕ} (hd : 0 < d)
    {p : ℝ} (hp : 0 < p) :
    (1 / 2 : ℝ≥0∞) ^ Nat.choose (n + d - 1) (d - 1) ≤
      (productStandardGaussian (LayerIndex d n))
        (smoothShapeJointGoodEvent p Finset.univ) := by
  have h := smoothShapeJointGoodEvent_measure_lower p
    (Finset.univ : Finset (Shape d n)) (hp := hp)
  have hcard : (Finset.univ : Finset (Shape d n)).card =
      Nat.choose (n + d - 1) (d - 1) := by
    rw [show (Finset.univ : Finset (Shape d n)).card =
      Fintype.card (Shape d n) by simp, shape_card d n hd]
  rw [hcard] at h
  exact h

end BrownianSharp
