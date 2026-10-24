import BrownianSharp.SmoothPeriodicConditional
import BrownianSharp.CameronMartinEntropy
import BrownianSharp.GaussianGridStatistics
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

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

/-- Shape-wise coefficient cutoff event. -/
def smoothShapeCoefficientCutoff {d n : ℕ} (p : ℝ)
    (x : LayerIndex d n → ℝ) : Prop :=
  ∀ r : Shape d n,
    smoothShapeCoefficientEnergy r p x ≤
      2 * (Fintype.card (SmoothShapeCells r) : ℝ) *
        (1 + gaussianAbsoluteMoment p)

/-- A positive deterministic expectation budget for one tensor shape. -/
def smoothShapeCoefficientBudget {d n : ℕ} (p : ℝ) (r : Shape d n) : ℝ :=
  (Fintype.card (SmoothShapeCells r) : ℝ) * (1 + gaussianAbsoluteMoment p)

/-- The normalized sum of all shape energies. -/
def smoothAllShapeCoefficientEnergy {d n : ℕ} (p : ℝ)
    (x : LayerIndex d n → ℝ) : ℝ :=
  ∑ r : Shape d n,
    smoothShapeCoefficientEnergy r p x / smoothShapeCoefficientBudget p r

theorem smoothShapeCoefficientBudget_pos {d n : ℕ} (r : Shape d n)
    (p : ℝ) : 0 < smoothShapeCoefficientBudget p r := by
  unfold smoothShapeCoefficientBudget
  have hcard : 0 < (Fintype.card (SmoothShapeCells r) : ℝ) := by
    have hn : Nonempty (SmoothShapeCells r) := ⟨fun i => ⟨0, by positivity⟩⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr hn)
  have hmoment := gaussianAbsoluteMoment_nonneg p
  positivity

theorem smoothAllShapeCoefficientEnergy_nonneg {d n : ℕ} (p : ℝ)
    (x : LayerIndex d n → ℝ) : 0 ≤ smoothAllShapeCoefficientEnergy p x := by
  unfold smoothAllShapeCoefficientEnergy
  apply Finset.sum_nonneg
  intro r hr
  apply div_nonneg (smoothShapeCoefficientEnergy_nonneg r p x)
  exact (smoothShapeCoefficientBudget_pos r p).le

theorem smoothAllShapeCoefficientEnergy_integrable {d n : ℕ} {p : ℝ}
    (hp : 0 < p) :
    Integrable (smoothAllShapeCoefficientEnergy p)
      (productStandardGaussian (LayerIndex d n)) := by
  unfold smoothAllShapeCoefficientEnergy
  apply integrable_finsetSum Finset.univ
  intro r hr
  exact (smoothShapeCoefficientEnergy_integrable r hp).div_const
    (smoothShapeCoefficientBudget p r)

theorem smoothShapeCoefficientEnergy_measurable {d n : ℕ} (r : Shape d n)
    {p : ℝ} (hp : 0 < p) :
    Measurable (smoothShapeCoefficientEnergy r p) := by
  unfold smoothShapeCoefficientEnergy
  have hp0 : 0 ≤ p := le_of_lt hp
  fun_prop

theorem smoothAllShapeCoefficientEnergy_measurable {d n : ℕ} {p : ℝ}
    (hp : 0 < p) :
    Measurable (smoothAllShapeCoefficientEnergy (d := d) (n := n) p) := by
  unfold smoothAllShapeCoefficientEnergy
  apply Finset.measurable_sum
  intro r hr
  exact (smoothShapeCoefficientEnergy_measurable r hp).div_const
    (smoothShapeCoefficientBudget p r)

theorem smoothAllShapeCoefficientEnergy_mean_le_shapeCount {d n : ℕ}
    {p : ℝ} (hp : 0 < p) :
    (∫ x : LayerIndex d n → ℝ, smoothAllShapeCoefficientEnergy p x
      ∂productStandardGaussian (LayerIndex d n)) ≤ Fintype.card (Shape d n) := by
  unfold smoothAllShapeCoefficientEnergy
  rw [integral_finsetSum Finset.univ (fun r hr => by
    exact (smoothShapeCoefficientEnergy_integrable r hp).div_const
      (smoothShapeCoefficientBudget p r))]
  have hbudget (r : Shape d n) : 0 < smoothShapeCoefficientBudget p r :=
    smoothShapeCoefficientBudget_pos r p
  have hterm (r : Shape d n) :
      (∫ x : LayerIndex d n → ℝ, smoothShapeCoefficientEnergy r p x
          / smoothShapeCoefficientBudget p r
          ∂productStandardGaussian (LayerIndex d n)) ≤ 1 := by
    rw [show (fun x : LayerIndex d n → ℝ =>
          smoothShapeCoefficientEnergy r p x / smoothShapeCoefficientBudget p r) =
        fun x => (smoothShapeCoefficientBudget p r)⁻¹ *
          smoothShapeCoefficientEnergy r p x by funext x; ring,
      integral_const_mul, smoothShapeCoefficientEnergy_mean r hp]
    have hcard : 0 < (Fintype.card (SmoothShapeCells r) : ℝ) := by
      have hn : Nonempty (SmoothShapeCells r) := ⟨fun i => ⟨0, by positivity⟩⟩
      exact_mod_cast (Fintype.card_pos_iff.mpr hn)
    have hmoment := gaussianAbsoluteMoment_nonneg p
    unfold smoothShapeCoefficientBudget
    calc
      (smoothShapeCoefficientBudget p r)⁻¹ *
          ((Fintype.card (SmoothShapeCells r) : ℝ) * gaussianAbsoluteMoment p) =
          ((Fintype.card (SmoothShapeCells r) : ℝ) * gaussianAbsoluteMoment p) /
            smoothShapeCoefficientBudget p r := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 := (div_le_one (hbudget r)).2 (by
        unfold smoothShapeCoefficientBudget
        have := gaussianAbsoluteMoment_nonneg p
        nlinarith)
  calc
    (∑ r : Shape d n,
        ∫ x : LayerIndex d n → ℝ, smoothShapeCoefficientEnergy r p x /
          smoothShapeCoefficientBudget p r
          ∂productStandardGaussian (LayerIndex d n)) ≤
      ∑ _r : Shape d n, (1 : ℝ) := Finset.sum_le_sum fun r hr => hterm r
    _ = (Fintype.card (Shape d n) : ℝ) := by simp

/-- A simultaneous cutoff for all tensor shapes, obtained by one global
Markov estimate. Each shape threshold carries the explicit shape-count loss;
the sharper product bound needs a separate block-independence argument. -/
theorem smoothAllShapeCoefficientCutoff_mass {d n : ℕ} {p : ℝ}
    (hd : 0 < d) (hp : 0 < p) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (LayerIndex d n))
        {x | ∀ r : Shape d n,
          smoothShapeCoefficientEnergy r p x ≤
            2 * (Fintype.card (Shape d n) : ℝ) *
              smoothShapeCoefficientBudget p r} := by
  have hshapepos : 0 < (Fintype.card (Shape d n) : ℝ) := by
    rw [shape_card d n hd]
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hmass := gaussian_nonneg_energy_cutoff_mass
    (productStandardGaussian (LayerIndex d n)) (smoothAllShapeCoefficientEnergy p)
    (smoothAllShapeCoefficientEnergy_measurable hp)
    (smoothAllShapeCoefficientEnergy_integrable hp)
    (smoothAllShapeCoefficientEnergy_nonneg p) hshapepos
    (smoothAllShapeCoefficientEnergy_mean_le_shapeCount hp)
  have hsubset :
      {x : LayerIndex d n → ℝ |
        smoothAllShapeCoefficientEnergy p x ≤ 2 * (Fintype.card (Shape d n) : ℝ)} ⊆
      {x | ∀ r : Shape d n,
        smoothShapeCoefficientEnergy r p x ≤
          2 * (Fintype.card (Shape d n) : ℝ) *
            smoothShapeCoefficientBudget p r} := by
    intro x hx r
    have hterm :
        smoothShapeCoefficientEnergy r p x /
          smoothShapeCoefficientBudget p r ≤
        smoothAllShapeCoefficientEnergy p x := by
      unfold smoothAllShapeCoefficientEnergy
      exact Finset.single_le_sum (fun s hs => div_nonneg
        (smoothShapeCoefficientEnergy_nonneg s p x)
        (smoothShapeCoefficientBudget_pos s p).le) (Finset.mem_univ r)
    have hb := smoothShapeCoefficientBudget_pos r p
    have hnonneg := smoothShapeCoefficientEnergy_nonneg r p x
    have := (div_le_iff₀ hb).1 (hterm.trans hx)
    nlinarith
  exact hmass.trans (measure_mono hsubset)

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

theorem smoothShapeGoodEvent_measurable {d n : ℕ} (p : ℝ) (r : Shape d n)
    {hp : 0 < p} : MeasurableSet (smoothShapeGoodEvent p r) := by
  exact measurableSet_le (smoothShapeCoefficientEnergy_measurable r hp) measurable_const

theorem smoothShapeJointGoodEvent_measurable {d n : ℕ} (p : ℝ)
    (S : Finset (Shape d n)) {hp : 0 < p} :
    MeasurableSet (smoothShapeJointGoodEvent p S) := by
  rw [smoothShapeJointGoodEvent]
  simp only [Set.setOf_forall]
  exact Finset.measurableSet_biInter S fun r hr =>
    smoothShapeGoodEvent_measurable (p := p) (r := r) (hp := hp)

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

/-- A deterministic weighted quadratic Sobolev energy of the actual Gaussian
coefficients. The weights are supplied by the concrete atomic norm bound. -/
def smoothWeightedCoefficientEnergy {d n : ℕ}
    (w : LayerIndex d n → ℝ) (x : LayerIndex d n → ℝ) : ℝ :=
  ∑ a : LayerIndex d n, w a * x a ^ 2

theorem smoothWeightedCoefficientEnergy_nonneg {d n : ℕ}
    (w : LayerIndex d n → ℝ) (hw : ∀ a, 0 ≤ w a)
    (x : LayerIndex d n → ℝ) :
    0 ≤ smoothWeightedCoefficientEnergy w x := by
  unfold smoothWeightedCoefficientEnergy
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (hw a) (sq_nonneg _)

theorem smoothWeightedCoefficientEnergy_integrable {d n : ℕ}
    (w : LayerIndex d n → ℝ) :
    Integrable (smoothWeightedCoefficientEnergy w)
      (productStandardGaussian (LayerIndex d n)) := by
  unfold smoothWeightedCoefficientEnergy
  apply integrable_finsetSum Finset.univ
  intro a ha
  exact (integrable_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
    (i := a) (standardGaussian_pow_integrable 2)).const_mul (w a)

theorem smoothWeightedCoefficientEnergy_mean {d n : ℕ}
    (w : LayerIndex d n → ℝ) :
    (∫ x : LayerIndex d n → ℝ, smoothWeightedCoefficientEnergy w x
      ∂productStandardGaussian (LayerIndex d n)) = ∑ a : LayerIndex d n, w a := by
  have hsecond : standardGaussianMoment 2 = 1 := by
    unfold standardGaussianMoment
    rw [show (2 : ℕ) = 2 * 1 by norm_num, standardGaussian_evenMoment]
    norm_num
  unfold smoothWeightedCoefficientEnergy productStandardGaussian
  rw [integral_finsetSum Finset.univ (fun a ha => by
    exact (integrable_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
      (i := a) (standardGaussian_pow_integrable 2)).const_mul (w a))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul]
  rw [integral_comp_eval (μ := fun _ : LayerIndex d n => gaussianReal 0 1)
    (i := a) (f := fun t => t ^ 2) (by fun_prop)]
  change w a * standardGaussianMoment 2 = w a
  rw [hsecond]
  ring

/-- With any deterministic nonnegative coefficient weights, a genuine
Gaussian Sobolev-energy cutoff has mass at least one half. Its threshold is
twice one plus the exact expected energy; no class norm estimate is built in. -/
theorem smoothWeightedCoefficientCutoff_mass {d n : ℕ}
    (w : LayerIndex d n → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (LayerIndex d n))
        {x | smoothWeightedCoefficientEnergy w x ≤
          2 * (1 + ∑ a : LayerIndex d n, w a)} := by
  let M : ℝ := 1 + ∑ a : LayerIndex d n, w a
  have hsum : 0 ≤ ∑ a : LayerIndex d n, w a := Finset.sum_nonneg fun a ha => hw a
  have hM : 0 < M := by dsimp [M]; linarith
  have hmean :
      ∫ x : LayerIndex d n → ℝ, smoothWeightedCoefficientEnergy w x
        ∂productStandardGaussian (LayerIndex d n) ≤ M := by
    rw [smoothWeightedCoefficientEnergy_mean]
    dsimp [M]
    linarith
  have hmass := gaussian_nonneg_energy_cutoff_mass
    (productStandardGaussian (LayerIndex d n)) (smoothWeightedCoefficientEnergy w)
    (by fun_prop [smoothWeightedCoefficientEnergy])
    (smoothWeightedCoefficientEnergy_integrable w)
    (smoothWeightedCoefficientEnergy_nonneg w hw) hM hmean
  simpa [M] using hmass

end BrownianSharp
