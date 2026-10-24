import BrownianSharp.GaussianRows
import BrownianSharp.SmoothCoefficientEvents
import Mathlib.Tactic

/-! Arbitrary-real absolute moments of finite Gaussian rows. This is the scalar
moment bridge needed before applying Tonelli to pointwise smooth-block variance
bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp

/-- The finite Gaussian row moment argument also records integrability,
needed when moments are moved through finite sums or Tonelli. -/
theorem gaussianRow_absRpow_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c : ι → ℝ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ω => |GaussianRows.row G c ω| ^ p) P := by
  let V : ℝ := ∑ i, c i ^ 2
  by_cases hV : V = 0
  · have hc : ∀ i, c i = 0 := by
      intro i
      have hi : c i ^ 2 ≤ ∑ j, c j ^ 2 := Finset.single_le_sum
        (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
      rw [show ∑ j, c j ^ 2 = V by rfl, hV] at hi
      nlinarith [sq_nonneg (c i)]
    have hrow : GaussianRows.row G c = 0 := by
      funext ω
      simp [GaussianRows.row, hc]
    rw [hrow]
    simpa using
      (integrable_const (c := (0 : ℝ)) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · have hVpos : 0 < V := by
      have hnonneg : 0 ≤ V := by
        dsimp [V]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
      exact lt_of_le_of_ne hnonneg (Ne.symm hV)
    let σ : ℝ := Real.sqrt V
    have hσ : 0 < σ := Real.sqrt_pos.mpr hVpos
    let X : Ω → ℝ := fun ω => GaussianRows.row G c ω / σ
    have hXlaw : P.map X = gaussianReal 0 1 := by
      dsimp [X, σ, V]
      exact GaussianRows.normalized_row_law G hG hLaw hIndep c hVpos
    have hrowm : Measurable (GaussianRows.row G c) := by
      change Measurable (fun ω => ∑ i, c i * G i ω)
      exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
    have hXm : Measurable X := by
      dsimp [X]
      exact hrowm.div_const σ
    have hX : HasLaw X (gaussianReal 0 1) P := ⟨hXm.aemeasurable, hXlaw⟩
    have hbase : Integrable (fun t : ℝ => |t| ^ p) (gaussianReal 0 1) :=
      gaussianAbsoluteMoment_integrable hp
    have hXint : Integrable (fun ω => |X ω| ^ p) P :=
      hX.integrable_comp hbase
    have hscale : ∀ ω, |GaussianRows.row G c ω| ^ p =
        σ ^ p * |X ω| ^ p := by
      intro ω
      have hx : GaussianRows.row G c ω = σ * X ω := by
        dsimp [X]
        field_simp
      rw [hx, abs_mul, abs_of_pos hσ, Real.mul_rpow hσ.le (abs_nonneg _)]
    have hmul : Integrable (fun ω => σ ^ p * |X ω| ^ p) P :=
      hXint.const_mul _
    apply hmul.congr
    filter_upwards with ω
    exact (hscale ω).symm

/-- A finite linear combination of independent standard Gaussian coordinates
has the expected absolute `p`th moment, for every positive real `p`. -/
theorem gaussianRow_absRpow_integral
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c : ι → ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, |GaussianRows.row G c ω| ^ p ∂P) =
      (Real.sqrt (∑ i, c i ^ 2)) ^ p * gaussianAbsoluteMoment p := by
  let V : ℝ := ∑ i, c i ^ 2
  by_cases hV : V = 0
  · have hc : ∀ i, c i = 0 := by
      intro i
      have hi : c i ^ 2 ≤ ∑ j, c j ^ 2 := Finset.single_le_sum
        (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
      have hnonneg : 0 ≤ c i ^ 2 := sq_nonneg _
      change c i ^ 2 ≤ V at hi
      rw [hV] at hi
      nlinarith
    have hrow : GaussianRows.row G c = 0 := by
      funext ω
      simp [GaussianRows.row, hc]
    rw [hrow]
    simp [V, hV, Real.zero_rpow hp.ne']
  · have hVpos : 0 < V := by
      have hnonneg : 0 ≤ V := by
        dsimp [V]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
      exact lt_of_le_of_ne hnonneg (Ne.symm hV)
    let σ : ℝ := Real.sqrt V
    have hσ : 0 < σ := Real.sqrt_pos.mpr hVpos
    have hσsq : σ ^ 2 = V := by dsimp [σ]; exact Real.sq_sqrt hVpos.le
    let X : Ω → ℝ := fun ω => GaussianRows.row G c ω / σ
    have hXlaw : P.map X = gaussianReal 0 1 := by
      dsimp [X, σ, V]
      exact GaussianRows.normalized_row_law G hG hLaw hIndep c hVpos
    have hrowm : Measurable (GaussianRows.row G c) := by
      change Measurable (fun ω => ∑ i, c i * G i ω)
      exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
    have hXm : Measurable X := by
      dsimp [X]
      exact hrowm.div_const σ
    have hX : HasLaw X (gaussianReal 0 1) P := ⟨by
      exact hXm.aemeasurable, hXlaw⟩
    have hbase : Integrable (fun t : ℝ => |t| ^ p) (gaussianReal 0 1) :=
      gaussianAbsoluteMoment_integrable hp
    have hXint : Integrable (fun ω => |X ω| ^ p) P :=
      hX.integrable_comp hbase
    have hXmean : (∫ ω, |X ω| ^ p ∂P) = gaussianAbsoluteMoment p := by
      unfold gaussianAbsoluteMoment
      exact hX.integral_comp hbase.aestronglyMeasurable
    have hscale : ∀ ω, |GaussianRows.row G c ω| ^ p =
        σ ^ p * |X ω| ^ p := by
      intro ω
      have hx : GaussianRows.row G c ω = σ * X ω := by
        dsimp [X]
        field_simp
      rw [hx, abs_mul, abs_of_pos hσ, Real.mul_rpow hσ.le (abs_nonneg _)]
    calc
      (∫ ω, |GaussianRows.row G c ω| ^ p ∂P) =
          ∫ ω, σ ^ p * |X ω| ^ p ∂P := by
            apply integral_congr_ae
            filter_upwards with ω
            exact hscale ω
      _ = σ ^ p * ∫ ω, |X ω| ^ p ∂P := by rw [integral_const_mul]
      _ = (Real.sqrt V) ^ p * gaussianAbsoluteMoment p := by
        rw [hXmean]

end BrownianSharp
