import BrownianSharp.GaussianRIPRandomMatrix
import Mathlib.Analysis.Normed.Operator.Basic
import BrownianSharp.TheoremFFiniteDimensionalCovering

/-!
# Deterministic extension from sphere nets to operator bounds

This module is independent of how the finite sphere net is built.  It records
the standard approximation step converting Gaussian bounds on a finite
epsilon-net into a norm estimate on the whole space.
-/

namespace BrownianSharp.GaussianRIP

open scoped NNReal

theorem operator_norm_le_of_finite_sphere_net
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Type*} [Fintype J] (A : E →L[ℝ] F) (v : J → E)
    (ε L U : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1) (hU : 0 ≤ U)
    (hcover : ∀ x, ‖x‖ = 1 → ∃ j, ‖x - v j‖ ≤ ε)
    (hnet : ∀ j, L ≤ ‖A (v j)‖ ∧ ‖A (v j)‖ ≤ U) :
    ‖A‖ ≤ U / (1 - ε) := by
  have hMnonneg : 0 ≤ U + ε * ‖A‖ := by positivity
  have hpoint : ∀ x : E, ‖A x‖ ≤ (U + ε * ‖A‖) * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y : E := (‖x‖⁻¹) • x
    have hy : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxnorm.le)]
      rw [inv_mul_cancel₀ hxnorm.ne']
    obtain ⟨j, hj⟩ := hcover y hy
    have hAy : ‖A y‖ ≤ U + ε * ‖A‖ := by
      have hsplit : A y = A (v j) + A (y - v j) := by
        rw [map_sub]
        abel
      calc
        ‖A y‖ ≤ ‖A (v j)‖ + ‖A (y - v j)‖ := by rw [hsplit]; exact norm_add_le _ _
        _ ≤ U + ‖A‖ * ‖y - v j‖ := by
          exact add_le_add (hnet j).2 (A.le_opNorm (y - v j))
        _ ≤ U + ‖A‖ * ε := by
          gcongr
        _ = U + ε * ‖A‖ := by ring
    have hxrep : x = ‖x‖ • y := by
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ hxnorm.ne', one_smul]
    have hnormrep : ‖‖x‖ • y‖ = ‖x‖ := by
      rw [norm_smul, hy, Real.norm_eq_abs, abs_of_nonneg hxnorm.le]
      simp
    rw [hxrep, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hxnorm.le]
    rw [hnormrep]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hAy hxnorm.le
  have hK : ‖A‖ ≤ U + ε * ‖A‖ := A.opNorm_le_bound hMnonneg hpoint
  have hmul : (1 - ε) * ‖A‖ ≤ U := by nlinarith
  have hmul' : ‖A‖ * (1 - ε) ≤ U := by nlinarith
  exact (le_div_iff₀ (by linarith : 0 < 1 - ε)).2 hmul'

theorem finite_sphere_net_global_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Type*} [Fintype J] (A : E →L[ℝ] F) (v : J → E)
    (ε L U : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1) (hU : 0 ≤ U)
    (hcover : ∀ x, ‖x‖ = 1 → ∃ j, ‖x - v j‖ ≤ ε)
    (hnet : ∀ j, L ≤ ‖A (v j)‖ ∧ ‖A (v j)‖ ≤ U)
    :
    ∀ x, (L - ε * (U / (1 - ε))) * ‖x‖ ≤ ‖A x‖ ∧
      ‖A x‖ ≤ (U / (1 - ε)) * ‖x‖ := by
  have hop := operator_norm_le_of_finite_sphere_net A v ε L U hε hεlt hU hcover hnet
  intro x
  have hup := A.le_of_opNorm_le hop x
  have hlo : (L - ε * (U / (1 - ε))) * ‖x‖ ≤ ‖A x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y : E := (‖x‖⁻¹) • x
    have hy : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxnorm.le)]
      rw [inv_mul_cancel₀ hxnorm.ne']
    obtain ⟨j, hj⟩ := hcover y hy
    have hAyLower : L - ε * (U / (1 - ε)) ≤ ‖A y‖ := by
      have hdiff : ‖A y‖ + ‖A‖ * ε ≥ ‖A (v j)‖ := by
        have hrepr : A (v j) = A y + A (v j - y) := by rw [map_sub]; abel
        have htriangle : ‖A (v j)‖ ≤ ‖A y‖ + ‖A (v j - y)‖ := by
          rw [hrepr]
          exact norm_add_le _ _
        have hdε : ‖A (v j - y)‖ ≤ ‖A‖ * ε := by
          have hjrev : ‖v j - y‖ ≤ ε := by simpa [norm_sub_rev] using hj
          calc
            ‖A (v j - y)‖ ≤ ‖A‖ * ‖v j - y‖ := A.le_opNorm _
            _ = ‖A‖ * dist (v j) y := by rw [dist_eq_norm]
            _ ≤ ‖A‖ * ε := by rw [dist_eq_norm]; gcongr
        linarith [htriangle, hdε]
      have hnetlo := (hnet j).1
      have hAupper : ‖A‖ * ε ≤ (U / (1 - ε)) * ε := by gcongr
      linarith
    have hAx : ‖A x‖ = ‖x‖ * ‖A y‖ := by
      have hxrep : x = ‖x‖ • y := by
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ hxnorm.ne', one_smul]
      have hnormrep : ‖‖x‖ • y‖ = ‖x‖ := by
        rw [norm_smul, hy, Real.norm_eq_abs, abs_of_nonneg hxnorm.le]
        simp
      rw [hxrep, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hxnorm.le]
      rw [hnormrep]
    rw [hAx]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hAyLower hxnorm.le
  exact ⟨hlo, hup⟩

/-- Every finite-dimensional normed space has a finite unit-sphere net whose
cardinality is controlled by the volumetric ball-covering bound.  We obtain
unit centers by normalizing the nonzero centers of an internal ball cover;
this only doubles the covering radius. -/
theorem exists_finite_unit_sphere_net
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1) :
    ∃ (C : Set E) (hC : C.Finite),
      (∀ x, ‖x‖ = 1 → ∃ c : C, ‖x - (‖c.1‖⁻¹ • c.1)‖ ≤ 2 * ε) ∧
      (∀ c : C, ‖‖c.1‖⁻¹ • c.1‖ = 1) ∧
      (C.ncard : ℝ) ≤ Nat.ceil ((1 + 2 / ε) ^ Module.finrank ℝ E) := by
  classical
  obtain ⟨B, hBsub, hBfin, hBcover, hBcard⟩ :=
    HaarQuarter.TheoremF.FiniteDimensionalCovering.exists_ball_cover
      (E := E) 1 ε (by norm_num) hε
  let C : Set E := {x | x ∈ B ∧ 0 < ‖x‖}
  have hCsub : C ⊆ B := by intro x hx; exact hx.1
  have hCfin : C.Finite := hBfin.subset hCsub
  letI : Fintype C := hCfin.fintype
  refine ⟨C, hCfin, ?_, ?_, ?_⟩
  · intro x hx
    have hxball : x ∈ Metric.closedBall (0 : E) 1 := by
      change dist x 0 ≤ 1
      rw [dist_zero_right, hx]
    obtain ⟨y, hyB, hxy⟩ := hBcover hxball
    have hxy' : dist x y ≤ ε := by
      have hxy'' := hxy
      change edist x y ≤ (NNReal.mk ε hε.le : ENNReal) at hxy''
      rw [edist_dist] at hxy''
      have hr : (NNReal.mk ε hε.le : ENNReal) = ENNReal.ofReal ε := by
        rw [ENNReal.coe_nnreal_eq]
        simp
      rw [hr] at hxy''
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hxy''
    have hyball : dist y 0 ≤ 1 := Metric.mem_closedBall.mp (hBsub hyB)
    have hylow : 1 - ε ≤ ‖y‖ := by
      have hnormdiff := norm_sub_norm_le x y
      rw [hx] at hnormdiff
      have hdist : ‖x - y‖ = dist x y := by rw [dist_eq_norm]
      rw [hdist] at hnormdiff
      linarith
    have hypos : 0 < ‖y‖ := by linarith
    let c : C := ⟨y, hyB, hypos⟩
    refine ⟨c, ?_⟩
    have hcpos : 0 < ‖c.1‖ := c.2.2
    have hnormc : ‖c.1 - (‖c.1‖⁻¹ • c.1)‖ = |‖c.1‖ - 1| := by
      rw [show c.1 - (‖c.1‖⁻¹ • c.1) = (1 - ‖c.1‖⁻¹) • c.1 by
        calc
          c.1 - (‖c.1‖⁻¹ • c.1) = (1 : ℝ) • c.1 - ‖c.1‖⁻¹ • c.1 := by rw [one_smul]
          _ = (1 - ‖c.1‖⁻¹) • c.1 := by rw [sub_smul]]
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |1 - ‖c.1‖⁻¹| * ‖c.1‖ = |1 - ‖c.1‖⁻¹| * |‖c.1‖| := by
          rw [abs_of_pos hcpos]
        _ = |(1 - ‖c.1‖⁻¹) * ‖c.1‖| := by rw [abs_mul]
        _ = |‖c.1‖ - 1| := by congr 1; field_simp
    have hcupper : ‖c.1‖ ≤ 1 := by
      have := Metric.mem_closedBall.mp (hBsub c.2.1)
      simpa [dist_zero_right] using this
    have hcab : |‖c.1‖ - 1| ≤ ε := by
      rw [abs_of_nonpos (by linarith : ‖c.1‖ - 1 ≤ 0)]
      have hclow : 1 - ε ≤ ‖c.1‖ := by simpa [c] using hylow
      linarith
    have hxyNorm : ‖x - c.1‖ ≤ ε := by simpa [dist_eq_norm, c] using hxy'
    calc
      ‖x - (‖c.1‖⁻¹ • c.1)‖ ≤ ‖x - c.1‖ + ‖c.1 - (‖c.1‖⁻¹ • c.1)‖ := by
        simpa [sub_add_sub_cancel] using norm_add_le (x - c.1) (c.1 - (‖c.1‖⁻¹ • c.1))
      _ ≤ ε + ε := by rw [hnormc]; exact add_le_add hxyNorm hcab
      _ = 2 * ε := by ring
  · intro c
    have hcpos : 0 < ‖c.1‖ := c.2.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
    exact inv_mul_cancel₀ (ne_of_gt hcpos)
  · have hCcard : C.ncard ≤ Nat.ceil ((1 + 2 * 1 / ε) ^ Module.finrank ℝ E) := by
      have hBnat : B.ncard ≤ Nat.ceil ((1 + 2 * 1 / ε) ^ Module.finrank ℝ E) :=
        (Set.encard_le_coe_iff_finite_ncard_le).mp hBcard |>.2
      exact (Set.ncard_le_ncard hCsub hBfin).trans hBnat
    norm_cast at hCcard ⊢

end BrownianSharp.GaussianRIP
