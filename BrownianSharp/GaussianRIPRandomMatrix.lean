import BrownianSharp.GaussianGridStatistics
import BrownianSharp.GaussianRIPChiSquare
import Mathlib.Probability.HasLaw

/-!
# Gaussian measurement vectors have the expected product law

An iid Gaussian row matrix maps any fixed unit vector to an iid standard
Gaussian vector.  This is the probabilistic bridge needed to apply the
chi-square bounds to fixed test vectors in a finite RIP/net argument.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp.GaussianRIP

/-- An `m`-by-`N` matrix with independent standard Gaussian rows. -/
noncomputable abbrev gaussianMatrixMeasure (m N : ℕ) : Measure (Fin m → (Fin N → ℝ)) :=
  Measure.pi fun _ : Fin m => BrownianSharp.productStandardGaussian (Fin N)

/-- The vector of row measurements of a fixed coefficient vector. -/
def gaussianMatrixProjection {m N : ℕ} (u : Fin N → ℝ)
    (ω : Fin m → (Fin N → ℝ)) : Fin m → ℝ :=
  fun i => ∑ k : Fin N, u k * ω i k

/-- Fixed unit directions are mapped to standard Gaussian vectors by an iid
Gaussian row matrix. -/
theorem gaussianMatrixProjection_hasLaw_standard
    {m N : ℕ} (u : Fin N → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    HasLaw (gaussianMatrixProjection u)
      (BrownianSharp.productStandardGaussian (Fin m)) (gaussianMatrixMeasure m N) := by
  let μ := gaussianMatrixMeasure m N
  have hRows : iIndepFun (fun i : Fin m => fun ω : Fin m → (Fin N → ℝ) => ω i) μ := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hRowLaw (i : Fin m) :
      HasLaw (fun ω : Fin m → (Fin N → ℝ) => ω i)
        (BrownianSharp.productStandardGaussian (Fin N)) μ := by
    exact (measurePreserving_eval
      (fun _ : Fin m => BrownianSharp.productStandardGaussian (Fin N)) i).hasLaw
  have hDot : HasLaw (fun z : Fin N → ℝ => ∑ k : Fin N, u k * z k)
      (gaussianReal 0 1) (BrownianSharp.productStandardGaussian (Fin N)) := by
    let A : Unit → Fin N → ℝ := fun _ => u
    have h := BrownianSharp.normalized_matrix_row_hasLaw A (fun _ => hu) ()
    simpa [A] using h
  have hOutInd : iIndepFun
      (fun i : Fin m => fun ω : Fin m → (Fin N → ℝ) =>
        ∑ k : Fin N, u k * ω i k) μ := by
    exact hRows.comp
      (fun _ z => ∑ k : Fin N, u k * z k)
      (fun _ => by fun_prop)
  have hOutLaw (i : Fin m) :
      HasLaw (fun ω : Fin m → (Fin N → ℝ) => ∑ k : Fin N, u k * ω i k)
        (gaussianReal 0 1) μ := by
    exact hDot.comp (hRowLaw i)
  have hPi := hOutInd.hasLaw_pi hOutLaw
  convert hPi using 1
  · funext ω
    rfl

/-- The upper chi-square estimate transfers to the measurements of any fixed
unit vector under the Gaussian matrix law. -/
theorem gaussianMatrixProjection_upper_tail
    {m N : ℕ} (u : Fin N → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    (gaussianMatrixMeasure m N).real
      {ω | 4 * (m : ℝ) ≤ ∑ i, (gaussianMatrixProjection u ω i) ^ 2} ≤
        Real.exp (-(m : ℝ) / 4) := by
  let P := gaussianMatrixProjection (m := m) u
  have hP := gaussianMatrixProjection_hasLaw_standard (m := m) u hu
  have hsum : Measurable (fun z : Fin m → ℝ => ∑ i, z i ^ 2) := by fun_prop
  have hset : MeasurableSet {z : Fin m → ℝ | 4 * (m : ℝ) ≤ ∑ i, z i ^ 2} := by
    change MeasurableSet ((fun z : Fin m → ℝ => ∑ i, z i ^ 2) ⁻¹' Set.Ici (4 * (m : ℝ)))
    exact measurableSet_Ici.preimage hsum
  have hmap := MeasureTheory.map_measureReal_apply_of_aemeasurable hP.aemeasurable hset
  rw [hP.map_eq] at hmap
  have htail := productGaussian_sqNorm_upper_tail (κ := Fin m)
  have heq : (gaussianMatrixMeasure m N).real
      {ω | 4 * (m : ℝ) ≤ ∑ i, (P ω i) ^ 2} =
      (BrownianSharp.productStandardGaussian (Fin m)).real
        {z | 4 * (m : ℝ) ≤ ∑ i, z i ^ 2} := by
    simpa [P, gaussianMatrixProjection] using hmap.symm
  rw [heq]
  simpa using htail

/-- The lower chi-square estimate transfers to the measurements of any fixed
unit vector under the Gaussian matrix law. -/
theorem gaussianMatrixProjection_lower_tail
    {m N : ℕ} (u : Fin N → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    (gaussianMatrixMeasure m N).real
      {ω | ∑ i, (gaussianMatrixProjection u ω i) ^ 2 ≤ (m : ℝ) / 4} ≤
        Real.exp (-(m : ℝ) / 4) := by
  let P := gaussianMatrixProjection (m := m) u
  have hP := gaussianMatrixProjection_hasLaw_standard (m := m) u hu
  have hsum : Measurable (fun z : Fin m → ℝ => ∑ i, z i ^ 2) := by fun_prop
  have hset : MeasurableSet {z : Fin m → ℝ | ∑ i, z i ^ 2 ≤ (m : ℝ) / 4} := by
    change MeasurableSet ((fun z : Fin m → ℝ => ∑ i, z i ^ 2) ⁻¹' Set.Iic ((m : ℝ) / 4))
    exact measurableSet_Iic.preimage hsum
  have hmap := MeasureTheory.map_measureReal_apply_of_aemeasurable hP.aemeasurable hset
  rw [hP.map_eq] at hmap
  have htail := productGaussian_sqNorm_lower_tail (κ := Fin m)
  have heq : (gaussianMatrixMeasure m N).real
      {ω | ∑ i, (P ω i) ^ 2 ≤ (m : ℝ) / 4} =
      (BrownianSharp.productStandardGaussian (Fin m)).real
        {z | ∑ i, z i ^ 2 ≤ (m : ℝ) / 4} := by
    simpa [P, gaussianMatrixProjection] using hmap.symm
  rw [heq]
  simpa using htail

/-- Stronger upper-tail transfer, at the squared radius `2m`. -/
theorem gaussianMatrixProjection_upper_tail_two
    {m N : ℕ} (u : Fin N → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    (gaussianMatrixMeasure m N).real
      {ω | 2 * (m : ℝ) ≤ ∑ i, (gaussianMatrixProjection u ω i) ^ 2} ≤
        Real.exp (-(m : ℝ) / 16) := by
  let P := gaussianMatrixProjection (m := m) u
  have hP := gaussianMatrixProjection_hasLaw_standard (m := m) u hu
  have hsum : Measurable (fun z : Fin m → ℝ => ∑ i, z i ^ 2) := by fun_prop
  have hset : MeasurableSet {z : Fin m → ℝ | 2 * (m : ℝ) ≤ ∑ i, z i ^ 2} := by
    change MeasurableSet ((fun z : Fin m → ℝ => ∑ i, z i ^ 2) ⁻¹' Set.Ici (2 * (m : ℝ)))
    exact measurableSet_Ici.preimage hsum
  have hmap := MeasureTheory.map_measureReal_apply_of_aemeasurable hP.aemeasurable hset
  rw [hP.map_eq] at hmap
  have htail := productGaussian_sqNorm_upper_tail_two (κ := Fin m)
  have heq : (gaussianMatrixMeasure m N).real
      {ω | 2 * (m : ℝ) ≤ ∑ i, (P ω i) ^ 2} =
      (BrownianSharp.productStandardGaussian (Fin m)).real
        {z | 2 * (m : ℝ) ≤ ∑ i, z i ^ 2} := by
    simpa [P, gaussianMatrixProjection] using hmap.symm
  rw [heq]
  simpa using htail

/-- Stronger lower-tail transfer, at the squared radius `m/2`. -/
theorem gaussianMatrixProjection_lower_tail_half
    {m N : ℕ} (u : Fin N → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    (gaussianMatrixMeasure m N).real
      {ω | ∑ i, (gaussianMatrixProjection u ω i) ^ 2 ≤ (m : ℝ) / 2} ≤
        Real.exp (-(m : ℝ) / 100) := by
  let P := gaussianMatrixProjection (m := m) u
  have hP := gaussianMatrixProjection_hasLaw_standard (m := m) u hu
  have hsum : Measurable (fun z : Fin m → ℝ => ∑ i, z i ^ 2) := by fun_prop
  have hset : MeasurableSet {z : Fin m → ℝ | ∑ i, z i ^ 2 ≤ (m : ℝ) / 2} := by
    change MeasurableSet ((fun z : Fin m → ℝ => ∑ i, z i ^ 2) ⁻¹' Set.Iic ((m : ℝ) / 2))
    exact measurableSet_Iic.preimage hsum
  have hmap := MeasureTheory.map_measureReal_apply_of_aemeasurable hP.aemeasurable hset
  rw [hP.map_eq] at hmap
  have htail := productGaussian_sqNorm_lower_tail_half (κ := Fin m)
  have heq : (gaussianMatrixMeasure m N).real
      {ω | ∑ i, (P ω i) ^ 2 ≤ (m : ℝ) / 2} =
      (BrownianSharp.productStandardGaussian (Fin m)).real
        {z | ∑ i, z i ^ 2 ≤ (m : ℝ) / 2} := by
    simpa [P, gaussianMatrixProjection] using hmap.symm
  rw [heq]
  simpa using htail

/-- A finite family of unit directions is simultaneously well-conditioned by
some Gaussian row matrix whenever the union-bound budget is below one.  This
is the probability-to-existence step used after constructing the sphere nets. -/
theorem exists_gaussianMatrix_good_on_finite_directions
    {m N : ℕ} {J : Type*} [Fintype J] (u : J → Fin N → ℝ)
    (hu : ∀ j, ∑ k, (u j k) ^ 2 = 1)
    (hbudget : (Fintype.card J : ℝ) *
      (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ ω : Fin m → (Fin N → ℝ), ∀ j : J,
      (m : ℝ) / 2 < ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ∧
      ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 < 2 * (m : ℝ) := by
  let μ := gaussianMatrixMeasure m N
  let bad : J → Set (Fin m → (Fin N → ℝ)) := fun j =>
    {ω | 2 * (m : ℝ) ≤ ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2} ∪
    {ω | ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ≤ (m : ℝ) / 2}
  have hbadmeas (j : J) : MeasurableSet (bad j) := by
    apply MeasurableSet.union
    · have hs : Measurable (fun ω : Fin m → (Fin N → ℝ) =>
          ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2) := by
        dsimp [gaussianMatrixProjection]
        fun_prop
      change MeasurableSet ((fun ω : Fin m → (Fin N → ℝ) =>
        ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2) ⁻¹' Set.Ici (2 * (m : ℝ)))
      exact measurableSet_Ici.preimage hs
    · have hs : Measurable (fun ω : Fin m → (Fin N → ℝ) =>
          ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2) := by
        dsimp [gaussianMatrixProjection]
        fun_prop
      change MeasurableSet ((fun ω : Fin m → (Fin N → ℝ) =>
        ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2) ⁻¹' Set.Iic ((m : ℝ) / 2))
      exact measurableSet_Iic.preimage hs
  have hbound : μ.real (⋃ j, bad j) ≤
      (Fintype.card J : ℝ) * (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) := by
    calc
      μ.real (⋃ j, bad j) ≤ ∑ j, μ.real (bad j) :=
        MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : J,
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) := by
        apply Finset.sum_le_sum
        intro j hj
        change μ.real
            ({ω | 2 * (m : ℝ) ≤
                ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2} ∪
              {ω | ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ≤ (m : ℝ) / 2}) ≤ _
        calc
          μ.real
              ({ω | 2 * (m : ℝ) ≤
                  ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2} ∪
                {ω | ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ≤ (m : ℝ) / 2}) ≤
              μ.real {ω | 2 * (m : ℝ) ≤
                  ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2} +
                μ.real {ω | ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ≤ (m : ℝ) / 2} :=
            MeasureTheory.measureReal_union_le _ _
          _ ≤ Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100) := by
            gcongr
            · exact gaussianMatrixProjection_upper_tail_two (u j) (hu j)
            · exact gaussianMatrixProjection_lower_tail_half (u j) (hu j)
      _ = (Fintype.card J : ℝ) *
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        <;> ring
  have hprob : IsProbabilityMeasure μ := by
    dsimp [μ, gaussianMatrixMeasure]
    infer_instance
  by_contra hnone
  push_neg at hnone
  have hunion : (⋃ j, bad j) = Set.univ := by
    apply Set.eq_univ_iff_forall.2
    intro ω
    obtain ⟨j, hj⟩ := hnone ω
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change 2 * (m : ℝ) ≤
        ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ∨
      ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2 ≤ (m : ℝ) / 2
    by_cases hlo : (m : ℝ) / 2 <
        ∑ i, (gaussianMatrixProjection (u j) ω i) ^ 2
    · exact Or.inl (hj hlo)
    · exact Or.inr (le_of_not_gt hlo)
  have hone : (1 : ℝ) ≤ μ.real (⋃ j, bad j) := by
    rw [hunion]
    simp
  linarith [hbudget]

end BrownianSharp.GaussianRIP
