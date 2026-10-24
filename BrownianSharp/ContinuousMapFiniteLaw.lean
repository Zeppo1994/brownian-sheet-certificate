import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Process.FiniteDimensionalLaws

open MeasureTheory ProbabilityTheory

namespace HaarQuarter

/-- Finite evaluation laws determine a random continuous function on a
second-countable locally compact parameter space. -/
theorem continuousMap_map_eq_of_finite_evaluations
    {K Ω : Type*} [TopologicalSpace K] [SecondCountableTopology K]
    [LocallyCompactSpace K] [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (F G : Ω → C(K, ℝ)) (hF : Measurable F) (hG : Measurable G)
    (hfinite : ∀ I : Finset K,
      P.map (fun ω => I.restrict (fun x => F ω x)) =
        P.map (fun ω => I.restrict (fun x => G ω x))) :
    P.map F = P.map G := by
  let coeFun : C(K, ℝ) → (K → ℝ) := fun f => f
  have hcoe : Measurable coeFun :=
    measurable_pi_lambda fun x => ContinuousMap.measurable_eval x
  have hraw : P.map (fun ω x => F ω x) = P.map (fun ω x => G ω x) :=
    (map_eq_iff_forall_finset_map_restrict_eq
      (hcoe.comp hF).aemeasurable (hcoe.comp hG).aemeasurable).mpr hfinite
  have hcomap : (inferInstance : MeasurableSpace C(K, ℝ)) =
      (inferInstance : MeasurableSpace (K → ℝ)).comap coeFun := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    rfl
  apply Measure.ext
  intro s hs
  have hs' : MeasurableSet[
      (inferInstance : MeasurableSpace (K → ℝ)).comap coeFun] s := by
    rw [← hcomap]
    exact hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs'
  calc
    (P.map F) (coeFun ⁻¹' t) = ((P.map F).map coeFun) t :=
      (Measure.map_apply hcoe ht).symm
    _ = ((P.map G).map coeFun) t := by
      rw [Measure.map_map hcoe hF, Measure.map_map hcoe hG]
      exact congrArg (fun μ : Measure (K → ℝ) => μ t) hraw
    _ = (P.map G) (coeFun ⁻¹' t) := Measure.map_apply hcoe ht

end HaarQuarter
