import BrownianSharp.AlignmentGaussianShift
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Bases

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BrownianSharp.AlignmentGaussianGridLimit

theorem finite_grid_mass_lower_to_uniform_mass_lower
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (points : ℕ→α) (hdense : DenseRange points)
    (F : Ω→C(α,ℝ)) (hF : ∀t,Measurable (fun ω=>F ω t))
    (f : C(α,ℝ)) (ε : ℝ) (hε : 0≤ε) (c : ENNReal)
    (hfinite : ∀S : Finset α,
      c*P {ω | ∀t∈S,|F ω t|≤ε} ≤
        P {ω | ∀t∈S,|F ω t-f t|≤ε}) :
    c*P {ω | ‖F ω‖≤ε} ≤ P {ω | ‖F ω-f‖≤ε} := by
  classical
  let A : ℕ→Set Ω := fun n => {ω | ∀j∈Finset.range n,
    |F ω (points j)-f (points j)|≤ε}
  have hAm : ∀n,MeasurableSet (A n) := by
    intro n
    simp only [A,Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (continuous_abs.measurable.comp
      ((hF (points j)).sub_const _)) measurable_const
  have hanti : Antitone A := by
    intro m n hmn ω hω j hj
    exact hω j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hmn))
  have hinter : (⋂n,A n)={ω | ‖F ω-f‖≤ε} := by
    ext ω
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro h
      apply (ContinuousMap.norm_le _ hε).2
      intro t
      exact hdense.induction_on (p:=fun t=>‖(F ω-f) t‖≤ε) t
        (isClosed_le (F ω-f).continuous.norm continuous_const) (by
          intro j
          have hj := h (j+1) j (Finset.mem_range.mpr (Nat.lt_succ_self j))
          simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs] using hj)
    · intro h n j _
      have hv := (ContinuousMap.norm_coe_le_norm (F ω-f) (points j)).trans h
      simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs] using hv
  rw [←hinter,hanti.measure_iInter (fun n=>(hAm n).nullMeasurableSet)
    ⟨0,measure_ne_top _ _⟩]
  apply le_iInf
  intro n
  let S : Finset α := (Finset.range n).image points
  have hbase : {ω | ‖F ω‖≤ε} ⊆ {ω | ∀t∈S,|F ω t|≤ε} := by
    intro ω hω t _
    exact (ContinuousMap.norm_coe_le_norm (F ω) t).trans hω
  have hbound := (mul_le_mul le_rfl (measure_mono hbase) bot_le bot_le).trans (hfinite S)
  simpa only [S,A,Finset.forall_mem_image] using hbound


end BrownianSharp.AlignmentGaussianGridLimit
