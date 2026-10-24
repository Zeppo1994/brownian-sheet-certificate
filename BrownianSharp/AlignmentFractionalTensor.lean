import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentFractionalL2
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensor

theorem memLp_pi_product {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun u : ι → ℝ => ∏ i, f i (u i)) 2 (Measure.pi μ) := by
  have hI : ∀ i, Integrable (f i) (μ i) := fun i =>
    (hf i).integrable (by norm_num)
  have hsq : ∀ i, Integrable (fun x => (f i x)^2) (μ i) := fun i =>
    (memLp_two_iff_integrable_sq (hf i).aestronglyMeasurable).mp (hf i)
  have hprod := Integrable.fintype_prod hI
  apply (memLp_two_iff_integrable_sq hprod.aestronglyMeasurable).mpr
  simpa only [Finset.prod_pow] using Integrable.fintype_prod hsq

theorem realLp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : ‖g‖^2 = ∫ u, (g u)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext u
  simp [pow_two]

def piProductLp {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    Lp ℝ 2 (Measure.pi μ) :=
  (memLp_pi_product f hf).toLp (fun u => ∏ i, f i (u i))

theorem piProductLp_norm_sq {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μ i)] (f : ι → ℝ → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    ‖piProductLp f hf‖^2 = ∏ i, ‖(hf i).toLp (f i)‖^2 := by
  rw [realLp_norm_sq]
  have hae := (memLp_pi_product f hf).coeFn_toLp
  change ∫ u, ((memLp_pi_product f hf).toLp (fun u => ∏ i, f i (u i)) u)^2
      ∂Measure.pi μ = _
  rw [integral_congr_ae (hae.mono (fun u hu => congrArg (fun x : ℝ => x^2) hu))]
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun i x => (f i x)^2)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [realLp_norm_sq]
  exact integral_congr_ae ((hf i).coeFn_toLp.mono (fun u hu =>
    congrArg (fun x : ℝ => x^2) hu.symm))

theorem unitCube_measure_eq_pi (d : ℕ) :
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d) =
      Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1)) := by
  exact Measure.restrict_pi_pi _ _

/-- The actual Gamma-normalized tensor kernel belongs to the source L²
space for every coordinate order greater than one half. -/
theorem fractionalTensorKernel_memLp {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i, 1/2<a i) (t : BrownianCubeAnchor d) :
    MemLp (Latest.fractionalTensorKernel a t) 2
      ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)) := by
  rw [unitCube_measure_eq_pi]
  have h := memLp_pi_product
    (fun i => AlignmentFractionalL2.causalKernel (a i) (t.val i))
    (fun i => AlignmentFractionalL2.causalKernel_memLp_unit (ha i)
      ((t.property i).1) ((t.property i).2))
  exact h

end BrownianSharp.AlignmentFractionalTensor
