import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Basic

/-!
# Fatou bridge from finite approximants to an integrable limit

This generic measure-theoretic lemma is intended for expected finite-grid
maxima whose pointwise limit is a path supremum. It does not assume the limit
is integrable.
-/

open MeasureTheory Filter
open scoped Topology

namespace BrownianSharp.AlignmentAuditFatou

theorem integrable_limit_and_integral_le_of_nonneg_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (fseq : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hfn : ∀ n, Integrable (fseq n) P)
    (hmeas : ∀ n, Measurable (fseq n)) (hfmeas : Measurable f)
    (hnonneg : ∀ n ω, 0 ≤ fseq n ω)
    (hbound : ∀ n, ∫ ω, fseq n ω ∂P ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => fseq n ω) atTop (𝓝 (f ω))) :
    Integrable f P ∧ ∫ ω, f ω ∂P ≤ C := by
  have hnorm_eq (n : ℕ) (ω : Ω) : ‖fseq n ω‖ₑ = ENNReal.ofReal (fseq n ω) := by
    exact Real.enorm_eq_ofReal (hnonneg n ω)
  have hnormMeas (n : ℕ) : Measurable (fun ω => ‖fseq n ω‖ₑ) :=
    measurable_enorm.comp (hmeas n)
  have hlintegral_bound (n : ℕ) :
      ∫⁻ ω, ‖fseq n ω‖ₑ ∂P ≤ ENNReal.ofReal C := by
    rw [show (fun ω => ‖fseq n ω‖ₑ) = fun ω => ENNReal.ofReal (fseq n ω) by
      funext ω
      exact hnorm_eq n ω]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfn n)
      (ae_of_all P (hnonneg n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hliminf_bound :
      Filter.liminf (fun n => ∫⁻ ω, ‖fseq n ω‖ₑ ∂P) atTop ≤ ENNReal.ofReal C := by
    exact liminf_le_of_frequently_le' (Filter.Frequently.of_forall hlintegral_bound)
  have hfatou :
      ∫⁻ ω, ‖f ω‖ₑ ∂P ≤
        Filter.liminf (fun n => ∫⁻ ω, ‖fseq n ω‖ₑ ∂P) atTop := by
    calc
      ∫⁻ ω, ‖f ω‖ₑ ∂P =
          ∫⁻ ω, Filter.liminf (fun n => ‖fseq n ω‖ₑ) atTop ∂P := by
        exact lintegral_congr_ae <| hlim.mono fun ω hω => hω.enorm.liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ‖fseq n ω‖ₑ ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hnormMeas n).aemeasurable)
  have hfnonneg : 0 ≤ᵐ[P] f := by
    filter_upwards [hlim] with ω hω
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hmem : ∀ᶠ n : ℕ in atTop, fseq n ω ∈ Set.Ici (0 : ℝ) :=
      Filter.Eventually.of_forall (fun n => hnonneg n ω)
    exact hclosed.mem_of_tendsto hω hmem
  have hnormf : (fun ω => ‖f ω‖ₑ) =ᵐ[P] fun ω => ENNReal.ofReal (f ω) :=
    hfnonneg.mono fun ω hω => Real.enorm_eq_ofReal hω
  have hliminf_lt_top :
      Filter.liminf (fun n => ∫⁻ ω, ‖fseq n ω‖ₑ ∂P) atTop < ⊤ :=
    lt_of_le_of_lt hliminf_bound ENNReal.ofReal_lt_top
  have hfint : Integrable f P := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt hfatou hliminf_lt_top
  have hfatou' : ENNReal.ofReal (∫ ω, f ω ∂P) ≤ ENNReal.ofReal C := by
    calc
      ENNReal.ofReal (∫ ω, f ω ∂P) = ∫⁻ ω, ‖f ω‖ₑ ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal hfint hfnonneg]
        exact (lintegral_congr_ae hnormf).symm
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ‖fseq n ω‖ₑ ∂P) atTop := hfatou
      _ ≤ ENNReal.ofReal C := hliminf_bound
  refine ⟨hfint, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hfatou'

end BrownianSharp.AlignmentAuditFatou
