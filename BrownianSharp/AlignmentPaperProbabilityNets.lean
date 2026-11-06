import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Genuine finite nets from lower masses of translated balls. This is the
packing step used to turn Cameron--Martin shift and enlargement estimates
into a finite Gaussian codebook. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentPaperProbabilityNets

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem finite_packing_card_mul_mass_le_one (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Set X) (hS : S.Finite) (r p : ℝ)
    (hsep : S.Pairwise (fun x y => 2*r < dist x y))
    (hmass : ∀ x ∈ S, p ≤ μ.real (Metric.closedBall x r)) :
    (Nat.card S : ℝ)*p ≤ 1 := by
  classical
  letI : Fintype S := hS.fintype
  have hd : Pairwise (fun x y : S => Disjoint (Metric.closedBall x.val r) (Metric.closedBall y.val r)) := by
    intro x y hxy
    apply Metric.closedBall_disjoint_closedBall
    have hne : x.val ≠ y.val := by intro h; exact hxy (Subtype.ext h)
    simpa [two_mul] using hsep x.property y.property hne
  calc
    (Nat.card S : ℝ)*p = ∑ _x : S, p := by simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ x : S, μ.real (Metric.closedBall x.val r) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hmass x.val x.property
    _ = μ.real (⋃ x : S, Metric.closedBall x.val r) :=
      (measureReal_iUnion_fintype (μ := μ) hd (fun _ => measurableSet_closedBall)).symm
    _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := by simp

/-- A compact set whose radius-r translated balls each have mass at least p
has an actual finite 2r-net with cardinality times p at most one. -/
theorem exists_compact_net_of_ball_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (K : Set X) (hK : IsCompact K) (r : ℝ≥0) (hr : 0 < r) (p : ℝ)
    (hmass : ∀ x ∈ K, p ≤ μ.real (Metric.closedBall x (r:ℝ))) :
    ∃ S : Set X, S ⊆ K ∧ S.Finite ∧ Metric.IsCover (2*r) K S ∧
      (Nat.card S : ℝ)*p ≤ 1 := by
  classical
  obtain ⟨C,hC,hCcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (r:ℝ) hr
  have hcover : Metric.IsCover r K C := by
    intro x hx
    obtain ⟨c,hxc⟩ := Set.mem_iUnion.1 (hCcover hx)
    obtain ⟨hc,hxc⟩ := Set.mem_iUnion.1 hxc
    refine ⟨c,hc,?_⟩
    have hd : dist x c ≤ (r:ℝ) := (Metric.mem_ball.1 hxc).le
    change edist x c ≤ (r:ℝ≥0∞)
    rw [edist_dist]
    exact_mod_cast hd
  have hpack : Metric.packingNumber (2*r) K ≠ ⊤ := by
    apply ne_of_lt
    exact (Metric.packingNumber_two_mul_le_externalCoveringNumber r K).trans_lt
      (hcover.externalCoveringNumber_le_encard.trans_lt hC.encard_lt_top)
  let S := Metric.maximalSeparatedSet (2*r) K
  have hsub : S ⊆ K := Metric.maximalSeparatedSet_subset
  have hS : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [show S.encard = Metric.packingNumber (2*r) K from Metric.encard_maximalSeparatedSet hpack]
    exact lt_top_iff_ne_top.mpr hpack
  have hsep : S.Pairwise (fun x y => 2*(r:ℝ) < dist x y) := by
    intro x hx y hy hxy
    have h := Metric.isSeparated_maximalSeparatedSet (ε := 2*r) (A := K) hx hy hxy
    change ((2*r:ℝ≥0):ℝ≥0∞) < edist x y at h
    rw [edist_dist] at h
    have h' : ENNReal.ofReal (((2*r:ℝ≥0):ℝ)) < ENNReal.ofReal (dist x y) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using h
    have hh := (ENNReal.ofReal_lt_ofReal_iff (dist_pos.mpr hxy)).mp h'
    exact_mod_cast hh
  exact ⟨S,hsub,hS,Metric.isCover_maximalSeparatedSet hpack,
    finite_packing_card_mul_mass_le_one μ S hS (r:ℝ) p hsep
      (fun x hx => hmass x (hsub hx))⟩

end BrownianSharp.AlignmentPaperProbabilityNets
