import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Whitney-style balls for an open bad set on a metric space.

The covering selection is the pinned Mathlib Vitali enlargement theorem. The
radius `infDist x Ωᶜ / 6` ensures the core ball stays in Ω and the sevenfold
ball reaches Ωᶜ, as in the attributed Calderón–Zygmund construction described
in `Partition.lean`.
-/

open Set Metric
open scoped Topology

namespace BrownianSharp.External.WeakCZ

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]

/-- A disjoint Whitney family whose fivefold balls cover the open set. Each
core is contained in the open set, while the sevenfold ball meets its
complement. `hR` is the bounded-radius condition required by Vitali; for a
bounded space this follows by comparing `infDist` with a point in Ωᶜ. -/
theorem exists_whitneyVitaliCover (Ω : Set α) (hΩ : IsOpen Ω) (hΩne : Ω ≠ univ)
    (R : ℝ) (hR : ∀ x ∈ Ω, infDist x Ωᶜ / 6 ≤ R) :
    ∃ U : Set α,
      U ⊆ Ω ∧
      U.PairwiseDisjoint (fun x => ball x (Metric.infDist x Ωᶜ / 6)) ∧
      (∀ x ∈ Ω, ∃ y ∈ U, x ∈ ball y (5 * (Metric.infDist y Ωᶜ / 6))) ∧
      (∀ y ∈ U, ball y (Metric.infDist y Ωᶜ / 6) ⊆ Ω ∧
        ¬ Disjoint (ball y (7 * (Metric.infDist y Ωᶜ / 6))) Ωᶜ) := by
  classical
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem Ω).mp hΩne
  have hΩc : Ωᶜ.Nonempty := ⟨z, hz⟩
  let r : α → ℝ := fun x => Metric.infDist x Ωᶜ / 6
  have hrpos : ∀ x ∈ Ω, 0 < r x := by
    intro x hx
    change 0 < Metric.infDist x Ωᶜ / 6
    have hx' : x ∉ Ωᶜ := by simpa using hx
    exact div_pos ((hΩ.isClosed_compl.notMem_iff_infDist_pos hΩc).mp hx') (by norm_num)
  have hball : ∀ x ∈ Ω, ball x (r x) ⊆ Ω := by
    intro x hx z hz
    change z ∈ ball x (Metric.infDist x Ωᶜ / 6) at hz
    exact (Metric.ball_subset_ball (by nlinarith [Metric.infDist_nonneg (x := x) (s := Ωᶜ)] :
      Metric.infDist x Ωᶜ / 6 ≤ Metric.infDist x Ωᶜ)).trans
      (Metric.ball_infDist_compl_subset (x := x) (s := Ω)) hz
  have hcontact : ∀ x ∈ Ω, ¬ Disjoint (ball x (7 * r x)) Ωᶜ := by
    intro x hx
    change ¬ Disjoint (ball x (7 * (Metric.infDist x Ωᶜ / 6))) Ωᶜ
    have hd : Metric.infDist x Ωᶜ < 7 * (Metric.infDist x Ωᶜ / 6) := by
      have hpos := hrpos x hx
      change 0 < Metric.infDist x Ωᶜ / 6 at hpos
      linarith
    obtain ⟨z, hz, hdist⟩ := (Metric.infDist_lt_iff hΩc).mp hd
    rw [not_disjoint_iff_nonempty_inter]
    exact ⟨z, ⟨mem_ball.mpr (by simpa [dist_comm] using hdist), hz⟩⟩
  obtain ⟨U, hU, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (t := Ω) (x := id) (r := r) R (fun x hx => hR x hx) 5 (by norm_num)
  refine ⟨U, hU, hdisj, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact ⟨y, hy, hxy (mem_ball_self (hrpos x hx))⟩
  · intro y hy
    exact ⟨hball y (hU hy), hcontact y (hU hy)⟩

/-- The radius bound in `exists_whitneyVitaliCover` follows from boundedness
of the ambient space. -/
theorem exists_whitneyVitaliCover_of_bounded (Ω : Set α) (hΩ : IsOpen Ω)
    (hΩne : Ω ≠ univ) (hbounded : Bornology.IsBounded (Set.univ : Set α)) :
    ∃ U : Set α,
      U ⊆ Ω ∧
      U.PairwiseDisjoint (fun x => ball x (Metric.infDist x Ωᶜ / 6)) ∧
      (∀ x ∈ Ω, ∃ y ∈ U, x ∈ ball y (5 * (Metric.infDist y Ωᶜ / 6))) ∧
      (∀ y ∈ U, ball y (Metric.infDist y Ωᶜ / 6) ⊆ Ω ∧
        ¬ Disjoint (ball y (7 * (Metric.infDist y Ωᶜ / 6))) Ωᶜ) := by
  have hR : ∀ x ∈ Ω, Metric.infDist x Ωᶜ / 6 ≤ Metric.diam (Set.univ : Set α) / 6 := by
    intro x hx
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem Ω).mp hΩne
    calc
      Metric.infDist x Ωᶜ / 6 ≤ dist x z / 6 := by
        gcongr
        exact Metric.infDist_le_dist_of_mem hz
      _ ≤ Metric.diam (Set.univ : Set α) / 6 := by
        gcongr
        exact Metric.dist_le_diam_of_mem hbounded (Set.mem_univ x) (Set.mem_univ z)
  exact exists_whitneyVitaliCover Ω hΩ hΩne (Metric.diam (Set.univ : Set α) / 6) hR

/-- On a separable bounded space, the selected Whitney centers form a
countable set, so the family can be enumerated for the CZ partition. -/
theorem exists_countable_whitneyVitaliCover [TopologicalSpace.SeparableSpace α] (Ω : Set α)
    (hΩ : IsOpen Ω) (hΩne : Ω ≠ univ)
    (hbounded : Bornology.IsBounded (Set.univ : Set α)) :
    ∃ U : Set α,
      U.Countable ∧ U ⊆ Ω ∧
      U.PairwiseDisjoint (fun x => ball x (Metric.infDist x Ωᶜ / 6)) ∧
      (∀ x ∈ Ω, ∃ y ∈ U, x ∈ ball y (5 * (Metric.infDist y Ωᶜ / 6))) ∧
      (∀ y ∈ U, ball y (Metric.infDist y Ωᶜ / 6) ⊆ Ω ∧
        ¬ Disjoint (ball y (7 * (Metric.infDist y Ωᶜ / 6))) Ωᶜ) := by
  obtain ⟨U, hU, hdisj, hcover, hprops⟩ :=
    exists_whitneyVitaliCover_of_bounded Ω hΩ hΩne hbounded
  have hcount : U.Countable := hdisj.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun y hy => ⟨y, mem_ball_self <|
      div_pos ((hΩ.isClosed_compl.notMem_iff_infDist_pos
        (by obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem Ω).mp hΩne; exact ⟨z, hz⟩)
        ).mp (by simpa using hU hy)) (by norm_num)⟩)
  exact ⟨U, hcount, hU, hdisj, hcover, hprops⟩

end BrownianSharp.External.WeakCZ
