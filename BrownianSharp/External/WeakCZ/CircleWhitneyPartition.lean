import BrownianSharp.External.WeakCZ.CountablePartition
import BrownianSharp.External.WeakCZ.WhitneyCover
import BrownianSharp.AlignmentPaperCircleDoubling
import BrownianSharp.UnitTorusMeasure
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Countable reserved-core Whitney partition for actual uncentered high-average
sets on the normalized circle.
-/

noncomputable section
open Set Metric MeasureTheory

namespace BrownianSharp.External.WeakCZ

structure CircleWhitneyPieceData (Ω : Set UnitAddCircle) where
  Index : Type
  countableIndex : Countable Index
  center : Index → UnitAddCircle
  radius : Index → ℝ
  core : Index → Set UnitAddCircle
  core_eq_ball : ∀ i, core i = ball (center i) (radius i)
  piece : Index → Set UnitAddCircle
  core_subset_piece : ∀ i, core i ⊆ piece i
  piece_subset_five : ∀ i, piece i ⊆ ball (center i) (5 * radius i)
  piece_subset_Ω : ∀ i, piece i ⊆ Ω
  core_positive : ∀ i, 0 < volume.real (core i)
  core_pairwiseDisjoint : Pairwise (fun i j => Disjoint (core i) (core j))
  piece_pairwiseDisjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  piece_measurable : ∀ i, MeasurableSet (piece i)
  piece_iUnion : (⋃ i, piece i) = Ω
  radius_pos : ∀ i, 0 < radius i
  contact : ∀ i, ¬ Disjoint (ball (center i) (7 * radius i)) Ωᶜ

attribute [instance] CircleWhitneyPieceData.countableIndex

/-- Build the actual countable Whitney partition by reserving each disjoint
core ball inside its assigned piece and assigning overlap points by code. -/
noncomputable def circleWhitneyPieceData (Ω : Set UnitAddCircle)
    (hΩ : IsOpen Ω) (hΩne : Ω ≠ Set.univ) : CircleWhitneyPieceData Ω := by
  let hcoverExists := exists_countable_whitneyVitaliCover Ω hΩ hΩne isCompact_univ.isBounded
  let U : Set UnitAddCircle := Classical.choose hcoverExists
  have hUdata : U.Countable ∧ U ⊆ Ω ∧
      U.PairwiseDisjoint (fun x => ball x (Metric.infDist x Ωᶜ / 6)) ∧
      (∀ x ∈ Ω, ∃ y ∈ U, x ∈ ball y (5 * (Metric.infDist y Ωᶜ / 6))) ∧
      (∀ y ∈ U, ball y (Metric.infDist y Ωᶜ / 6) ⊆ Ω ∧
        ¬ Disjoint (ball y (7 * (Metric.infDist y Ωᶜ / 6))) Ωᶜ) := by
    simpa [U] using Classical.choose_spec hcoverExists
  rcases hUdata with ⟨hUcount, hU, hdisj, hcover, hprops⟩
  let I := {x : UnitAddCircle // x ∈ U}
  letI : Countable I := hUcount.to_subtype
  letI : Encodable I := Encodable.ofCountable I
  let c : I → UnitAddCircle := fun i => i.val
  let r : I → ℝ := fun i => Metric.infDist i.val Ωᶜ / 6
  let C : I → Set UnitAddCircle := fun i => ball (c i) (r i)
  let D : I → Set UnitAddCircle := fun i => ball (c i) (5*r i) ∩ Ω
  let E : I → Set UnitAddCircle := fun i => rankedCoreExpandedPiece C D i
  have hrpos (i : I) : 0 < r i := by
    dsimp [r, c]
    obtain ⟨z, hz⟩ := Set.ne_univ_iff_exists_notMem Ω |>.mp hΩne
    have hxΩ : i.val ∈ Ω := hU i.property
    have hdist := (hΩ.isClosed_compl.notMem_iff_infDist_pos ⟨z, hz⟩).mp (by simpa using hxΩ)
    positivity
  have hcoreΩ (i : I) : C i ⊆ Ω := by
    dsimp [C, c, r]
    exact (hprops i.val i.property).1
  have hball5 (i : I) : C i ⊆ ball (c i) (5*r i) := by
    apply ball_subset_ball
    nlinarith [le_of_lt (hrpos i)]
  have hCD (i : I) : C i ⊆ D i := by
    intro x hx
    exact ⟨hball5 i hx, hcoreΩ i hx⟩
  have hcoreDisj : Pairwise (fun i j : I => Disjoint (C i) (C j)) := by
    intro i j hij
    have hij' : i.val ≠ j.val := by
      intro h
      exact hij (Subtype.ext h)
    simpa [C, c, r] using hdisj i.property j.property hij'
  have hEDisj : Pairwise (fun i j : I => Disjoint (E i) (E j)) :=
    rankedCoreExpandedPiece_pairwiseDisjoint C D hCD hcoreDisj
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    apply measurableSet_rankedCoreExpandedPiece C D i
    · intro j; exact measurableSet_ball
    · intro j; exact (measurableSet_ball.inter hΩ.measurableSet)
  have hUcover : (⋃ i : I, D i) = Ω := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      exact hi.2
    · intro hx
      obtain ⟨y, hyU, hyx⟩ := hcover x hx
      exact mem_iUnion.mpr ⟨⟨y, hyU⟩, hyx, hx⟩
  have hEunion : (⋃ i : I, E i) = Ω := by
    rw [iUnion_rankedCoreExpandedPiece_eq C D hCD, hUcover]
  refine ⟨I, inferInstance, c, r, C, ?_, E, ?_, ?_, ?_, ?_, ?_, hEDisj, hEm, hEunion, hrpos, ?_⟩
  · intro i; rfl
  · intro i; exact rankedCoreExpandedPiece_core_subset C D i
  · intro i x hx
    exact (rankedCoreExpandedPiece_subset C D i hCD hx).1
  · intro i x hx
    exact (rankedCoreExpandedPiece_subset C D i hCD hx).2
  · intro i
    have hr := hrpos i
    have hhaar := BrownianSharp.AlignmentPaperCircleDoubling.haar_ball_pos (c i) hr
    have hvol : 0 < volume (C i) := by
      simpa [C, c, r, BrownianSharp.unitAddCircle_volume_eq_haar] using hhaar
    exact ENNReal.toReal_pos hvol.ne' (measure_ne_top _ _)
  · intro i j hij
    have hij' : i.val ≠ j.val := by
      intro h
      exact hij (Subtype.ext h)
    simpa [C, c, r] using hdisj i.property j.property hij'
  · intro i
    exact (hprops i.val i.property).2
