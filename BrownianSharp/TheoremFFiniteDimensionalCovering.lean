import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.CoveringNumbers

open MeasureTheory MeasureTheory.Measure Metric Set ENNReal Module

namespace HaarQuarter.TheoremF.FiniteDimensionalCovering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A volume-packing bound for separated points in a finite-dimensional norm ball.
The constant is independent of the norm on `E`. -/
theorem card_le_covering_bound (S : Finset E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hbound : ∀ x ∈ S, dist x 0 ≤ R)
    (hsep : Set.Pairwise (↑S : Set E) fun x y => ε < dist x y) :
    (S.card : ℝ) ≤ (1 + 2 * R / ε) ^ Module.finrank ℝ E := by
  let b : Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let μ : Measure E := b.addHaar
  letI : IsAddHaarMeasure μ := isAddHaarMeasure_basis_addHaar b
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have houter : 0 ≤ R + δ := by positivity
  have hdisj : Set.PairwiseDisjoint (↑S : Set E) fun x => closedBall x δ := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    have hxy' : ε < dist x y := hsep hx hy hxy
    dsimp [δ]
    nlinarith
  have hmeas : ∀ x ∈ S, MeasurableSet (closedBall x δ) := by
    intro x hx
    exact measurableSet_closedBall
  have hfinite : ∀ x ∈ S, μ (closedBall x δ) ≠ ⊤ := by
    intro x hx
    rw [addHaar_closedBall_eq_addHaar_ball μ x δ]
    exact (ne_of_lt measure_ball_lt_top)
  have hcontain : (⋃ x ∈ S, closedBall x δ) ⊆ closedBall 0 (R + δ) := by
    intro z hz
    rcases mem_iUnion.1 hz with ⟨x, hz⟩
    rcases mem_iUnion.1 hz with ⟨hxS, hzball⟩
    have hxR := hbound x hxS
    have hzx := (mem_closedBall.mp hzball)
    change dist z 0 ≤ R + δ
    calc
      dist z 0 ≤ dist z x + dist x 0 := dist_triangle z x 0
      _ ≤ δ + R := by linarith
      _ = R + δ := by ring
  have hsum := measureReal_biUnion_finset (μ := μ) hdisj hmeas hfinite
  have houterfinite : μ (closedBall (0 : E) (R + δ)) ≠ ⊤ := by
    rw [addHaar_closedBall_eq_addHaar_ball μ 0 (R + δ)]
    exact (ne_of_lt measure_ball_lt_top)
  have hmeasure_le := measureReal_mono hcontain houterfinite
  have hball (x : E) : μ.real (closedBall x δ) = δ ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
    exact addHaar_real_closedBall μ x hδ0
  have houterball : μ.real (closedBall (0 : E) (R + δ)) =
      (R + δ) ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
    exact addHaar_real_closedBall μ 0 houter
  have hpos : 0 < μ.real (ball (0 : E) 1) := by
    have hopen : 0 < μ (ball (0 : E) 1) :=
      isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr zero_lt_one)
    rw [measureReal_def]
    exact ENNReal.toReal_pos hopen.ne.symm (ne_of_lt measure_ball_lt_top)
  have hsumform : (∑ x ∈ S, μ.real (closedBall x δ)) =
      (S.card : ℝ) * (δ ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1)) := by
    simp_rw [hball]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hineq : (S.card : ℝ) * (δ ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1)) ≤
      (R + δ) ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
    calc
      _ = μ.real (⋃ x ∈ S, closedBall x δ) := by rw [hsum]; exact hsumform.symm
      _ ≤ μ.real (closedBall (0 : E) (R + δ)) := hmeasure_le
      _ = _ := houterball
  have hδpow : 0 < δ ^ Module.finrank ℝ E := pow_pos hδ _
  have hscaled : (S.card : ℝ) * δ ^ Module.finrank ℝ E ≤ (R + δ) ^ Module.finrank ℝ E := by
    apply (le_of_mul_le_mul_right ?_ hpos)
    simpa [mul_assoc] using hineq
  have hfinal : (S.card : ℝ) ≤ ((R + δ) / δ) ^ Module.finrank ℝ E := by
    have := (le_div_iff₀ hδpow).2 hscaled
    calc
      (S.card : ℝ) ≤ (R + δ) ^ Module.finrank ℝ E / δ ^ Module.finrank ℝ E := this
      _ = ((R + δ) / δ) ^ Module.finrank ℝ E := by rw [← div_pow]
  have hratio : (R + δ) / δ = 1 + 2 * R / ε := by
    dsimp [δ]
    field_simp
    ring
  simpa [hratio] using hfinal

/-- A separated subset of a compact set is finite. -/
theorem finite_of_separated_subset_compact {α : Type*} [PseudoMetricSpace α]
    {K C : Set α} {ε : ℝ} (hK : IsCompact K) (hCK : C ⊆ K)
    (hε : 0 < ε) (hsep : Set.Pairwise C fun x y => ε < dist x y) : C.Finite := by
  classical
  obtain ⟨t, htK, htfin, htcover⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hcoverx (x : C) : ∃ y ∈ t, dist (x : α) y < ε / 3 := by
    rcases mem_iUnion.1 (htcover (hCK x.2)) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyt, hyx⟩
    exact ⟨y, hyt, by simpa [Metric.mem_ball] using hyx⟩
  let f : C → {y : α // y ∈ t} := fun x =>
    ⟨Classical.choose (hcoverx x), (Classical.choose_spec (hcoverx x)).1⟩
  have hfcover (x : C) : dist (x : α) (f x) < ε / 3 :=
    (Classical.choose_spec (hcoverx x)).2
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hsep' : ε < dist (x : α) y := by
      exact hsep x.2 y.2 (fun hxy => hne (Subtype.ext hxy))
    have hlt : dist (x : α) y < ε := by
      calc
        dist (x : α) y ≤ dist (x : α) (f x : α) + dist (f x : α) (y : α) := dist_triangle ..
        _ < ε / 3 + ε / 3 := by
          have hy := hfcover y
          have hx := hfcover x
          exact add_lt_add hx (by simpa [dist_comm, hxy] using hy)
        _ < ε := by linarith
    exact (not_lt_of_ge (le_of_lt hsep')) hlt
  letI : Finite {y : α // y ∈ t} := Finite.to_subtype htfin
  exact Set.finite_coe_iff.mpr (Finite.of_injective f hfinj)

/-- The packing number of a compact finite-dimensional norm ball is bounded by the
volumetric estimate, rounded up to a natural number. -/
theorem packingNumber_le_ceil (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    [CompleteSpace E] :
    Metric.packingNumber (NNReal.mk ε hε.le) (closedBall (0 : E) R) ≤
      ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ E)) := by
  classical
  have hcompact : IsCompact (closedBall (0 : E) R) := isCompact_closedBall (0 : E) R
  unfold Metric.packingNumber
  apply iSup_le
  intro C
  apply iSup_le
  intro hCK
  apply iSup_le
  intro hsep
  have hsepReal : Set.Pairwise C fun x y => ε < dist x y := by
    intro x hx y hy hne
    have h := hsep hx hy hne
    have hcast : ENNReal.ofNNReal (NNReal.mk ε hε.le) < ENNReal.ofReal (dist x y) := by
      simpa [edist_dist] using h
    rw [← ENNReal.ofReal_eq_coe_nnreal hε.le] at hcast
    have hdpos : 0 < dist x y := by
      by_contra hnot
      have hzero : dist x y = 0 := le_antisymm (le_of_not_gt hnot) dist_nonneg
      rw [hzero, ENNReal.ofReal_zero] at hcast
      have hnn : 0 ≤ ENNReal.ofReal ε := by positivity
      exact (not_lt_of_ge hnn) hcast
    exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mp hcast
  have hfinite := finite_of_separated_subset_compact hcompact hCK hε hsepReal
  let S := hfinite.toFinset
  have hSC : (↑S : Set E) = C := hfinite.coe_toFinset
  have hbound : ∀ x ∈ S, dist x 0 ≤ R := by
    intro x hx
    have hxC : x ∈ C := by rw [← hSC]; exact hx
    have hxK : x ∈ closedBall (0 : E) R := hCK hxC
    exact mem_closedBall.mp hxK
  have hsep' : Set.Pairwise (↑S : Set E) fun x y => ε < dist x y := by
    intro x hx y hy hne
    have hxC : x ∈ C := by rw [← hSC]; exact hx
    have hyC : y ∈ C := by rw [← hSC]; exact hy
    exact hsepReal hxC hyC hne
  have hreal := card_le_covering_bound S hR hε hbound hsep'
  have hnat : S.card ≤ Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ E) := by
    exact_mod_cast hreal.trans (Nat.le_ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ E))
  have hencard : C.encard = ↑S.card := by
    rw [← hSC]
    simp
  rw [hencard]
  exact_mod_cast hnat

/-- The internal covering number of a compact finite-dimensional norm ball is bounded by
its volumetric estimate. -/
theorem coveringNumber_le_ceil (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    [CompleteSpace E] :
    Metric.coveringNumber ⟨ε, hε.le⟩ (closedBall (0 : E) R) ≤
      ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ E)) := by
  exact (Metric.coveringNumber_le_packingNumber _ _).trans
    (packingNumber_le_ceil R ε hR hε)

/-- A finite-dimensional ball admits an actual finite internal cover with the volumetric
cardinality bound. -/
theorem exists_ball_cover (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    [CompleteSpace E] :
    ∃ C : Set E, C ⊆ closedBall (0 : E) R ∧ C.Finite ∧
      Metric.IsCover (NNReal.mk ε hε.le) (closedBall (0 : E) R) C ∧
      C.encard ≤ ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ E)) := by
  let εN := NNReal.mk ε hε.le
  let K := closedBall (0 : E) R
  have hcover := coveringNumber_le_ceil (E := E) R ε hR hε
  have hne : Metric.coveringNumber εN K ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hcover
  refine ⟨Metric.minimalCover εN K, Metric.minimalCover_subset, Metric.finite_minimalCover,
    Metric.isCover_minimalCover hne, ?_⟩
  rw [Metric.encard_minimalCover hne]
  exact hcover


/-- The image in the ambient space of a closed ball in a subspace. -/
def submoduleBallImage {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Submodule ℝ X) (R : ℝ) : Set X :=
  Subtype.val '' Metric.closedBall (0 : W) R

/-- A finite-dimensional subspace ball has an ambient-center cover with the same
volumetric bound. The centers remain in the approximating subspace. -/
theorem exists_submodule_ball_cover
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Submodule ℝ X) [FiniteDimensional ℝ W] [Nontrivial W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ C : Set X, C ⊆ submoduleBallImage W R ∧ C.Finite ∧
      Metric.IsCover (NNReal.mk ε hε.le) (submoduleBallImage W R) C ∧
      C.encard ≤ ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ W)) := by
  obtain ⟨C₀, hC₀, hfinite₀, hcover₀, hcard₀⟩ :=
    exists_ball_cover (E := W) R ε hR hε
  let C : Set X := Subtype.val '' C₀
  refine ⟨C, ?_, hfinite₀.image _, ?_, ?_⟩
  · exact Set.image_mono hC₀
  · change Metric.IsCover (NNReal.mk ε hε.le)
      (Subtype.val '' Metric.closedBall (0 : W) R) (Subtype.val '' C₀)
    change ∀ ⦃x⦄, x ∈ Subtype.val '' Metric.closedBall (0 : W) R →
      ∃ y ∈ Subtype.val '' C₀, edist x y ≤ (NNReal.mk ε hε.le : ENNReal)
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hwv⟩ := hcover₀ hw
    have hwv' : edist w v ≤ (NNReal.mk ε hε.le : ENNReal) := by
      change edist w v ≤ (NNReal.mk ε hε.le : ENNReal) at hwv
      exact hwv
    exact ⟨v, ⟨v, hv, rfl⟩,
      by simpa only [edist_nndist, Subtype.nndist_eq] using hwv'⟩
  · exact (Set.encard_image_le Subtype.val C₀).trans hcard₀



end HaarQuarter.TheoremF.FiniteDimensionalCovering
