import BrownianSharp.FiniteDictionaryReindex
import BrownianSharp.FiniteCoordinateLayerRank
import BrownianSharp.FiniteCoordinateLayers

/-! Assemble finite dictionary approximations on disjoint coordinate layers.
The `none` layer is represented exactly by its coordinate-sliced row span;
each `some j` layer uses the supplied finite Gaussian dictionary theorem. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp

variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq J]

theorem finiteRow_dictionary_layer_assembly {C : ℝ}
    (hfin : FinDictionaryApproximation C) (hC : 0 ≤ C)
    (σ : I → Option J) (v : G → EuclideanSpace ℝ I)
    (m : J → ℕ) (R : J → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g, ‖coordinateLayerMask σ (some j) (v g)‖ ≤ R j) :
    ∃ W : Submodule ℝ (G → ℝ),
      Module.rank ℝ W ≤
        ((Fintype.card {i : I // σ i = none} + ∑ j, m j : ℕ) : Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ 1 → ∃ y ∈ W,
        ‖finiteRowLinear v x - y‖ ≤
          Real.sqrt (∑ j,
            (C * R j * Real.sqrt
              (Real.log (2 * (Fintype.card G : ℝ) + 2) / ((m j : ℝ) + 1))) ^ 2) := by
  classical
  let Vlow : Submodule ℝ (G → ℝ) := finiteLayerRowSpan σ v none
  let mlow : ℕ := Fintype.card {i : I // σ i = none}
  let epsHi : J → ℝ := fun j =>
    C * R j * Real.sqrt
      (Real.log (2 * (Fintype.card G : ℝ) + 2) / ((m j : ℝ) + 1))
  have hhigh : ∀ j, ∃ V : Submodule ℝ (G → ℝ),
      Module.rank ℝ V ≤ (m j : Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ 1 → ∃ y ∈ V,
        ‖finiteRowLayerLinear σ v (some j) x - y‖ ≤ epsHi j := by
    intro j
    exact dictionary_approximation_of_fin_dictionary hfin (m j)
      (fun g => coordinateLayerMask σ (some j) (v g)) (R j) (hR j) (hrow j)
  choose Vhigh hVhigh_rank hVhigh_approx using hhigh
  let V : Option J → Submodule ℝ (G → ℝ) := fun q =>
    match q with | none => Vlow | some j => Vhigh j
  let m' : Option J → ℕ := fun q => match q with | none => mlow | some j => m j
  let eps : Option J → ℝ := fun q => match q with | none => 0 | some j => epsHi j
  have hVfin : ∀ q : Option J, FiniteDimensional ℝ (V q) := by
    intro q
    infer_instance
  letI : ∀ q : Option J, FiniteDimensional ℝ (V q) := hVfin
  have hm : ∀ q : Option J, Module.finrank ℝ (V q) ≤ m' q := by
    intro q
    cases q with
    | none =>
        dsimp [V, m']
        exact (finiteLayerRowSpan_finrank_le σ v none)
    | some j =>
        have hrank := hVhigh_rank j
        rw [← Module.finrank_eq_rank ℝ (Vhigh j)] at hrank
        exact_mod_cast hrank
  have heps : ∀ q : Option J, 0 ≤ eps q := by
    intro q
    cases q with
    | none => simp [eps]
    | some j =>
        dsimp [eps, epsHi]
        have harg : 1 ≤ 2 * (Fintype.card G : ℝ) + 2 := by
          have hM : (0 : ℝ) ≤ (Fintype.card G : ℝ) := Nat.cast_nonneg _
          nlinarith
        have hlog : 0 ≤ Real.log (2 * (Fintype.card G : ℝ) + 2) :=
          Real.log_nonneg harg
        have hden : 0 < (m j : ℝ) + 1 := by positivity
        have hfrac : 0 ≤ Real.log (2 * (Fintype.card G : ℝ) + 2) /
            ((m j : ℝ) + 1) := div_nonneg hlog hden.le
        exact mul_nonneg (mul_nonneg hC (hR j))
          (Real.sqrt_nonneg _)
  have happ : ∀ q : Option J, ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ 1 →
      ∃ y ∈ V q, ‖finiteRowLayerLinear σ v q x - y‖ ≤ eps q := by
    intro q x hx
    cases q with
    | none =>
        let y := finiteRowLayerLinear σ v none x
        have hy : y ∈ Vlow := by
          exact finiteRowLayerLinear_mem_finiteLayerRowSpan σ v none x
        refine ⟨y, ?_, ?_⟩
        · simpa [V, y, Vlow] using hy
        · simp [y, eps]
    | some j =>
        simpa [V, eps, epsHi] using hVhigh_approx j x hx
  obtain ⟨W, hWrank, hWapprox⟩ :=
    finiteRow_unitBall_approximation σ v V m' hm eps heps happ
  refine ⟨W, ?_, ?_⟩
  · have hsum : (∑ q : Option J, m' q) =
        Fintype.card {i : I // σ i = none} + ∑ j, m j := by
      simp [m', mlow, Fintype.sum_option]
    rw [hsum] at hWrank
    exact hWrank
  · intro x hx
    obtain ⟨y, hy, herr⟩ := hWapprox x hx
    refine ⟨y, hy, ?_⟩
    have hsimp : ∑ q : Option J, (eps q) ^ 2 = ∑ j, (epsHi j) ^ 2 := by
      simp [eps, Fintype.sum_option]
    rw [hsimp] at herr
    simpa [epsHi] using herr

end BrownianSharp
