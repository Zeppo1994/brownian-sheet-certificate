import BrownianSharp.CameronMartinEntropy
import BrownianSharp.IndependentComparison
import BrownianSharp.ProbabilisticCover
import BrownianSharp.Statistics
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic


/-!
# Cameron--Martin covering lower bound from native confinement

A finite native Haar coefficient ball has substantial standard-Gaussian mass and maps into the
actual restricted-cube Cameron--Martin image.  Anderson's inequality bounds every translated
finite-grid path ball by the centered confinement probability.  The resulting entropy lower
bound is conditional only on that explicit confinement estimate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal ENNReal RealInnerProductSpace

namespace BrownianSharp.CameronMartinCover

/-- Reindex a standard coefficient vector by a finite equivalence to the native layer. -/
def reindexNative {d n : ℕ} (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) : LayerIndex d n → ℝ :=
  fun a => x (e.symm a)

/-- Reindexing preserves exact Euclidean coefficient energy. -/
theorem coefficientEnergy_reindex {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) :
    CameronMartinEntropy.coefficientEnergy (reindexNative e x) =
      CameronMartinEntropy.coefficientEnergy x := by
  classical
  unfold CameronMartinEntropy.coefficientEnergy reindexNative
  symm
  exact Fintype.sum_equiv e (fun i => x i ^ 2)
    (fun a => x (e.symm a) ^ 2) (by intro i; simp)

/-- The deterministic native evaluation matrix on a finite grid. -/
def nativeGridMatrix {d n M : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (t : Fin M → BrownianCubeAnchor d) : Fin M → Fin (Fintype.card (LayerIndex d n)) → ℝ :=
  fun j i => ⟪CameronMartinEntropy.nativeAmbientBasis (e i),
    (brownianCubeSpanEmbedding d (CameronMartin.featureVector (t j)))⟫

/-- The coefficient vector's normalized native path in the actual Cameron--Martin ball model. -/
def normalizedNativePath {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) :
    C(BrownianCubeAnchor d, ℝ) :=
  CameronMartin.anchoredIntegrationPath
    (CameronMartinEntropy.normalizedAmbientIntegrand (reindexNative e x))

/-- Every point in the Euclidean native coefficient cutoff produces a point in the manuscript's
restricted-cube Cameron--Martin image. -/
theorem normalizedNativePath_mem_KdUnitCube {d n : ℕ} [Nonempty (LayerIndex d n)]
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ)
    (hcut : CameronMartinEntropy.coefficientEnergy x ≤
      4 * (Fintype.card (LayerIndex d n) : ℝ)) :
    normalizedNativePath e x ∈ CameronMartin.KdUnitCube d := by
  unfold normalizedNativePath
  apply CameronMartinEntropy.nativeNormalizedPath_mem_KdUnitCube
  rw [coefficientEnergy_reindex]
  exact hcut

private theorem normalizedNativePath_eval_eq {d n M : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) (j : Fin M)
    (t : Fin M → BrownianCubeAnchor d) :
    normalizedNativePath e x (t j) =
      (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ))⁻¹ *
        rowEvaluation (nativeGridMatrix e t) x j := by
  classical
  let feat : CameronMartin.AmbientL2 d :=
    brownianCubeSpanEmbedding d (CameronMartin.featureVector (t j))
  have hsynth :
      ⟪CameronMartinEntropy.nativeAmbientSynthesis (reindexNative e x), feat⟫ =
        rowEvaluation (nativeGridMatrix e t) x j := by
    rw [CameronMartinEntropy.nativeAmbientSynthesis,
      CameronMartinEntropy.coefficientIntegrandMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_smul_left]
    unfold rowEvaluation nativeGridMatrix
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    change (∑ a : LayerIndex d n,
        (starRingEnd ℝ) (x (e.symm a)) *
          ⟪CameronMartinEntropy.nativeAmbientBasis a, feat⟫) =
      ∑ i : Fin (Fintype.card (LayerIndex d n)),
        ⟪CameronMartinEntropy.nativeAmbientBasis (e i), feat⟫ * x i
    symm
    apply Fintype.sum_equiv e
    intro i
    simp [mul_comm]
  change ⟪(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ))⁻¹ •
      CameronMartinEntropy.nativeAmbientSynthesis (reindexNative e x),
      brownianCubeSpanEmbedding d (CameronMartin.featureVector (t j))⟫ = _
  rw [inner_smul_left, hsynth]
  simp only [starRingEnd_apply, star_trivial]



/-- A path ball of radius `ε/R` around any center maps at the finite grid into a translated
closed cube of radius `ε`. -/
private theorem normalizedPathBall_subset_translatedGridCube {d n M : ℕ} [Nonempty (LayerIndex d n)]
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (t : Fin M → BrownianCubeAnchor d) (ε : ℝ) (hε : 0 ≤ ε)
    (f : C(BrownianCubeAnchor d, ℝ))
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ)
    (hball : edist (normalizedNativePath e x) f ≤
      (ENNReal.ofNNReal (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0))) :
    rowEvaluation (nativeGridMatrix e t) x +
      (fun j => -(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) * f (t j)) ∈
        Metric.closedBall (0 : Fin M → ℝ) ε := by
  let R : ℝ := 2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hball' : edist (normalizedNativePath e x) f ≤
      (ENNReal.ofNNReal (⟨ε / R, by positivity⟩ : ℝ≥0)) := by
    simpa [R] using hball
  have hdistNN : nndist (normalizedNativePath e x) f ≤
      (⟨ε / R, by positivity⟩ : ℝ≥0) := (edist_le_coe.mp hball')
  have hdist : dist (normalizedNativePath e x) f ≤ ε / R := by
    have hcast : (↑(nndist (normalizedNativePath e x) f) : ℝ) =
        nndist (normalizedNativePath e x) f := rfl
    exact_mod_cast hdistNN
  have hnorm : ‖normalizedNativePath e x - f‖ ≤ ε / R := by
    simpa [dist_eq_norm] using hdist
  have hscaled : ‖R • (normalizedNativePath e x - f)‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    calc
      R * ‖normalizedNativePath e x - f‖ ≤ R * (ε / R) :=
        mul_le_mul_of_nonneg_left hnorm (le_of_lt hR)
      _ = ε := by field_simp
  have hcoord : ∀ j, |rowEvaluation (nativeGridMatrix e t) x j -
      R * f (t j)| ≤ ε := by
    intro j
    have hpath :
        (normalizedNativePath e x - f) (t j) =
          (R⁻¹ * rowEvaluation (nativeGridMatrix e t) x j) - f (t j) := by
      change normalizedNativePath e x (t j) - f (t j) = _
      rw [normalizedNativePath_eval_eq]
    have hcomponent : ‖(R • (normalizedNativePath e x - f)) (t j)‖ ≤
        ‖R • (normalizedNativePath e x - f)‖ :=
      (R • (normalizedNativePath e x - f)).norm_coe_le_norm (t j)
    have hscaledcoord : |R * ((normalizedNativePath e x - f) (t j))| ≤ ε := by
      have h := hcomponent.trans hscaled
      simpa [Real.norm_eq_abs, abs_of_pos hR] using h
    have hRinv : R * (R⁻¹ * rowEvaluation (nativeGridMatrix e t) x j - f (t j)) =
        rowEvaluation (nativeGridMatrix e t) x j - R * f (t j) := by
      field_simp
    rw [hpath, hRinv] at hscaledcoord
    exact hscaledcoord
  have hnormball : ‖rowEvaluation (nativeGridMatrix e t) x -
      (R • (fun j => f (t j)))‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).2
    intro j
    change ‖rowEvaluation (nativeGridMatrix e t) x j - R * f (t j)‖ ≤ ε
    rw [Real.norm_eq_abs]
    exact hcoord j
  change dist _ _ ≤ ε
  rw [dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hε).2
  intro j
  change ‖rowEvaluation (nativeGridMatrix e t) x j +
    (-(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) * f (t j))‖ ≤ ε
  rw [Real.norm_eq_abs]
  have harg : rowEvaluation (nativeGridMatrix e t) x j +
      (-(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) * f (t j)) =
      rowEvaluation (nativeGridMatrix e t) x j - R * f (t j) := by
    dsimp [R]
    ring
  rw [harg]
  exact hcoord j

/-- Each path ball is controlled by the centered finite-grid confinement bound via Anderson.
The probability input `hconf` is the only probabilistic hypothesis left in this cover step. -/
theorem normalizedNativePath_ball_mass_le {d n M : ℕ} [Nonempty (LayerIndex d n)]
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (t : Fin M → BrownianCubeAnchor d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ≥0∞)
    (hconf : (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1))
      {x | ‖rowEvaluation (nativeGridMatrix e t) x‖ ≤ ε} ≤ q) :
    ∀ f : C(BrownianCubeAnchor d, ℝ),
      (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1))
        {x | edist (normalizedNativePath e x) f ≤
          (ENNReal.ofNNReal (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0))} ≤ q := by
  intro f
  let A : (Fin (Fintype.card (LayerIndex d n)) → ℝ) →ₗ[ℝ] (Fin M → ℝ) :=
    rowEvaluation (nativeGridMatrix e t)
  let C : Set (Fin M → ℝ) := Metric.closedBall (0 : Fin M → ℝ) ε
  have hN : 0 < Fintype.card (LayerIndex d n) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hconv : Convex ℝ C := by
    exact convex_closedBall _ _
  have hsymm : ∀ z, z ∈ C → -z ∈ C := by
    intro z hz
    have hz' : ‖z‖ ≤ ε := by simpa [C, Metric.mem_closedBall, dist_eq_norm] using hz
    simpa [C, Metric.mem_closedBall, dist_eq_norm] using hz'
  have hmeas : MeasurableSet C := by
    exact measurableSet_closedBall
  have hshift : (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1))
      {x | A x + (fun j => -(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) * f (t j)) ∈ C} ≤ q := by
    calc
      _ ≤ (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1))
          {x | A x ∈ C} := by
            exact standardGaussian_linear_shift_le_of_pos hN
              C A (fun j => -(2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) * f (t j))
              hconv hsymm hmeas
      _ ≤ q := by simpa [A, C, Metric.mem_closedBall, dist_eq_norm] using hconf
  apply le_trans (measure_mono ?_) hshift
  intro x hx
  have hcube := normalizedPathBall_subset_translatedGridCube e t ε (le_of_lt hε) f x hx
  simpa [A, C] using hcube

/-- Direct Cameron--Martin entropy lower bound from native coefficient cutoff mass and a centered
finite-grid confinement estimate. -/
theorem nativeCameronMartin_externalCoveringNumber_gt
    {d n M : ℕ} [Nonempty (LayerIndex d n)] (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (t : Fin M → BrownianCubeAnchor d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ≥0∞) (m : ℕ)
    (hconf : (Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1))
      {x | ‖rowEvaluation (nativeGridMatrix e t) x‖ ≤ ε} ≤ q)
    (hmass : (m : ℝ≥0∞) * q < (3 / 4 : ℝ≥0∞)) :
    (m : ℕ∞) < Metric.externalCoveringNumber
      (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0)
      (CameronMartin.KdUnitCube d) := by
  have hcardpos : 0 < Fintype.card (LayerIndex d n) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hFinCard : 0 < Fintype.card (Fin (Fintype.card (LayerIndex d n))) := by
    simpa using hcardpos
  haveI : Nonempty (Fin (Fintype.card (LayerIndex d n))) := Fintype.card_pos_iff.mp hFinCard
  let P := Measure.pi (fun _ : Fin (Fintype.card (LayerIndex d n)) => gaussianReal 0 1)
  let E : Set (Fin (Fintype.card (LayerIndex d n)) → ℝ) :=
    {x | CameronMartinEntropy.coefficientEnergy x ≤
      4 * (Fintype.card (LayerIndex d n) : ℝ)}
  let F : (Fin (Fintype.card (LayerIndex d n)) → ℝ) → C(BrownianCubeAnchor d, ℝ) :=
    normalizedNativePath e
  have hclass : ∀ x ∈ E, F x ∈ CameronMartin.KdUnitCube d := by
    intro x hx
    have hx' : CameronMartinEntropy.coefficientEnergy x ≤
        4 * (Fintype.card (LayerIndex d n) : ℝ) := by
      change CameronMartinEntropy.coefficientEnergy x ≤
        4 * (Fintype.card (LayerIndex d n) : ℝ) at hx
      exact hx
    exact normalizedNativePath_mem_KdUnitCube e x hx
  have hball : ∀ f : C(BrownianCubeAnchor d, ℝ), P {x | edist (F x) f ≤
      (ENNReal.ofNNReal (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0))} ≤ q :=
    normalizedNativePath_ball_mass_le e t ε hε q hconf
  have hcut := CameronMartinEntropy.standardGaussian_coefficientCutoff_mass
    (Fin (Fintype.card (LayerIndex d n)))
  have hmassE : (m : ℝ≥0∞) * q < P E := lt_of_lt_of_le hmass (by
    dsimp [P, E]
    simpa only [Fintype.card_fin] using hcut)
  simpa [P, F, E] using
    (externalCoveringNumber_gt_of_admissible_mass
      P F E (CameronMartin.KdUnitCube d)
      (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0)
      q m hclass hball hmassE)

end BrownianSharp.CameronMartinCover
