import BrownianSharp.NativeRow
import BrownianSharp.CovarianceBound
import BrownianSharp.Prefix

/-!
Finite-row variance of the actual Brownian-sheet projection.  All row entries
are inner products against the original anchored-box evaluation vectors.
-/

open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp

/-- Squared Euclidean norm of the native layer's coefficient row at a midpoint
anchor. -/
noncomputable def nativeLayerRowVariance {d n : ℕ}
    (q : MidpointGridIndex d n) : ℝ :=
  ∑ a : LayerIndex d n, (nativeLayerRowCoefficient q a) ^ 2

/-- The full grid depth profile, viewed as a finitely supported function. -/
noncomputable def nativeFullDepthProfile (d n : ℕ) : Fin d →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => n + 1) (by simp)

/-- Every depth in a grade-`n` layer is at most `n`. -/
theorem layerIndexDepth_le_grade {d n : ℕ} (a : LayerIndex d n) (i : Fin d) :
    layerIndexDepth a i ≤ n := by
  have hgrade := layerIndexDepth_grade a
  have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
    simpa [layerIndexDepth, Finsupp.sum_fintype] using hgrade
  have hle : layerIndexDepth a i ≤ ∑ j : Fin d, layerIndexDepth a j := by
    apply Finset.single_le_sum (s := Finset.univ)
    · intro j hj
      exact Nat.zero_le _
    · simp
  omega

/-- For a fixed midpoint and a fixed depth profile, at most one cell-address
choice can have a nonzero row coefficient. -/
theorem nativeLayerRowCoefficient_sq_pos_unique {d n : ℕ}
    (q : MidpointGridIndex d n) (a b : LayerIndex d n)
    (ha : 0 < (nativeLayerRowCoefficient q a) ^ 2)
    (hb : 0 < (nativeLayerRowCoefficient q b) ^ 2)
    (hdepth : layerIndexDepth a = layerIndexDepth b) : a = b := by
  exact nativeLayerRowProduct_unique_addresses q q a b
    (by simpa [pow_two] using ha)
    (by simpa [pow_two] using hb) hdepth

/-- The sum of squared native row coefficients has the elementary sharp
upper bound obtained by counting one active address per depth profile. -/
theorem nativeLayerRowVariance_le {d n : ℕ} (hd : 0 < d)
    (q : MidpointGridIndex d n) :
    nativeLayerRowVariance q ≤
      (1 / (2 : ℝ) ^ (n + 2 * d)) * Nat.choose (n + d - 1) (d - 1) := by
  classical
  let f : LayerIndex d n → ℝ := fun a =>
    (nativeLayerRowCoefficient q a) ^ 2
  let c := nativeFullDepthProfile d n
  let h := d * (n + 1) - n
  have hc : c.sum (fun _ x => x) = n + h := by
    have hsum : c.sum (fun _ x => x) = d * (n + 1) := by
      simp [c, nativeFullDepthProfile, Finsupp.sum_fintype]
    dsimp [h]
    have hd' : 1 ≤ d := hd
    have hnle : n ≤ d * (n + 1) := by
      calc
        n ≤ n + 1 := Nat.le_succ _
        _ = 1 * (n + 1) := by omega
        _ ≤ d * (n + 1) := Nat.mul_le_mul_right _ hd'
    omega
  have hnonneg : ∀ a, 0 ≤ f a := by
    intro a
    dsimp [f]
    positivity
  have hbound : ∀ a, f a ≤ 1 / (2 : ℝ) ^ (n + 2 * d) := by
    intro a
    dsimp [f]
    exact nativeLayerRowCoefficient_sq_le q a
  have hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i := by
    intro a ha i
    simp [c, nativeFullDepthProfile]
    have hle := layerIndexDepth_le_grade a i
    omega
  have hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b := by
    intro a b ha hb hdepth
    exact nativeLayerRowCoefficient_sq_pos_unique q a b (by simpa [f] using ha)
      (by simpa [f] using hb) hdepth
  have hsum := layerRowProduct_sum_le_of_support hd c hc f
      (1 / (2 : ℝ) ^ (n + 2 * d)) (by positivity) hnonneg hbound hsupport hunique
  calc
    nativeLayerRowVariance q ≤
        (1 / (2 : ℝ) ^ (n + 2 * d)) *
          min (Nat.choose (n + d - 1) (d - 1))
            (Nat.choose (h + d - 1) (d - 1)) := by
      simpa [nativeLayerRowVariance, f] using hsum
    _ ≤ (1 / (2 : ℝ) ^ (n + 2 * d)) *
          Nat.choose (n + d - 1) (d - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.min_le_left _ _

/-- Once a midpoint-grid mean lower bound is available, the actual native row
variance has a positive-density set of grid points above half that mean.
The pointwise upper bound is the sharp layer-count bound proved above. -/
theorem nativeLayerRowVariance_good_fraction {d n : ℕ} (hd : 0 < d)
    (m : ℝ) (hm : 0 < m)
    (hmean : m ≤
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ)) :
    m / (2 * ((1 / (2 : ℝ) ^ (n + 2 * d)) *
        Nat.choose (n + d - 1) (d - 1))) ≤
      ((Finset.univ.filter (fun q : MidpointGridIndex d n =>
          m / 2 ≤ nativeLayerRowVariance q)).card : ℝ) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  have hchoose : 0 < Nat.choose (n + d - 1) (d - 1) := by
    apply Nat.choose_pos
    omega
  have hM : 0 < (1 / (2 : ℝ) ^ (n + 2 * d)) *
      Nat.choose (n + d - 1) (d - 1) := by
    apply mul_pos
    · positivity
    · exact_mod_cast hchoose
  apply Prefix.finite_good_fraction_lower (fun q : MidpointGridIndex d n =>
      nativeLayerRowVariance q) hm
  · exact hM
  · intro q
    exact nativeLayerRowVariance_le hd q
  · exact hmean

end BrownianSharp
