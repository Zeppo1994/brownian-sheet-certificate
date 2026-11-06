import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic
import BrownianSharp.KolmogorovWidth

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-!
# A finite-dimensional quotient-duality bridge for KGG widths

The key analytic fact is the normed quotient/Hahn--Banach identity: distance to
a closed subspace is controlled by all norm-one functionals annihilating it.
This is the abstract part of converting a Kashin nullspace estimate into an
ambient Kolmogorov-width estimate.  The special coordinate identification of
the dual of `ℓ∞` with `ℓ¹` is kept separate so that later arguments can reuse
the quotient lemma for general finite-dimensional maps.
-/

open Set
open scoped ENNReal
open scoped RealInnerProductSpace

namespace BrownianSharp.KGGFiniteDuality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If every unit dual functional annihilating `W` is bounded by `C` at `x`,
then the distance from `x` to `W` is at most `C`.  The proof factors through
the normed quotient and applies Hahn--Banach to its quotient class. -/
theorem infDist_le_of_annihilator_bound
    (W : Submodule ℝ E) [hW : IsClosed (W : Set E)] (x : E) {C : ℝ}
    (hC : 0 ≤ C)
    (hdual : ∀ φ : StrongDual ℝ E,
      (∀ w ∈ W, φ w = 0) → ‖φ‖ ≤ 1 → |φ x| ≤ C) :
    Metric.infDist x (W : Set E) ≤ C := by
  let q : E ⧸ W := W.mkQ x
  by_cases hq : ‖q‖ = 0
  · have hdist : Metric.infDist x (W : Set E) = 0 := by
      have hqx : ‖(W.mkQ x : E ⧸ W)‖ = 0 := by simpa [q] using hq
      have hxW : x ∈ W := (QuotientAddGroup.norm_mk_eq_zero (m := x)).mp hqx
      exact Metric.infDist_zero_of_mem hxW
    rw [hdist]
    exact hC
  · obtain ⟨ψ, hψnorm, hψq⟩ := exists_dual_vector ℝ q hq
    let φ : StrongDual ℝ E := ψ.comp W.mkQL
    have hφann : ∀ w ∈ W, φ w = 0 := by
      intro w hw
      have hz : W.mkQ w = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero (p := W) (x := w)).2 hw
      simp [φ, hz]
    have hqop : ‖W.mkQL‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro z
      rw [Submodule.mkQL_apply]
      calc
        ‖Submodule.mkQ W z‖ ≤ ‖z‖ := Submodule.Quotient.norm_mk_le W z
        _ = 1 * ‖z‖ := by ring
    have hφnorm : ‖φ‖ ≤ 1 := by
      calc
        ‖φ‖ ≤ ‖ψ‖ * ‖W.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 := by rw [hψnorm]; simpa using hqop
    have hvalue := hdual φ hφann hφnorm
    have hqnorm : ‖q‖ = Metric.infDist x (W : Set E) := by
      change ‖(x : E ⧸ W.toAddSubgroup)‖ =
        Metric.infDist x (W.toAddSubgroup : Set E)
      exact QuotientAddGroup.norm_mk x
    have hvalueEq : φ x = Metric.infDist x (W : Set E) := by
      calc
        φ x = ψ q := by simp [φ, q]
        _ = ‖q‖ := hψq
        _ = Metric.infDist x (W : Set E) := hqnorm
    rw [hvalueEq, abs_of_nonneg (Metric.infDist_nonneg)] at hvalue
    exact hvalue

end BrownianSharp.KGGFiniteDuality

namespace BrownianSharp.KGGFiniteDuality

variable {M : ℕ}

/-- A functional on a finite `ℓ∞` product is determined by its values on the
coordinate vectors. -/
theorem strongDual_apply_eq_sum_coordinates (φ : StrongDual ℝ (PiLp ∞ (fun _ : Fin M => ℝ)))
    (y : PiLp ∞ (fun _ : Fin M => ℝ)) :
    φ y = ∑ i : Fin M, φ (PiLp.single ∞ i 1) * y i := by
  have hy : y = ∑ i : Fin M, y i • PiLp.single ∞ i 1 := by
    ext j
    change (PiLp.proj (p := ∞) (𝕜 := ℝ) (β := fun _ : Fin M => ℝ) j) y =
      (PiLp.proj (p := ∞) (𝕜 := ℝ) (β := fun _ : Fin M => ℝ) j)
        (∑ i : Fin M, y i • PiLp.single ∞ i 1)
    rw [map_sum]
    simp [PiLp.single_apply, Pi.single_apply]
  calc
    φ y = φ (∑ i : Fin M, y i • PiLp.single ∞ i 1) := congrArg φ hy
    _ = ∑ i : Fin M, y i * φ (PiLp.single ∞ i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : Fin M, φ (PiLp.single ∞ i 1) * y i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The coefficients of a functional on a finite `ℓ∞` product have `ℓ¹`
norm at most its operator norm.  The sign vector attains the sum of absolute
coefficient values and has `ℓ∞` norm at most one. -/
theorem sum_abs_coordinate_coefficients_le_dual_norm
    (φ : StrongDual ℝ (PiLp ∞ (fun _ : Fin M => ℝ))) :
    (∑ i : Fin M, |φ (PiLp.single ∞ i 1)|) ≤ ‖φ‖ := by
  let coeff : Fin M → ℝ := fun i => φ (PiLp.single ∞ i 1)
  let s : PiLp ∞ (fun _ : Fin M => ℝ) := WithLp.toLp ∞ fun i => if coeff i < 0 then -1 else 1
  have hs : ‖s‖ ≤ 1 := by
    by_cases hM : M = 0
    · subst M
      simp [s, PiLp.norm_eq_ciSup]
    · letI : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero hM⟩⟩
      rw [PiLp.norm_eq_ciSup]
      apply ciSup_le
      intro i
      simp only [s, PiLp.toLp_apply]
      split_ifs <;> norm_num
  have hsign : φ s = ∑ i : Fin M, |coeff i| := by
    rw [strongDual_apply_eq_sum_coordinates]
    dsimp [s]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : coeff i < 0
    · simp [coeff, h, abs_of_neg h]
    · have hnonneg : 0 ≤ coeff i := le_of_not_gt h
      simp [coeff, h, abs_of_nonneg hnonneg]
  have hφs : ‖φ s‖ ≤ ‖φ‖ := by
    calc
      ‖φ s‖ ≤ ‖φ‖ * ‖s‖ := φ.le_opNorm s
      _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = ‖φ‖ := mul_one _
  have habs : |φ s| ≤ ‖φ‖ := by simpa [Real.norm_eq_abs] using hφs
  rw [hsign] at habs
  have hsum_nonneg : 0 ≤ ∑ i : Fin M, |coeff i| := Finset.sum_nonneg fun i hi => abs_nonneg _
  simpa [coeff, abs_of_nonneg hsum_nonneg] using habs

/-- The approximating space induced by the orthogonal complement of a kernel
subspace in the source Hilbert space. -/
noncomputable def orthogonalImageSubspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : ℕ)
    (T : H →L[ℝ] PiLp ∞ (fun _ : Fin M => ℝ)) (W : Submodule ℝ H) :
    Submodule ℝ (PiLp ∞ (fun _ : Fin M => ℝ)) :=
  LinearMap.range (T.toLinearMap.comp Wᗮ.subtype)

end BrownianSharp.KGGFiniteDuality
