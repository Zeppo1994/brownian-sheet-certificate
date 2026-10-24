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

/-- Any unit-norm dual functional that annihilates an approximating subspace
controls the distance to that subspace. This turns such dual estimates into
an actual width bound. -/
theorem image_unitBall_width_le_of_dual_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : ℕ}
    (T : H →L[ℝ] PiLp ∞ (fun _ : Fin M => ℝ))
    (K : Set (PiLp ∞ (fun _ : Fin M => ℝ)))
    (V : Submodule ℝ (PiLp ∞ (fun _ : Fin M => ℝ))) (m : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hVrank : Module.rank ℝ V ≤ (m : Cardinal))
    (hVclosed : IsClosed (V : Set (PiLp ∞ (fun _ : Fin M => ℝ))))
    (hK : ∀ y ∈ K, ∃ x : H, ‖x‖ ≤ 1 ∧ T x = y)
    (hdual : ∀ φ : StrongDual ℝ (PiLp ∞ (fun _ : Fin M => ℝ)),
      (∀ v ∈ V, φ v = 0) → ‖φ‖ ≤ 1 →
        ∀ x : H, ‖x‖ ≤ 1 → |φ (T x)| ≤ C) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth K m ≤ ENNReal.ofReal C := by
  letI : IsClosed (V : Set (PiLp ∞ (fun _ : Fin M => ℝ))) := hVclosed
  have herror : HaarQuarter.TheoremD.Width.approximationError K V ≤ ENNReal.ofReal C := by
    unfold HaarQuarter.TheoremD.Width.approximationError
    apply iSup_le
    intro y
    obtain ⟨x, hxnorm, hy⟩ := hK y.1 y.2
    rw [← hy]
    have hdist := infDist_le_of_annihilator_bound V (T x) hC
      (fun φ hφ hφnorm => hdual φ hφ hφnorm x hxnorm)
    exact (ENNReal.le_ofReal_iff_toReal_le
      (Metric.infEDist_ne_top ⟨0, V.zero_mem⟩) hC).2 hdist
  unfold HaarQuarter.TheoremD.Width.kolmogorovWidth
  exact (iInf_le _ ⟨V, hVrank⟩).trans herror

/-- A dictionary synthesis bound on the annihilator of `Wᗮ` yields an actual
Kolmogorov width upper bound for a set represented by the image of the source
unit ball.  `B` is the adjoint/synthesis map; `hAdj` records the exact finite
pairing identity, while `hB` is the Kashin-type estimate supplied by the
finite-matrix argument. -/
theorem image_width_le_of_adjoint_synthesis_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] {M : ℕ}
    (T : H →L[ℝ] PiLp ∞ (fun _ : Fin M => ℝ))
    (B : (Fin M → ℝ) →ₗ[ℝ] H) (W : Submodule ℝ H)
    (K : Set (PiLp ∞ (fun _ : Fin M => ℝ))) (m : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ y ∈ K, ∃ x : H, ‖x‖ ≤ 1 ∧ T x = y)
    (hVrank : Module.rank ℝ (orthogonalImageSubspace M T W) ≤ (m : Cardinal))
    (hVclosed : IsClosed (orthogonalImageSubspace M T W :
      Set (PiLp ∞ (fun _ : Fin M => ℝ))))
    (hAdj : ∀ x (coeff : Fin M → ℝ),
      (∑ i : Fin M, coeff i * (T x) i) = inner ℝ x (B coeff))
    (hB : ∀ coeff : Fin M → ℝ, (∑ i : Fin M, |coeff i|) ≤ 1 →
      B coeff ∈ W → ‖B coeff‖ ≤ C) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth K m ≤ ENNReal.ofReal C := by
  let V := orthogonalImageSubspace M T W
  letI : IsClosed (V : Set (PiLp ∞ (fun _ : Fin M => ℝ))) := hVclosed
  have hdual : ∀ φ : StrongDual ℝ (PiLp ∞ (fun _ : Fin M => ℝ)),
      (∀ v ∈ V, φ v = 0) → ‖φ‖ ≤ 1 →
        ∀ x : H, ‖x‖ ≤ 1 → |φ (T x)| ≤ C := by
    intro φ hφ hφnorm x hx
    let coeff : Fin M → ℝ := fun i => φ (PiLp.single ∞ i 1)
    have hcoeff : (∑ i : Fin M, |coeff i|) ≤ 1 := by
      calc
        _ ≤ ‖φ‖ := sum_abs_coordinate_coefficients_le_dual_norm φ
        _ ≤ 1 := hφnorm
    have hBmem : B coeff ∈ W := by
      have horth : B coeff ∈ Wᗮᗮ := by
        apply (Submodule.mem_orthogonal' _ _).2
        intro z hz
        have hTz : T z ∈ V := by
          apply LinearMap.mem_range.mpr
          exact ⟨⟨z, hz⟩, rfl⟩
        have hzero : φ (T z) = 0 := hφ (T z) hTz
        have hcoord := strongDual_apply_eq_sum_coordinates φ (T z)
        have hpair := hAdj z coeff
        calc
          inner ℝ (B coeff) z = inner ℝ z (B coeff) := real_inner_comm _ _
          _ = ∑ i : Fin M, coeff i * (T z) i := hpair.symm
          _ = φ (T z) := by simpa [coeff] using hcoord.symm
          _ = 0 := hzero
      simpa [Submodule.orthogonal_orthogonal] using horth
    have hBnorm := hB coeff hcoeff hBmem
    have hpair := hAdj x coeff
    have hcoord := strongDual_apply_eq_sum_coordinates φ (T x)
    have hφvalue : φ (T x) = inner ℝ x (B coeff) := by
      calc
        φ (T x) = ∑ i : Fin M, coeff i * (T x) i := by simpa [coeff] using hcoord
        _ = inner ℝ x (B coeff) := hpair
    rw [hφvalue]
    calc
      |inner ℝ x (B coeff)| ≤ ‖x‖ * ‖B coeff‖ := abs_real_inner_le_norm x (B coeff)
      _ ≤ 1 * C := mul_le_mul hx hBnorm (norm_nonneg _) (by norm_num)
      _ = C := one_mul _
  exact image_unitBall_width_le_of_dual_bound T K V m hC hVrank hVclosed hK hdual

end BrownianSharp.KGGFiniteDuality
