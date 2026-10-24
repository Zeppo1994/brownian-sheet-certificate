import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentPeriodicUpperReduction
import BrownianSharp.Carl
import Mathlib.Tactic

/-! Scalar dilation transfer for set widths and strict operator Kolmogorov numbers. -/
noncomputable section
open scoped ENNReal
open HaarQuarter.TheoremD.Width

namespace BrownianSharp.AlignmentScaledSetWidth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The image of a set under multiplication by a positive scalar. -/
def scalarImage (A : ℝ) (J : Set X) : Set X := (fun x : X => A • x) '' J

/-- Positive scalar dilation of a set multiplies its Kolmogorov width by at
most that scalar. The proof uses a near-minimizing subspace and scales that
subspace together with each pointwise approximant. -/
theorem kolmogorovWidth_scalarImage_le_of_bound
    (J : Set X) (m : ℕ) (A E : ℝ) (hA : 0 < A) (hE : 0 ≤ E)
    (hJ : kolmogorovWidth J m ≤ ENNReal.ofReal E) :
    kolmogorovWidth (scalarImage A J) m ≤ ENNReal.ofReal (A * E) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  let δ : ℝ := (ε : ℝ) / (2 * A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR : 0 < E + δ := by linarith
  have hstrict : kolmogorovWidth J m < ENNReal.ofReal (E + δ) := by
    calc
      kolmogorovWidth J m ≤ ENNReal.ofReal E := hJ
      _ < ENNReal.ofReal (E + δ) :=
        (ENNReal.ofReal_lt_ofReal_iff hR).2 (by linarith)
  obtain ⟨V, hV, happrox⟩ :=
    BrownianSharp.Carl.exists_width_subspace_pointwise_approximation
      J m hR hstrict
  let S : X →ₗ[ℝ] X :=
    { toFun := fun x => A • x
      map_add' := by intro x y; exact smul_add A x y
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, smul_smul]
        rw [mul_comm] }
  let W : Submodule ℝ X := V.map S
  have hW : Module.rank ℝ W ≤ (m : Cardinal) :=
    (rank_map_le S V).trans hV
  have hpoint : ∀ x ∈ scalarImage A J, ∃ w ∈ W,
      ‖x - w‖ ≤ A * (E + δ) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨v, hv⟩ := happrox y hy
    refine ⟨A • (v : X), Submodule.mem_map.mpr ⟨v, v.property, ?_⟩, ?_⟩
    · rfl
    · calc
        ‖A • y - A • (v : X)‖ = ‖A • (y - (v : X))‖ := by rw [smul_sub]
        _ = |A| * ‖y - (v : X)‖ := norm_smul A _
        _ = A * ‖y - (v : X)‖ := by rw [abs_of_pos hA]
        _ ≤ A * (E + δ) := mul_le_mul_of_nonneg_left hv.le hA.le
  have hscaled : kolmogorovWidth (scalarImage A J) m ≤
      ENNReal.ofReal (A * (E + δ)) := by
    unfold kolmogorovWidth
    refine (iInf_le _ ⟨W, hW⟩).trans ?_
    exact BrownianSharp.AlignmentAmbientWidth.approximationError_le_of_pointwise
      (scalarImage A J) W (mul_nonneg hA.le (le_of_lt hR)) hpoint
  have hreal : A * (E + δ) = A * E + (ε : ℝ) / 2 := by
    dsimp [δ]
    field_simp
  have hεhalf : ENNReal.ofReal ((ε : ℝ) / 2) ≤ (ε : ENNReal) := by
    calc
      ENNReal.ofReal ((ε : ℝ) / 2) ≤ ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = (ε : ENNReal) := by simp
  calc
    kolmogorovWidth (scalarImage A J) m ≤ ENNReal.ofReal (A * (E + δ)) := hscaled
    _ = ENNReal.ofReal (A * E) + ENNReal.ofReal ((ε : ℝ) / 2) := by
      rw [hreal, ENNReal.ofReal_add (mul_nonneg hA.le hE) (by positivity)]
    _ ≤ ENNReal.ofReal (A * E) + ε := add_le_add_right hεhalf (ENNReal.ofReal (A * E))

/-- Transfer a width estimate through a positive scalar image and a set
inclusion. -/
theorem kolmogorovWidth_le_of_subset_scalarImage
    {K J : Set X} (A E : ℝ) (hK : K ⊆ scalarImage A J) (m : ℕ) (hA : 0 < A) (hE : 0 ≤ E)
    (hJ : kolmogorovWidth J m ≤ ENNReal.ofReal E) :
    kolmogorovWidth K m ≤ ENNReal.ofReal (A * E) := by
  exact (BrownianSharp.AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set
      hK m).trans (kolmogorovWidth_scalarImage_le_of_bound J m A E hA hE hJ)

/-- Strict-index operator version, matching the manuscript's `dim V < k`
convention. -/
theorem operatorKolmogorovNumber_le_of_subset_scalarImage
    {K J : Set X} (A E : ℝ) (hK : K ⊆ scalarImage A J) {k : ℕ} (hk : 1 ≤ k) (hA : 0 < A) (hE : 0 ≤ E)
    (hJ : BrownianSharp.AlignmentOperatorNumbers.operatorKolmogorovNumber J k ≤
      ENNReal.ofReal E) :
    BrownianSharp.AlignmentOperatorNumbers.operatorKolmogorovNumber K k ≤
      ENNReal.ofReal (A * E) := by
  rw [BrownianSharp.AlignmentOperatorNumbers.operatorKolmogorovNumber_eq_width_pred K hk]
  apply kolmogorovWidth_le_of_subset_scalarImage A E hK (k - 1) hA hE
  rw [← BrownianSharp.AlignmentOperatorNumbers.operatorKolmogorovNumber_eq_width_pred J hk]
  exact hJ

end BrownianSharp.AlignmentScaledSetWidth

