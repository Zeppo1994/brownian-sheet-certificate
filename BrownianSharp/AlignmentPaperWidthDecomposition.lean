import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.AlignmentScaledSetWidth
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! Approximation from two endpoint classes. The decomposition hypothesis is
an input only to this generic lemma; applications must prove it for their
actual classes before using it. No interpolation theorem is assumed. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperWidthDecomposition

open HaarQuarter.TheoremD.Width

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Adding approximating subspaces adds their dimension budgets and errors. -/
theorem width_upper_of_endpoint_decomposition
    (K K₀ K₁ : Set X) (m n : ℕ) (A B E₀ E₁ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hdecomp : ∀ x ∈ K, ∃ u ∈ K₀, ∃ v ∈ K₁, x = A • u + B • v)
    (h₀ : kolmogorovWidth K₀ m ≤ ENNReal.ofReal E₀)
    (h₁ : kolmogorovWidth K₁ n ≤ ENNReal.ofReal E₁) :
    kolmogorovWidth K (m + n) ≤ ENNReal.ofReal (A * E₀ + B * E₁) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hfinite
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  let δ : ℝ := (ε : ℝ) / (2 * (A + B))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR₀ : 0 < E₀ + δ := by positivity
  have hR₁ : 0 < E₁ + δ := by positivity
  have hstrict₀ : kolmogorovWidth K₀ m < ENNReal.ofReal (E₀ + δ) :=
    h₀.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR₀).2 (by linarith))
  have hstrict₁ : kolmogorovWidth K₁ n < ENNReal.ofReal (E₁ + δ) :=
    h₁.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR₁).2 (by linarith))
  obtain ⟨V₀, hV₀, ha₀⟩ :=
    BrownianSharp.Carl.exists_width_subspace_pointwise_approximation K₀ m hR₀ hstrict₀
  obtain ⟨V₁, hV₁, ha₁⟩ :=
    BrownianSharp.Carl.exists_width_subspace_pointwise_approximation K₁ n hR₁ hstrict₁
  let W : Submodule ℝ X := V₀ ⊔ V₁
  have hW : Module.rank ℝ W ≤ ((m + n : ℕ) : Cardinal) := by
    calc
      Module.rank ℝ W ≤ Module.rank ℝ V₀ + Module.rank ℝ V₁ :=
        Submodule.rank_add_le_rank_add_rank V₀ V₁
      _ ≤ (m : Cardinal) + (n : Cardinal) := add_le_add hV₀ hV₁
      _ = ((m + n : ℕ) : Cardinal) := by simp
  have hpoint : ∀ x ∈ K, ∃ w ∈ W,
      ‖x - w‖ ≤ A * (E₀ + δ) + B * (E₁ + δ) := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hdecomp x hx
    obtain ⟨u', hu'⟩ := ha₀ u hu
    obtain ⟨v', hv'⟩ := ha₁ v hv
    have hAu : A • (u' : X) ∈ W :=
      (show V₀ ≤ W from le_sup_left) (V₀.smul_mem A u'.property)
    have hBv : B • (v' : X) ∈ W :=
      (show V₁ ≤ W from le_sup_right) (V₁.smul_mem B v'.property)
    refine ⟨A • (u' : X) + B • (v' : X), W.add_mem hAu hBv, ?_⟩
    calc
      ‖A • u + B • v - (A • (u' : X) + B • (v' : X))‖ =
          ‖A • (u - (u' : X)) + B • (v - (v' : X))‖ := by
            congr 1
            module
      _ ≤ ‖A • (u - (u' : X))‖ + ‖B • (v - (v' : X))‖ :=
        norm_add_le _ _
      _ = A * ‖u - (u' : X)‖ + B * ‖v - (v' : X)‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hB]
      _ ≤ A * (E₀ + δ) + B * (E₁ + δ) :=
        add_le_add (mul_le_mul_of_nonneg_left hu'.le hA.le)
          (mul_le_mul_of_nonneg_left hv'.le hB.le)
  have hbound : kolmogorovWidth K (m + n) ≤
      ENNReal.ofReal (A * (E₀ + δ) + B * (E₁ + δ)) := by
    unfold kolmogorovWidth
    refine (iInf_le _ ⟨W, hW⟩).trans ?_
    exact BrownianSharp.AlignmentAmbientWidth.approximationError_le_of_pointwise
      K W (by positivity) hpoint
  have hreal : A * (E₀ + δ) + B * (E₁ + δ) =
      (A * E₀ + B * E₁) + (ε : ℝ) / 2 := by
    dsimp [δ]
    field_simp
    ring
  have hhalf : ENNReal.ofReal ((ε : ℝ) / 2) ≤ (ε : ENNReal) := by
    calc
      ENNReal.ofReal ((ε : ℝ) / 2) ≤ ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = (ε : ENNReal) := by simp
  calc
    kolmogorovWidth K (m + n) ≤
        ENNReal.ofReal (A * (E₀ + δ) + B * (E₁ + δ)) := hbound
    _ = ENNReal.ofReal (A * E₀ + B * E₁) +
        ENNReal.ofReal ((ε : ℝ) / 2) := by
          rw [hreal, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (A * E₀ + B * E₁) + ε :=
      add_le_add le_rfl hhalf

end BrownianSharp.AlignmentPaperWidthDecomposition
