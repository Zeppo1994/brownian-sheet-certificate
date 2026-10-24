import BrownianSharp.AlignmentCompactFeatureBall
import BrownianSharp.AlignmentFractionalSheetRKHS

/-! Compactness closes uniformly bounded finite source constructions. -/
noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace BrownianSharp.AlignmentFeatureSourceClosure
open AlignmentCompactFeatureBall AlignmentFractionalSheetRKHS

theorem exists_source_of_finite_approximations
    {d : ℕ} {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : C(HaarQuarter.BrownianCubeAnchor d,H)) (A : ℝ) (hA : 0 < A)
    (F : Finset I → H) (f : C(HaarQuarter.BrownianCubeAnchor d,ℝ))
    (hF : ∀ s, ‖F s‖ ≤ A)
    (hlim : Tendsto (fun s => featureOperator K (F s)) atTop (𝓝 f)) :
    ∃ z : H, ‖z‖ ≤ A ∧ featureOperator K z = f := by
  have hclosed := (featureBall_isCompact (A • K)).isClosed
  have hmem : ∀ s, featureOperator K (F s) ∈ featureBall (A • K) := by
    intro s
    refine ⟨A⁻¹ • F s,?_,?_⟩
    · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hA]
      calc
        A⁻¹ * ‖F s‖ ≤ A⁻¹*A := mul_le_mul_of_nonneg_left (hF s) (inv_pos.mpr hA).le
        _ = 1 := inv_mul_cancel₀ hA.ne'
    · ext t
      change inner ℝ (A⁻¹ • F s) (A • K t) = inner ℝ (K t) (F s)
      rw [real_inner_smul_left,real_inner_smul_right,real_inner_comm (F s)]
      field_simp
  have hf : f ∈ featureBall (A • K) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  obtain ⟨g,hg,hgf⟩ := hf
  refine ⟨A • g,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hA]
    nlinarith
  · rw [← hgf]
    ext t
    change inner ℝ (K t) (A • g) = inner ℝ g (A • K t)
    rw [real_inner_smul_right,real_inner_smul_right,real_inner_comm]

end BrownianSharp.AlignmentFeatureSourceClosure
