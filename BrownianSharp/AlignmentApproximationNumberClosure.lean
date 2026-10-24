import BrownianSharp.AlignmentApproximationNumberProduct
import BrownianSharp.AlignmentApproximationNumberIdeal

/-! Infimum closure and product laws for strict-rank approximation numbers. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped ENNReal
namespace BrownianSharp.AlignmentApproximationNumberClosure
open AlignmentFractionalApproximationNumbers AlignmentApproximationNumberProduct
universe u
variable {X Y Z : Type u}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem approximationNumber_antitone (T : X →L[ℝ] Y) :
    Antitone (approximationNumber T) := by
  intro k l hkl
  change approximationNumber T l ≤
    ⨅ A : {A : X →L[ℝ] Y // Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal)}, ENNReal.ofReal ‖T-A.val‖
  apply le_iInf
  intro A
  exact approximationNumber_le_of_approximant T A.val
    (A.property.trans_le (by exact_mod_cast hkl))

theorem approximationNumber_le_of_arbitrarily_close_approximants
    (T : X →L[ℝ] Y) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ A : X →L[ℝ] Y,
        Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal) ∧
        ‖T-A‖ ≤ δ+ε) :
    approximationNumber T k ≤ ENNReal.ofReal δ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  have hεR : (0:ℝ) < ε := by exact_mod_cast hε
  obtain ⟨A,hA,herr⟩ := h ε hεR
  have hh := (approximationNumber_le_of_approximant T A hA).trans
    (ENNReal.ofReal_le_ofReal herr)
  simpa only [ENNReal.ofReal_add hδ ε.coe_nonneg,ENNReal.ofReal_coe_nnreal] using hh

theorem approximationNumber_product
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    approximationNumber (S.comp T) (m+n-1) ≤
      approximationNumber S m * approximationNumber T n := by
  classical
  have h0S : Module.rank ℝ (LinearMap.range (0 : Y →ₗ[ℝ] Z)) < (m : Cardinal) := by
    simpa using (show (0:Cardinal.{u}) < (m:Cardinal.{u}) by exact_mod_cast (show 0<m by omega))
  have h0T : Module.rank ℝ (LinearMap.range (0 : X →ₗ[ℝ] Y)) < (n : Cardinal) := by
    simpa using (show (0:Cardinal.{u}) < (n:Cardinal.{u}) by exact_mod_cast (show 0<n by omega))
  change approximationNumber (S.comp T) (m+n-1) ≤
    (⨅ A : {A : Y →L[ℝ] Z //
      Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) < (m : Cardinal)},
      ENNReal.ofReal ‖S-A.val‖) *
    (⨅ B : {B : X →L[ℝ] Y //
      Module.rank ℝ (LinearMap.range (B : X →ₗ[ℝ] Y)) < (n : Cardinal)},
      ENNReal.ofReal ‖T-B.val‖)
  apply ENNReal.le_iInf_mul_iInf
    (f:=fun A : {A : Y →L[ℝ] Z // Module.rank ℝ (LinearMap.range (A : Y →ₗ[ℝ] Z)) < (m : Cardinal)} => ENNReal.ofReal ‖S-A.val‖)
    (g:=fun B : {B : X →L[ℝ] Y // Module.rank ℝ (LinearMap.range (B : X →ₗ[ℝ] Y)) < (n : Cardinal)} => ENNReal.ofReal ‖T-B.val‖)
    (⟨⟨0,h0S⟩,ENNReal.ofReal_ne_top⟩)
    (⟨⟨0,h0T⟩,ENNReal.ofReal_ne_top⟩)
  intro A B
  have h := approximationNumber_comp_le_of_approximants S T A.val B.val hm hn A.property B.property
  simpa only [ENNReal.ofReal_mul (norm_nonneg _)] using h

end BrownianSharp.AlignmentApproximationNumberClosure
