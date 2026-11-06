import BrownianSharp.AlignmentMaternScalarFeature

noncomputable section
namespace BrownianSharp.AlignmentPaperMaternRealPhase

def realPhaseProjection : ℂ→L[ℝ]ℝ:=Complex.reCLM+Complex.imCLM

theorem realPhaseProjection_norm_le (z:ℂ):‖realPhaseProjection z‖≤2*‖z‖:=by
  change |z.re+z.im|≤2*‖z‖
  exact (abs_add_le _ _).trans (by
    linarith [Complex.abs_re_le_norm z,Complex.abs_im_le_norm z])

theorem realPhaseProjection_exp (x:ℝ):
    realPhaseProjection (Complex.exp (Complex.I*x))=Real.cos x+Real.sin x:=by
  change (Complex.exp (Complex.I*x)).re+(Complex.exp (Complex.I*x)).im=_
  rw [mul_comm Complex.I,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]

theorem scalarPhase_eq_projection (t ξ:ℝ):
    AlignmentMaternScalarFeature.scalarPhase t ξ=
      realPhaseProjection (Complex.exp (Complex.I*((2*Real.pi*t*ξ:ℝ):ℂ))) := by
  rw [realPhaseProjection_exp]
  unfold AlignmentMaternScalarFeature.scalarPhase
  congr 1 <;> congr 1 <;> ring

/-- A complex Fourier phase approximation projects to the actual real
cosine-plus-sine feature with at most twice its error. -/
theorem scalarPhase_error_le (t ξ:ℝ) (z:ℂ):
    |AlignmentMaternScalarFeature.scalarPhase t ξ-realPhaseProjection z|≤
      2*‖Complex.exp (Complex.I*((2*Real.pi*t*ξ:ℝ):ℂ))-z‖ := by
  have h:=realPhaseProjection_norm_le
    (Complex.exp (Complex.I*((2*Real.pi*t*ξ:ℝ):ℂ))-z)
  rw [map_sub,←scalarPhase_eq_projection,Real.norm_eq_abs] at h
  exact h

end BrownianSharp.AlignmentPaperMaternRealPhase
