import BrownianSharp.AlignmentExponentialGradedReverseInversion

namespace BrownianSharp.AlignmentGaussianGradedReverseClosure

open BrownianSharp.AlignmentExponentialGradedReverseInversion

noncomputable section

/-- The small-ball logarithmic rate corresponding to a source decay exponent
`β` and grade multiplicity `d`. -/
def gradedLogRate (β : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow ε⁻¹ (2/β) *
    Real.rpow (Real.log ε⁻¹) ((d:ℝ)-1+(d:ℝ)/β)

/-- Monotonicity transfers a dyadic lower probability bound to the matching
small-ball upper-log rate for arbitrary positive `β`. -/
theorem uniform_upperLog_of_dyadic_probability_lower
    (d N₀ : ℕ) (hd : 2≤d) (A B β : ℝ)
    (hA : 0<A) (hB : 0<B) (hβ : 0<β) :
    ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
      ∀p : ℝ→ℝ,
        (∀x y,0<x → x≤y → p x≤p y) →
        (∀N : ℕ,N₀≤N →
          Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)))≤p (radiusProfile β d A N)) →
        ∀ε : ℝ,0<ε → ε≤ε₀ → -Real.log (p ε)≤C*gradedLogRate β d ε := by
  obtain ⟨δ,D,hδ,hD,hindex⟩ := exists_dyadic_radius_index d N₀ hd hA hβ
  let ε₀ := min δ (Real.exp (-1)/2)
  refine ⟨B*D,ε₀,mul_pos hB hD,lt_min hδ (by positivity),?_,?_⟩
  · exact (min_le_right _ _).trans_lt (by have h := Real.exp_pos (-1); linarith)
  intro p hmono hdyadic ε hε hsmall
  obtain ⟨N,hN,hradius,hcost⟩ := hindex ε hε (hsmall.trans (min_le_left _ _))
  have hradpos : 0<radiusProfile β d A N := by
    unfold radiusProfile
    positivity
  have hp := (hdyadic N hN).trans (hmono _ _ hradpos hradius)
  have hlog := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlog
  have hbound : -Real.log (p ε)≤B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)) := by linarith
  apply hbound.trans
  have h := mul_le_mul_of_nonneg_left hcost hB.le
  simpa only [gradedLogRate,mul_assoc] using h

end
end BrownianSharp.AlignmentGaussianGradedReverseClosure
