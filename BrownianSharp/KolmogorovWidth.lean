import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Bounded

/-!
An extended-nonnegative-real version of the Kolmogorov width. It is the
supremum, over points of `K`, of the infimum distance to a candidate linear
subspace, followed by the infimum over subspaces of dimension at most `m`.
For compact `K` this has the same finite value as the manuscript's
real-valued formula after taking `ENNReal.toReal`; the conversion is not
formalized in this module.
-/

namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Worst-case distance of a set `K` to a linear subspace `V`. -/
noncomputable def approximationError (K : Set X) (V : Submodule ℝ X) : ENNReal :=
  ⨆ x : {x : X // x ∈ K}, Metric.infEDist x.1 (V : Set X)

/-- Kolmogorov width: infimum of worst-case approximation error over linear
subspaces of dimension at most `m`. The cardinal-valued rank bound is used
instead of `finrank`, since Lean defines `finrank` to be zero at infinite
rank. -/
noncomputable def kolmogorovWidth (K : Set X) (m : ℕ) : ENNReal :=
  ⨅ V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)},
    approximationError K V.1

/-- Kolmogorov widths are nonincreasing in the allowed dimension. This is
the monotonicity step used when the Carl inequality's `d_{j-1}` is bounded by
`d_m` for `j > m+1`. -/
theorem kolmogorovWidth_antitone (K : Set X) {m n : ℕ} (hmn : m ≤ n) :
    kolmogorovWidth K n ≤ kolmogorovWidth K m := by
  unfold kolmogorovWidth
  apply le_iInf
  intro V
  have hmn' : (m : Cardinal) ≤ (n : Cardinal) := by exact_mod_cast hmn
  exact iInf_le (fun W : {W : Submodule ℝ X // Module.rank ℝ W ≤ (n : Cardinal)} =>
      approximationError K W.1)
    ⟨V.1, le_trans V.2 hmn'⟩

end HaarQuarter.TheoremD.Width

/-!
Real-valued interface for the extended-real Kolmogorov width in
`KolmogorovWidth.lean`. This interface is intended to connect the width
monotonicity lemma to the real-valued numerical extraction.
-/

namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- At dimension zero, the only admissible linear subspace is `{0}`, so the
width is exactly the worst-case distance to the zero subspace. -/
theorem kolmogorovWidth_zero_eq_bot (K : Set X) :
    kolmogorovWidth K 0 = approximationError K ⊥ := by
  unfold kolmogorovWidth
  apply le_antisymm
  · exact iInf_le (fun V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (0 : Cardinal)} =>
      approximationError K V.1) ⟨⊥, by simp⟩
  · apply le_iInf
    intro V
    have hrank : Module.rank ℝ V.1 = 0 := by
      exact le_antisymm V.2 zero_le
    have hsub : Subsingleton V.1 := rank_zero_iff.mp hrank
    have hV : V.1 = (⊥ : Submodule ℝ X) := by
      apply le_antisymm
      · intro x hx
        change x = 0
        have hx' : (⟨x, hx⟩ : V.1) = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val hx'
      · exact bot_le
    rw [hV]

end HaarQuarter.TheoremD.Width

namespace HaarQuarter.TheoremD.Width

set_option maxHeartbeats 500000

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end HaarQuarter.TheoremD.Width
