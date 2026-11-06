import BrownianSharp.KolmogorovWidth
import BrownianSharp.TheoremFFiniteDimensionalCovering
import Mathlib.Tactic

open scoped BigOperators

namespace HaarQuarter.TheoremF.Carl

open HaarQuarter.TheoremD.Width

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strict worst-case error bound yields a pointwise approximant at every point of `K`. -/
theorem exists_pointwise_approximation
    (K : Set X) (V : Submodule ℝ X) {r : ENNReal}
    (h : approximationError K V < r) :
    ∀ x ∈ K, ∃ v : V, edist x v < r := by
  intro x hx
  have hsup := iSup_lt_iff.mp (by simpa [approximationError] using h)
  rcases hsup with ⟨b, hbr, hle⟩
  have hdist : Metric.infEDist x (V : Set X) < r :=
    lt_of_le_of_lt (hle ⟨x, hx⟩) hbr
  rcases Metric.infEDist_lt_iff.mp hdist with ⟨v, hv, hxr⟩
  exact ⟨⟨v, hv⟩, by simpa [edist_comm] using hxr⟩

/-- Real-norm form of the strict pointwise approximation consequence. -/
theorem exists_pointwise_norm_approximation
    (K : Set X) (V : Submodule ℝ X) {r : ℝ} (hr : 0 < r)
    (h : approximationError K V < ENNReal.ofReal r) :
    ∀ x ∈ K, ∃ v : V, ‖x - (v : X)‖ < r := by
  intro x hx
  obtain ⟨v, hdist⟩ := exists_pointwise_approximation K V h x hx
  have hdist' : ENNReal.ofReal ‖x - (v : X)‖ < ENNReal.ofReal r := by
    simpa [edist_dist, dist_eq_norm] using hdist
  exact ⟨v, (ENNReal.ofReal_lt_ofReal_iff hr).mp hdist'⟩

end HaarQuarter.TheoremF.Carl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A subspace of finite cardinal rank is finite-dimensional, using rank rather
than `finrank` so that the infinite-dimensional ambient-space case is excluded. -/
theorem finiteDimensional_of_rank_le
    (V : Submodule ℝ X) {n : ℕ} (hV : Module.rank ℝ V ≤ (n : Cardinal)) :
    FiniteDimensional ℝ V := by
  have hlt : Module.rank ℝ V < Cardinal.aleph0 :=
    lt_of_le_of_lt hV Cardinal.natCast_lt_aleph0
  exact Module.rank_lt_aleph0_iff.mp hlt

namespace HaarQuarter.TheoremF.PackingWidth

open HaarQuarter.TheoremD.Width
open HaarQuarter.TheoremF.Carl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end HaarQuarter.TheoremF.PackingWidth
