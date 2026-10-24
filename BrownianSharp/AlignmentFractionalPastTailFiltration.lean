import BrownianSharp.AlignmentFractionalHilbertTaylor
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Tactic

/-! A nested finite source filtration for the coarse-plus-dyadic-shell Taylor
models used for the MvN past tail. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentFractionalPastTailFiltration

open BrownianSharp.AlignmentFractionalHilbertTaylor
open HaarQuarter.TheoremD.Width

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The permanent address of one of the two coarse pieces or one of the four
refined pieces in a dyadic shell. -/
inductive PastTailTaylorIndex
  | coarse : Fin 4 → PastTailTaylorIndex
  | shell : ℕ → Fin 4 → PastTailTaylorIndex
  deriving DecidableEq

/-- Embed the finite depth-`J` address into the permanent address type. -/
def embedIndex (J : ℕ) : Option (Fin J) × Fin 4 → PastTailTaylorIndex
  | (none,i) => .coarse i
  | (some j,i) => .shell j.val i

/-- All source coefficient vectors through shell depth `J` and Taylor order
`M`, placed in one finite-dimensional subspace. -/
def pastTailTaylorSpan (J M : ℕ)
    (v : PastTailTaylorIndex → ℕ → H) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun p :
    ULift.{u} ((Option (Fin J) × Fin 4) × Fin M) =>
      v (embedIndex J p.down.1) p.down.2.val))

theorem pastTailTaylorSpan_rank_le (J M : ℕ)
    (v : PastTailTaylorIndex → ℕ → H) :
    Module.rank ℝ (pastTailTaylorSpan J M v) ≤
      (((4*(J+1))*M : ℕ) : Cardinal) := by
  classical
  unfold pastTailTaylorSpan
  calc
    Module.rank ℝ (Submodule.span ℝ (Set.range (fun p :
        ULift.{u} ((Option (Fin J) × Fin 4) × Fin M) =>
          v (embedIndex J p.down.1) p.down.2.val)) ) ≤
        Cardinal.mk (Set.range (fun p :
          ULift.{u} ((Option (Fin J) × Fin 4) × Fin M) =>
            v (embedIndex J p.down.1) p.down.2.val)) := rank_span_le _
    _ ≤ Cardinal.mk (ULift.{u} ((Option (Fin J) × Fin 4) × Fin M)) :=
      Cardinal.mk_range_le
    _ = (((4*(J+1))*M : ℕ) : Cardinal) := by
      simp [Cardinal.mk_fintype, Nat.mul_comm, Nat.add_comm]

theorem pastTailTaylorSpan_mono (v : PastTailTaylorIndex → ℕ → H)
    {J J' M M' : ℕ} (hJ : J ≤ J') (hM : M ≤ M') :
    pastTailTaylorSpan J M v ≤ pastTailTaylorSpan J' M' v := by
  classical
  apply Submodule.span_mono
  rintro z ⟨⟨⟨i,k⟩⟩,rfl⟩
  rcases i with ⟨j,a⟩
  rcases j with _ | j
  · exact ⟨⟨⟨(none,a), Fin.castLE hM k⟩⟩, rfl⟩
  · refine ⟨⟨⟨(some (Fin.castLE hJ j),a), Fin.castLE hM k⟩⟩, ?_⟩
    simp [embedIndex]

/-- The generic weighted Taylor estimate specialized to the permanent shell
addresses, with the coefficient span shared by all parameters. -/
theorem pastTailTaylor_family_width
    (J M : ℕ) (v : PastTailTaylorIndex → ℕ → H)
    (center : (Option (Fin J) × Fin 4) → ℝ)
    (weight : (Option (Fin J) × Fin 4) → ℝ → ℝ)
    (remainder : ℝ → ℝ) (K : ℝ → H) (A : Set ℝ)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hweights : ∀ t, t ∈ A → ∀ i, 0 ≤ weight i t)
    (hrem : ∀ t, t ∈ A → 0 ≤ remainder t)
    (hmass : ∀ t, t ∈ A →
      (∑ i : Option (Fin J) × Fin 4, weight i t)+remainder t=1)
    (hlocal : ∀ t, t ∈ A → ∀ i, weight i t ≠ 0 →
      ‖K t-localTaylor M (fun i k => v (embedIndex J i) k.val)
          center i t‖ ≤ δ)
    (htail : ∀ t, t ∈ A → remainder t ≠ 0 → ‖K t‖ ≤ η) :
    kolmogorovWidth (K '' A) ((4*(J+1))*M) ≤ ENNReal.ofReal (δ+η) := by
  have h := weighted_taylor_family_width M
    (fun i k => v (embedIndex J i) k.val) center weight remainder K A
    hδ hη hweights hrem hmass hlocal htail
  simpa [Fintype.card_option, Fintype.card_prod, Nat.mul_comm, Nat.add_comm] using h

end BrownianSharp.AlignmentFractionalPastTailFiltration
