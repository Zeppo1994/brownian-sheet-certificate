import BrownianSharp.Alignment

/-!
# Information budget from the likelihood and score identities

Source: unrestricted quarter-gain proof, Section 4, Lemma T1.
An elementary log inequality yields the sufficient bound `KL ≤ V` instead of
the source's sharper `KL ≤ (8/15) V`. This changes only an intermediate
constant, not the gain exponent or the target theorem's free prefactor.
The actual stopped law's likelihood/score identities remain explicit inputs.
-/

open scoped BigOperators

namespace HaarQuarter

theorem information_budget_from_score {ι J : Type*} [Fintype ι] [Fintype J]
    (P Q : PositiveLaw ι) (e f : J → ι → ℝ) (V : ℝ)
    (hpositive : ∀ u x, 0 < 1 + e u x * f u x)
    (hlikelihood : ∀ x, Real.log (P.mass x / Q.mass x) =
      ∑ u, Real.log (1 + e u x * f u x))
    (hscore : ∀ u, mean P (fun x => e u x * f u x) = mean P (fun x => (f u x) ^ 2))
    (henergy : ∀ x, ∑ u, (f u x) ^ 2 ≤ V) :
    relativeEntropy P Q ≤ V := by
  have hpoint : ∀ x, Real.log (P.mass x / Q.mass x) ≤ ∑ u, e u x * f u x := by
    intro x
    rw [hlikelihood]
    apply Finset.sum_le_sum
    intro u hu
    have h := Real.log_le_sub_one_of_pos (hpositive u x)
    linarith
  calc
    _ = mean P (fun x => Real.log (P.mass x / Q.mass x)) := rfl
    _ ≤ mean P (fun x => ∑ u, e u x * f u x) := mean_mono P hpoint
    _ = ∑ u, mean P (fun x => (f u x) ^ 2) := by rw [mean_sum]; simp_rw [hscore]
    _ = mean P (fun x => ∑ u, (f u x) ^ 2) := (mean_sum P _).symm
    _ ≤ mean P (fun _ => V) := mean_mono P henergy
    _ = V := mean_const P V

end HaarQuarter
