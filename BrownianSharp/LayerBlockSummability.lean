import BrownianSharp.LayerBlockVariance
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic

/-! Coordinate factorization of the weighted target-scale series. The remaining
analytic estimate is reduced explicitly to one scalar geometric series. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.LayerBlockSummability

open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.LayerBlockVariance

/-- ENNReal tsum of a coordinate-product function on a finite natural
product factors into the product of coordinate tsums. -/
theorem tsum_pi_prod (d : ℕ) (f : Fin d → ℕ → ENNReal) :
    (∑' t : Fin d → ℕ, ∏ i : Fin d, f i (t i)) =
      ∏ i : Fin d, ∑' k : ℕ, f i k := by
  induction d with
  | zero => simp
  | succ d ih =>
      let e : ℕ × (Fin d → ℕ) ≃ (Fin (d+1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (d+1) => ℕ)
      rw [← e.tsum_eq (fun t : Fin (d+1) → ℕ => ∏ i : Fin (d+1), f i (t i))]
      have hfun : ∀ (k : ℕ) (u : Fin d → ℕ),
          (∏ i : Fin (d+1), f i (e (k,u) i)) =
            f 0 k * ∏ i : Fin d, f i.succ (u i) := by
        intro k u
        simp [e, Fin.consEquiv, Fin.cons, Fin.prod_univ_succ]
      calc
        (∑' c : ℕ × (Fin d → ℕ), ∏ i : Fin (d+1), f i (e c i)) =
            ∑' k : ℕ, ∑' u : Fin d → ℕ, ∏ i : Fin (d+1), f i (e (k,u) i) :=
          (by simpa using (ENNReal.tsum_prod
            (f := fun k u => ∏ i : Fin (d+1), f i (e (k,u) i))))
        _ = ∑' k : ℕ, f 0 k * ∑' u : Fin d → ℕ, ∏ i : Fin d, f i.succ (u i) := by
          simp_rw [hfun, ENNReal.tsum_mul_left]
        _ = ∑' k : ℕ, f 0 k * ∏ i : Fin d, ∑' m : ℕ, f i.succ m := by
          simp_rw [ih]
        _ = ∏ i : Fin (d+1), ∑' k : ℕ, f i k := by
          rw [Fin.prod_univ_succ, ← ENNReal.tsum_mul_right]

/-- One-coordinate weighted variance summand. -/
def scalarWeightedVariance (r : ℝ) (K : ℕ) (C : ℝ)
    (s k : ℕ) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ (2 * r * (k : ℝ)) *
    scalarVarianceEnvelope K C s k)

/-- Split-sum lemma for the low/high scalar envelope. The only analytic inputs
are the displayed pointwise estimates; all finite-prefix and translated-tail
bookkeeping is discharged here. -/
theorem scalarTsum_le_of_pointwise_split
    (s : ℕ) (q A B : ENNReal) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (f : ℕ → ENNReal)
    (hlow : ∀ k, k ≤ s → f k ≤ A * (1 / 2 : ENNReal) ^ (s - k))
    (hhigh : ∀ k, s < k → f k ≤ B * q ^ (k - s)) :
    (∑' k : ℕ, f k) ≤ A * 2 + B * (q * (1 - q)⁻¹) := by
  let low : ℕ → ENNReal := fun k =>
    if k ≤ s then A * (1 / 2 : ENNReal) ^ (s - k) else 0
  let high : ℕ → ENNReal := fun k =>
    if s < k then B * q ^ (k - s) else 0
  have hpoint : ∀ k, f k ≤ low k + high k := by
    intro k
    by_cases hk : k ≤ s
    · simpa [low, high, hk, Nat.not_lt.mpr hk, one_div] using hlow k hk
    · have hsk : s < k := Nat.lt_of_not_ge hk
      simp [low, high, hk, hsk]
      exact hhigh k hsk
  have hsum := ENNReal.tsum_le_tsum hpoint
  have hlow_id : (∑' k : ℕ, low k) =
      A * ∑' k : {k : ℕ // k ≤ s}, (1 / 2 : ENNReal) ^ (s - k) := by
    calc
      _ = ∑' k : ℕ, A * (if k ≤ s then (1 / 2 : ENNReal) ^ (s-k) else 0) := by
        congr 1
        funext k
        simp [low]
      _ = A * ∑' k : ℕ, if k ≤ s then (1 / 2 : ENNReal) ^ (s-k) else 0 :=
        ENNReal.tsum_mul_left
      _ = A * ∑' k : {k : ℕ // k ≤ s}, (1 / 2 : ENNReal) ^ (s - k.1) := by
        congr 1
        have hseq : (fun k : ℕ => if k ≤ s then
            (1 / 2 : ENNReal) ^ (s-k) else 0) =
            (Set.Iic s).indicator (fun k => (1 / 2 : ENNReal) ^ (s-k)) := by
          funext k
          simp [Set.indicator_apply, Set.mem_Iic]
        rw [hseq, ← tsum_subtype (Set.Iic s)]
        rfl
  have hlow_bound : (∑' k : ℕ, low k) ≤ A * 2 := by
    rw [hlow_id]
    have hinj : Function.Injective
        (fun k : {k : ℕ // k ≤ s} => s - k.1) := by
      intro a b hab
      apply Subtype.ext
      change s - a.1 = s - b.1 at hab
      have ha := Nat.sub_add_cancel a.2
      have hb := Nat.sub_add_cancel b.2
      rw [hab] at ha
      omega
    calc
      A * ∑' k : {k : ℕ // k ≤ s}, (1 / 2 : ENNReal) ^ (s - k.1)
          ≤ A * ∑' n : ℕ, (1 / 2 : ENNReal) ^ n := by
            gcongr
            exact ENNReal.tsum_comp_le_tsum_of_injective hinj
              (fun n => (1 / 2 : ENNReal) ^ n)
      _ = A * 2 := by
            rw [ENNReal.tsum_geometric]
            norm_num
  have hhigh_id : (∑' k : ℕ, high k) =
      B * ∑' k : {k : ℕ // s < k}, q ^ (k.1 - s) := by
    calc
      _ = ∑' k : ℕ, B * (if s < k then q ^ (k-s) else 0) := by
        congr 1
        funext k
        simp [high]
      _ = B * ∑' k : ℕ, if s < k then q ^ (k-s) else 0 :=
        ENNReal.tsum_mul_left
      _ = B * ∑' k : {k : ℕ // s < k}, q ^ (k.1 - s) := by
        congr 1
        have hseq : (fun k : ℕ => if s < k then q ^ (k-s) else 0) =
            (Set.Ioi s).indicator (fun k => q ^ (k-s)) := by
          funext k
          simp [Set.indicator_apply, Set.mem_Ioi]
        rw [hseq, ← tsum_subtype (Set.Ioi s)]
        rfl
  have hhigh_bound : (∑' k : ℕ, high k) ≤ B * (q * (1 - q)⁻¹) := by
    rw [hhigh_id]
    let e : {k : ℕ // s < k} → ℕ := fun k => k.1 - (s + 1)
    have hinj : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      dsimp [e] at hab
      omega
    have hexp (k : {k : ℕ // s < k}) : k.1 - s = e k + 1 := by
      dsimp [e]
      omega
    calc
      B * ∑' k : {k : ℕ // s < k}, q ^ (k.1 - s)
          = B * ∑' k : {k : ℕ // s < k}, q ^ (e k + 1) := by
              congr 2
              funext k
              rw [hexp]
      _ ≤ B * ∑' n : ℕ, q ^ (n + 1) := by
            gcongr
            exact ENNReal.tsum_comp_le_tsum_of_injective hinj
              (fun n => q ^ (n + 1))
      _ = B * (q * (1 - q)⁻¹) := by
            rw [ENNReal.tsum_geometric_add_one]
  calc
    _ ≤ (∑' k : ℕ, low k) + ∑' k : ℕ, high k := by
      simpa [ENNReal.tsum_add] using hsum
    _ ≤ A * 2 + B * (q * (1 - q)⁻¹) := add_le_add hlow_bound hhigh_bound

/-- For a fixed source shape, the full target-scale series of the tensor
variance envelope factors exactly into one-dimensional weighted series. This
separates the difficult high-frequency estimate from all finite-dimensional
bookkeeping. -/
theorem shapeWeightedVariance_tsum_eq_prod
    (d K : ℕ) (C r : ℝ) (s : Fin d → ℕ) :
    (∑' t : Fin d → ℕ,
      ∏ i : Fin d, scalarWeightedVariance r K C (s i) (t i)) =
      ∏ i : Fin d, ∑' k : ℕ, scalarWeightedVariance r K C (s i) k :=
  tsum_pi_prod d (fun i k => scalarWeightedVariance r K C (s i) k)

/-- Explicit reduction theorem: if every scalar weighted envelope has bound
`B·2^(2rs)`, then the tensor target-scale series is bounded by the product of
those coordinate budgets. The hypothesis is only one-dimensional and is not
hidden inside the conclusion. -/
theorem shapeWeightedVariance_tsum_le
    (d K : ℕ) (C r B : ℝ) (hB : 0 ≤ B)
    (hscalar : ∀ s : ℕ,
      ∑' k : ℕ, scalarWeightedVariance r K C s k ≤
        ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (s : ℝ))))
    (s : Fin d → ℕ) :
    (∑' t : Fin d → ℕ,
      ∏ i : Fin d, scalarWeightedVariance r K C (s i) (t i)) ≤
      ∏ i : Fin d, ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (s i : ℝ))) := by
  rw [shapeWeightedVariance_tsum_eq_prod]
  apply Finset.prod_le_prod
  intro i hi
  exact hscalar (s i)

end BrownianSharp.LayerBlockSummability
