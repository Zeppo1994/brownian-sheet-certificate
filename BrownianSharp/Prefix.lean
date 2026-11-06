import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import BrownianSharp.HaarTensorGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Lean.Elab.Tactic.Omega
import BrownianSharp.QuarterScale
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Choose.Basic

/-!
Deterministic midpoint/prefix counting lemmas for the Brownian sharp small-ball
candidate.  This module isolates the finite combinatorics from any Gaussian
probability or concentration theorem.
-/

namespace BrownianSharp.Prefix

/-- Coordinatewise domination of a shape by a capped common-prefix vector. -/
def Below {d : ℕ} (r c : Fin d → ℕ) : Prop := ∀ i, r i ≤ c i

/-- Contradictory prefix mass cannot support a layer shape: a tuple below
`c` has total grade at most the total grade of `c`. -/
theorem no_shape_below_prefix_when_grade_exceeds {d : ℕ}
    (r c : Fin d → ℕ) (hrc : Below r c)
    {n : ℕ} (hr : (∑ i : Fin d, r i) = n)
    (hcn : (∑ i : Fin d, c i) < n) : False := by
  have hle : (∑ i : Fin d, r i) ≤ ∑ i : Fin d, c i :=
    Finset.sum_le_sum (fun i hi => hrc i)
  omega

/-- The mean/max split for a finite grid yields a deterministic lower bound
on the proportion above half the mean. This is the actual finite-set version
of the good-point extraction used for `A_n`. -/
theorem finite_good_fraction_lower {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hupper : ∀ x, f x ≤ M)
    (hmean : m ≤ (∑ x : α, f x) / (Fintype.card α : ℝ)) :
    m / (2 * M) ≤
      ((Finset.univ.filter (fun x => m / 2 ≤ f x)).card : ℝ) /
        (Fintype.card α : ℝ) := by
  classical
  let G : Finset α := Finset.univ.filter (fun x => m / 2 ≤ f x)
  have hcpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Classical.choice ‹Nonempty α›⟩)
  have hsum : (∑ x : α, f x) ≤
      (Fintype.card α : ℝ) * (m / 2) + (G.card : ℝ) * M := by
    calc
      (∑ x : α, f x) ≤ ∑ x : α, (m / 2 + if x ∈ G then M else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hg : x ∈ G
        · have hfg : m / 2 ≤ f x := (Finset.mem_filter.mp hg).2
          have hfx := hupper x
          simp only [hg, ite_true]
          linarith
        · have hfg : f x < m / 2 := by
            by_contra hn
            exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hn⟩)
          simp only [hg, ite_false]
          linarith
      _ = (Fintype.card α : ℝ) * (m / 2) + (G.card : ℝ) * M := by
        simp [Finset.sum_add_distrib, G, Finset.sum_ite, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
  have htot : m * (Fintype.card α : ℝ) ≤ ∑ x : α, f x :=
    (le_div_iff₀ hcpos).mp hmean
  have hcount : m * (Fintype.card α : ℝ) ≤ 2 * M * (G.card : ℝ) := by
    nlinarith [htot, hsum]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * M) hcpos).2
  simpa [G, mul_comm] using hcount

/-- In a depth-`L` dyadic address grid, the addresses sharing a fixed
prefix cell at depth `j` form exactly the standard dyadic cell fiber. This
reuses the Haar tensor-grid split rather than redefining address division. -/
theorem common_prefix_fiber_card {L : ℕ} (j : Fin L)
    (c : Fin (2 ^ j.val)) :
    Fintype.card {k : Fin (2 ^ L) //
      HaarQuarter.dyadicCellIndex L j k.val = c.val} = 2 ^ (L - j.val) :=
  HaarQuarter.dyadicGridFiber_card L j c

/-- Exact weak-composition count: the antidiagonal of finitely supported
`d`-coordinate natural vectors of total grade `h` has size
`binom(d+h-1,h)`. -/
theorem weak_composition_count (d h : ℕ) :
    ((Finset.univ : Finset (Fin d)).finsuppAntidiag h).card =
      Nat.choose (d + h - 1) h := by
  classical
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_fin]

/-- Sum of the odd squares through `2k-1`, evaluated over the reals. -/
theorem sum_odd_squares_real (k : ℕ) :
    (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) ^ 2) =
      (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1) / 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [ih]

/-- The squared peak-one tent values at all `2k` cell midpoints reduce, by
reflection about the center, to twice the odd-square sum on the first half. -/
theorem midpoint_tent_numerator_sum (k : ℕ) :
    (∑ j ∈ Finset.range (2 * k),
      (((min (2 * j + 1) (4 * k - (2 * j + 1)) : ℕ) : ℝ) ^ 2)) =
      2 * (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) ^ 2) := by
  let f : ℕ → ℝ := fun i =>
    ((min (2 * i + 1) (4 * k - (2 * i + 1)) : ℕ) : ℝ) ^ 2
  have hsplit : (∑ j ∈ Finset.range (2 * k), f j) =
      (∑ j ∈ Finset.range k, f j) +
        ∑ j ∈ Finset.Ico k (2 * k), f j :=
    (Finset.sum_range_add_sum_Ico f (by omega)).symm
  have hupper : (∑ j ∈ Finset.Ico k (2 * k), f j) =
      ∑ j ∈ Finset.range k, f (2 * k - 1 - j) := by
    apply Finset.sum_bij (fun j _ => 2 * k - 1 - j)
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]
      omega
    · intro i hi j hj hij
      simp only [Finset.mem_Ico] at hi hj
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨2 * k - 1 - j, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hindex : 2 * k - 1 - (2 * k - 1 - j) = j := by
        have hjle : j ≤ 2 * k - 1 := by omega
        omega
      simp [f, hindex]
  have hsym : ∀ j, j < k → f (2 * k - 1 - j) = f j := by
    intro j hj
    have hfirst : 2 * (2 * k - 1 - j) + 1 = 4 * k - (2 * j + 1) := by omega
    have houter : 4 * k - (4 * k - (2 * j + 1)) = 2 * j + 1 := by omega
    have hmin : min (2 * (2 * k - 1 - j) + 1)
        (4 * k - (2 * (2 * k - 1 - j) + 1)) =
        min (2 * j + 1) (4 * k - (2 * j + 1)) := by
      rw [hfirst, houter, Nat.min_comm]
    have hcast := congrArg (fun x : ℕ => (x : ℝ) ^ 2) hmin
    simpa [f] using hcast
  have hfirst : (∑ j ∈ Finset.range k, f j) =
      ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    have hmin : min (2 * j + 1) (4 * k - (2 * j + 1)) = 2 * j + 1 := by
      apply Nat.min_eq_left
      omega
    have hcast := congrArg (fun x : ℕ => (x : ℝ) ^ 2) hmin
    simpa [f] using hcast
  calc
    _ = (∑ j ∈ Finset.range k, f j) +
          ∑ j ∈ Finset.Ico k (2 * k), f j := by
      simpa [f, Nat.cast_min] using hsplit
    _ = (∑ j ∈ Finset.range k, f j) +
          ∑ j ∈ Finset.range k, f (2 * k - 1 - j) := by rw [hupper]
    _ = 2 * (∑ j ∈ Finset.range k, f j) := by
      rw [Finset.sum_congr rfl (fun j hj => hsym j (Finset.mem_range.mp hj))]
      ring
    _ = _ := by rw [hfirst]

/-- Uniform mean square of the peak-one tent on a midpoint grid with `2k`
samples, written directly from the integer tent numerators. -/
noncomputable def midpoint_tent_square_mean (k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2 * k),
    (((min (2 * j + 1) (4 * k - (2 * j + 1)) : ℕ) : ℝ) /
      (2 * k : ℝ)) ^ 2) / (2 * k : ℝ)

/-- Exact midpoint identity: the discrete mean square is the continuous tent
integral `1/3` minus the dyadic midpoint correction `1/(12k²)`. -/
theorem midpoint_tent_square_mean_eq (k : ℕ) (hk : 0 < k) :
    midpoint_tent_square_mean k =
      (1 - 1 / (4 * (k : ℝ) ^ 2)) / 3 := by
  have hkR : (2 * k : ℝ) ≠ 0 := by positivity
  rw [midpoint_tent_square_mean]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  rw [midpoint_tent_numerator_sum, sum_odd_squares_real]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp
  <;> ring

/-- For the depth-`a` dyadic midpoint grid, `k=2^(a-1)` and the exact
finite-sum correction is `(1-4^(-a))/3`. -/
theorem midpoint_tent_square_mean_dyadic {a : ℕ} (ha : 1 ≤ a) :
    midpoint_tent_square_mean (2 ^ (a - 1)) =
      (1 - 1 / (4 : ℝ) ^ a) / 3 := by
  have hk : 0 < 2 ^ (a - 1) := Nat.pow_pos (by decide)
  rw [midpoint_tent_square_mean_eq _ hk]
  have hpowNat : 2 * 2 ^ (a - 1) = 2 ^ a := by
    calc
      2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by ring
      _ = 2 ^ ((a - 1) + 1) := (Nat.pow_succ 2 (a - 1)).symm
      _ = 2 ^ a := by congr 1; omega
  have hpow : 4 * (2 ^ (a - 1) : ℝ) ^ 2 = (4 : ℝ) ^ a := by
    have hscale : 2 * (2 ^ (a - 1) : ℝ) = (2 : ℝ) ^ a := by
      exact_mod_cast hpowNat
    calc
      4 * (2 ^ (a - 1) : ℝ) ^ 2 =
          (2 * (2 ^ (a - 1) : ℝ)) ^ 2 := by ring
      _ = ((2 : ℝ) ^ a) ^ 2 := by rw [hscale]
      _ = (2 : ℝ) ^ (a * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (2 * a) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ a := by rw [← pow_mul]
      _ = (4 : ℝ) ^ a := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  push_cast
  rw [hpow]

/-- The numerical midpoint identity from the candidate, in its valid range:
for `a ≥ 1` dyadic midpoint samples of the peak-one tent have mean square
`(1 - 4^(-a))/3`, hence at least `1/4`. -/
theorem midpoint_tent_square_mean_lower {a : ℕ} (ha : 1 ≤ a) :
    (1 : ℝ) / 4 ≤ (1 - (1 : ℝ) / (4 : ℝ) ^ a) / 3 := by
  have hpow : (4 : ℝ) ≤ (4 : ℝ) ^ a := by
    have hpow' : (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ a :=
      pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℝ)) ha
    simpa using hpow'
  have hrecip : (1 : ℝ) / (4 : ℝ) ^ a ≤ 1 / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [hpow]
  nlinarith

end BrownianSharp.Prefix
