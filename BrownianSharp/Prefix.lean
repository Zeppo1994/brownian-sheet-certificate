import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import BrownianSharp.HaarTensorGrid
import BrownianSharp.Target

/-!
Deterministic midpoint/prefix counting lemmas for the Brownian sharp small-ball
candidate.  This module isolates the finite combinatorics from any Gaussian
probability or concentration theorem.
-/

namespace BrownianSharp.Prefix

/-- Coordinatewise domination of a shape by a capped common-prefix vector. -/
def Below {d : ℕ} (r c : Fin d → ℕ) : Prop := ∀ i, r i ≤ c i

/-- The sum of the coordinatewise remainder is the excess prefix grade. -/
theorem remainder_grade {d : ℕ} (r c : Fin d → ℕ)
    (hrc : Below r c) (hr : (∑ i : Fin d, r i) = n)
    (hc : (∑ i : Fin d, c i) = n + h) :
    (∑ i : Fin d, (c i - r i)) = h := by
  have hsum : (∑ i : Fin d, (c i - r i)) + ∑ i : Fin d, r i =
      ∑ i : Fin d, c i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := hrc i
    omega
  omega

/-- Distinct contributing shapes have distinct coordinatewise remainders. -/
theorem remainder_injective {d : ℕ} (c : Fin d → ℕ) :
    Function.Injective (fun r : {r : Fin d → ℕ // Below r c} =>
      fun i => c i - r.1 i) := by
  intro r s hrs
  apply Subtype.ext
  funext i
  have hri := r.2 i
  have hsi := s.2 i
  have heq : c i - r.1 i = c i - s.1 i :=
    congrArg (fun f : Fin d → ℕ => f i) hrs
  omega

/-- Consequently, prefix subtraction is a genuine injection into the
remainder shapes; this is the set-theoretic core of the overlap count. -/
theorem contributing_shape_remainders_are_injective {d : ℕ}
    (c : Fin d → ℕ) :
    ∀ r s : {r : Fin d → ℕ // Below r c},
      (fun i => c i - r.1 i) = (fun i => c i - s.1 i) → r = s := by
  exact remainder_injective c

/-- A deterministic fixed-fraction estimate used to extract good gridpoints.
The bounds `0 ≤ alpha ≤ 1` express that it is a fraction. -/
theorem good_fraction_lower {m M alpha : ℝ}
    (hm : 0 < m) (hM : 0 < M) (halpha0 : 0 ≤ alpha)
    (hmean : m ≤ M * alpha + (m / 2) * (1 - alpha)) :
    m / (2 * M) ≤ alpha := by
  have hbad : (m / 2) * (1 - alpha) ≤ m / 2 := by
    calc
      (m / 2) * (1 - alpha) ≤ (m / 2) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = m / 2 := by ring
  have hgood : m / 2 ≤ M * alpha := by linarith
  have hprod : m ≤ (2 * M) * alpha := by nlinarith [hgood]
  exact (div_le_iff₀ (by positivity : 0 < 2 * M)).2 (by nlinarith [hprod])

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

/-- A fixed grid address has at most the fraction `2^-j` of all addresses
sharing its first `j` cell bits. This is the one-coordinate estimate used in
the product prefix-mass count. -/
theorem common_prefix_fiber_fraction {L : ℕ} (j : Fin L)
    (c : Fin (2 ^ j.val)) :
    Fintype.card {k : Fin (2 ^ L) //
      HaarQuarter.dyadicCellIndex L j k.val = c.val} * 2 ^ j.val = 2 ^ L := by
  rw [common_prefix_fiber_card]
  rw [← Nat.pow_add]
  congr 1
  omega

/-- Product-grid version of the fixed common-prefix fiber count. -/
theorem product_common_prefix_fiber_card {d L : ℕ}
    (profile : HaarQuarter.ProductGridProfile (Fin d) L)
    (cell : HaarQuarter.ProductGridCell profile) :
    Fintype.card {x : HaarQuarter.ProductGridPoint (Fin d) L //
      HaarQuarter.productGridCellIndex profile x = cell} =
      ∏ i, 2 ^ (L - (profile i).val) :=
  HaarQuarter.productGridFiber_card profile cell

/-- For a fixed product address, the proportion of addresses sharing all
specified coordinate prefixes is exactly `2^(-sum j)`, expressed without
rational probabilities by clearing the finite sample-space denominator. -/
theorem product_common_prefix_fiber_fraction {d L : ℕ}
    (profile : HaarQuarter.ProductGridProfile (Fin d) L)
    (cell : HaarQuarter.ProductGridCell profile) :
    Fintype.card {x : HaarQuarter.ProductGridPoint (Fin d) L //
      HaarQuarter.productGridCellIndex profile x = cell} *
        (∏ i, 2 ^ (profile i).val) =
      Fintype.card (HaarQuarter.ProductGridPoint (Fin d) L) := by
  rw [product_common_prefix_fiber_card]
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i, 2 ^ (L - (profile i).val) * 2 ^ (profile i).val) =
        ∏ i, 2 ^ L := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt (profile i).isLt)]
    _ = Fintype.card (HaarQuarter.ProductGridPoint (Fin d) L) := by
      simp [HaarQuarter.ProductGridPoint, Fintype.card_pi]

/-- The profile count appearing in the Brownian argument is the existing
Haar shape-count normalization at `D=d-1`, `N=n+1`. -/
theorem layer_shape_count_eq_haar_shapeCount {d n : ℕ} (hd : 1 ≤ d) :
    Nat.choose (n + d - 1) (d - 1) = HaarQuarter.shapeCount (d - 1) (n + 1) := by
  have htop : n + d - 1 = n + (d - 1) := by omega
  rw [HaarQuarter.shapeCount, Nat.succ_sub_one, htop]

/-- The contributing part of the grade-`n` Finsupp antidiagonal injects into
the grade-`h` antidiagonal by subtracting from the fixed prefix vector. This
is the finite cardinal form of the common-prefix remainder count. -/
theorem contributing_finsupp_count_le {d n h : ℕ}
    (c : Fin d →₀ ℕ)
    (hc : (c.sum fun _ x => x) = n + h) :
    (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).filter
        (fun r => ∀ i, r i ≤ c i)).card ≤
      ((Finset.univ : Finset (Fin d)).finsuppAntidiag h).card := by
  classical
  let S := (Finset.univ : Finset (Fin d)).finsuppAntidiag n
  let T := (Finset.univ : Finset (Fin d)).finsuppAntidiag h
  let A := S.filter (fun r => ∀ i, r i ≤ c i)
  apply Finset.card_le_card_of_injOn (fun r => c - r)
  · intro r hr
    have hrs := (Finset.mem_filter.mp hr).1
    have hbound := (Finset.mem_filter.mp hr).2
    have hrgrade : (r.sum fun _ x => x) = n := by
      simpa [S] using (Finset.mem_finsuppAntidiag'.mp hrs).1
    have hpoint : r + (c - r) = c := by
      ext i
      exact Nat.add_sub_of_le (hbound i)
    have hsumAdd := Finsupp.sum_hom_add_index
      (h := fun _ : Fin d => AddMonoidHom.id ℕ) (f := r) (g := c - r)
    have hsum : (r.sum fun _ x => x) + ((c - r).sum fun _ x => x) =
        c.sum fun _ x => x := by
      calc
        _ = (r + (c - r)).sum fun _ x => x := hsumAdd.symm
        _ = c.sum fun _ x => x := by rw [hpoint]
    have hout : ((c - r).sum fun _ x => x) = h := by omega
    change c - r ∈ Finset.univ.finsuppAntidiag h
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨hout, Finsupp.support_subset_iff.mpr (by simp)⟩
  · intro r hr s hs hrs
    have hrbound := (Finset.mem_filter.mp hr).2
    have hsbound := (Finset.mem_filter.mp hs).2
    apply Finsupp.ext
    intro i
    have hcoord : c i - r i = c i - s i :=
      congrArg (fun f : Fin d →₀ ℕ => f i) hrs
    have hri := hrbound i
    have hsi := hsbound i
    omega

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
