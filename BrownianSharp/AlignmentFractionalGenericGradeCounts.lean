import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.AlignmentFractionalWeightedGrades
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalGenericGradeCounts

open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalPadding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev ProductGradeFiber {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ E)
    (s : HaarGradeProfileBox d M) :=
  ∀ i, GradeIndex (U i) (s i).val

/-- Decompose a product of arbitrary nested graded-frame indices into its
coordinate grade profile and the product of coordinate grade fibers. -/
def productGradeFiberEquiv {d M n : ℕ}
    (U : Fin d → ℕ → Submodule ℝ E) (α : Fin d → ℝ) (r : ℝ) :
    {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n} ≃
    Σ s : {s : HaarGradeProfileBox d M //
      weightedProfileGrade α r (profileNat s) = n}, ProductGradeFiber U s.1 where
  toFun a := ⟨⟨fun i => (a.1 i).1, a.2⟩, fun i => (a.1 i).2⟩
  invFun x := ⟨(fun i => ⟨x.1.1 i, x.2 i⟩), x.1.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact Sigma.eta (a.1 i)
  right_inv x := by
    cases x with
    | mk s fiber =>
      apply Sigma.ext (Subtype.ext rfl)
      exact HEq.rfl

/-! Counts of product indices assembled from arbitrary finite-dimensional
graded coordinate families.  The profile/fiber reindexing is shared with the
tensor-energy module; the only input here is a per-grade dimension bound. -/

/-- Product-index cardinality is bounded by the sum over grade profiles of
the products of the coordinatewise grade-fiber bounds. -/
theorem productGrade_weightedFiber_card_le_profile_sum
    {d M n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (U : Fin d → ℕ → Submodule ℝ E)
    (α : Fin d → ℝ) (r : ℝ) (A : Fin d → ℕ)
    (hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i * 2^g) :
    Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n} ≤
      ∑ s : {s : HaarGradeProfileBox d M //
          weightedProfileGrade α r (profileNat s) = n},
        ∏ i : Fin d, A i * 2^(s.1 i).val := by
  classical
  rw [Fintype.card_congr (productGradeFiberEquiv U α r), Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro s hs
  rw [Fintype.card_pi]
  apply Finset.prod_le_prod
  intro i hi
  exact hA i (s.1 i).val

private theorem cast_profile_product_eq {d M : ℕ} (A : Fin d → ℕ)
    (s : HaarGradeProfileBox d M) :
    (∏ i : Fin d, ((A i * 2^(s i).val : ℕ) : ℝ)) =
      (∏ i : Fin d, (A i : ℝ)) *
        (2 : ℝ)^(∑ i : Fin d, (s i).val) := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

/-- Sharp weighted-grade cardinality for arbitrary product graded frames whose
coordinate grade multiplicities grow like `Aᵢ 2^g`. The constant is uniform in
both truncation depth and weighted grade. -/
theorem productGrade_weightedFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (U : Fin (ν + e) → ℕ → Submodule ℝ E)
    (α : Fin (ν + e) → ℝ) (A : Fin (ν + e) → ℕ)
    (hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i * 2^g)
    (hm : Latest.minimumMultiplicity α r ν) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    (Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n} : ℝ) ≤
      (∏ i : Fin (ν + e), (A i : ℝ)) *
        (Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹)) := by
  classical
  unfold Latest.minimumMultiplicity at hm
  have hcard : (minimumIndexSet α r).card = ν := by
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation α r hcard
  let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ hr]
    exact minimumCoordinatePermutation_inactive_lt α r hcard hm.1 j
  have hrne : r ≠ 0 := ne_of_gt hr
  have hpad : reindexOrders ep α = paddedOrders r (fun j => r * w j) := by
    dsimp [w, ep]
    exact minimumCoordinatePermutation_eq_padded α r hcard hrne hm.1
  have hnat := productGrade_weightedFiber_card_le_profile_sum
    (U := U) (α := α) (r := r) (A := A) (hA := hA) (M := M) (n := n)
  have hreal :
      (Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n} : ℝ) ≤
        ∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade α r (profileNat s) = n},
          ∏ i : Fin (ν + e), ((A i * 2^(s.1 i).val : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hprofile :
      (∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade α r (profileNat s) = n},
        ∏ i : Fin (ν + e), ((A i * 2^(s.1 i).val : ℕ) : ℝ)) =
      (∏ i : Fin (ν + e), (A i : ℝ)) *
        (∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade α r (profileNat s) = n},
          (2 : ℝ)^(∑ i : Fin (ν + e), (s.1 i).val)) := by
    rw [show (∑ s : {s : HaarGradeProfileBox (ν + e) M //
        weightedProfileGrade α r (profileNat s) = n},
      ∏ i : Fin (ν + e), ((A i * 2^(s.1 i).val : ℕ) : ℝ)) =
        ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade α r (profileNat s) = n},
          (∏ i : Fin (ν + e), (A i : ℝ)) *
            (2 : ℝ)^(∑ i : Fin (ν + e), (s.1 i).val) by
      apply Finset.sum_congr rfl
      intro s hs
      exact cast_profile_product_eq A s.1]
    rw [← Finset.mul_sum]
  have hprofile₂ :
      (∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade α r (profileNat s) = n},
        ∏ i : Fin (ν + e), ((A i * 2^(s.1 i).val : ℕ) : ℝ)) =
      (∏ i : Fin (ν + e), (A i : ℝ)) *
        (∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade α r (profileNat s) = n},
          (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) := by
    simpa [profileNat] using hprofile
  have hprofile' :
      (∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade α r (profileNat s) = n},
        (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) =
      ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
            (profileNat s) = n},
        (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) := by
    calc
      _ = ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade (reindexOrders ep α) r (profileNat s) = n},
          (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) :=
        weightedProfileSum_permute ep α r
      _ = _ := by rw [hpad]
  have hbound := paddedProfile_dimension_sum_le (M := M) (n := n) hrne w hw hν
  have hK : 0 ≤ ∏ i : Fin (ν + e), (A i : ℝ) := by positivity
  calc
    _ ≤ (∏ i : Fin (ν + e), (A i : ℝ)) *
        (∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade α r (profileNat s) = n},
          (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) := by
      rw [← hprofile₂]
      exact hreal
    _ = (∏ i : Fin (ν + e), (A i : ℝ)) *
        (∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
              (profileNat s) = n},
          (2 : ℝ)^(∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) := by
      rw [hprofile']
    _ ≤ (∏ i : Fin (ν + e), (A i : ℝ)) *
        (Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹)) :=
      mul_le_mul_of_nonneg_left hbound hK

private theorem sum_rpow_two_succ_le (n : ℕ) :
    (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) ≤ Real.rpow 2 (n + 2) := by
  have hnat : (∑ k : Fin (n + 1), (2 : ℝ)^(k.val + 1)) ≤ (2 : ℝ)^(n + 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (2 : ℝ)^(k + 1)) (n + 1)]
    have hgeom : (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) = (2 : ℝ)^(n + 1) - 1 := by
      have h := geom_sum_mul (2 : ℝ) (n + 1)
      nlinarith [h]
    have hshift :
        (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^(k + 1)) =
          2 * (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) := by
      calc
        _ = ∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k * 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_succ]
        _ = (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) * 2 := by rw [Finset.sum_mul]
        _ = _ := by ring
    rw [hshift, hgeom]
    have hp : (2 : ℝ)^(n + 2) = 2 * (2 : ℝ)^(n + 1) := by rw [pow_succ]; ring
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1)]
  have hleft : (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) =
      ∑ k : Fin (n + 1), (2 : ℝ)^(k.val + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Real.rpow_natCast]
    congr 1
    norm_cast
  have hright : (2 : ℝ)^(n + 2) = Real.rpow 2 (n + 2) := by
    rw [← Real.rpow_natCast]
    congr 1
    norm_cast
  rw [hleft, ← hright]
  exact hnat

/-- Sharp cumulative count for arbitrary product graded frames. The same
geometric profile bound controls all grades at most `n` without adding an
extra polynomial factor. -/
theorem productGrade_weightedLowFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (U : Fin (ν + e) → ℕ → Submodule ℝ E)
    (α : Fin (ν + e) → ℝ) (A : Fin (ν + e) → ℕ)
    (hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i * 2^g)
    (hm : Latest.minimumMultiplicity α r ν) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    (Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) ≤ n} : ℝ) ≤
      (∏ i : Fin (ν + e), (A i : ℝ)) *
        (Real.rpow 2 (n + 2) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹)) := by
  classical
  unfold Latest.minimumMultiplicity at hm
  have hcard : (minimumIndexSet α r).card = ν := by
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation α r hcard
  let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ hr]
    exact minimumCoordinatePermutation_inactive_lt α r hcard hm.1 j
  let K : ℝ := ∏ i : Fin (ν + e), (A i : ℝ)
  let G : ℝ := ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹
  let P (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)^(ν - 1)
  have hK : 0 ≤ K := by positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    apply Finset.prod_nonneg
    intro j hj
    have hq : Real.rpow 2 (-(w j - 1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
    exact inv_nonneg.mpr (sub_nonneg.mpr hq.le)
  have hPmono {k : ℕ} (hk : k ≤ n) : P k ≤ P n := by
    dsimp [P]
    gcongr
  let low := {a : ∀ i, GradedFrameIndex (U i) M //
    weightedProfileGrade α r (profileNat (fun i => (a i).1)) ≤ n}
  let exact (k : Fin (n + 1)) := {a : ∀ i, GradedFrameIndex (U i) M //
    weightedProfileGrade α r (profileNat (fun i => (a i).1)) = k.val}
  let injectLow : low → Σ k : Fin (n + 1), exact k := fun a =>
    ⟨⟨weightedProfileGrade α r (profileNat (fun i => (a.1 i).1)),
      Nat.lt_succ_of_le a.2⟩, ⟨a.1, rfl⟩⟩
  have hinj : Function.Injective injectLow := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun p : Σ k : Fin (n + 1), exact k => p.2.1) hab
  have hcardle := Fintype.card_le_of_injective injectLow hinj
  rw [Fintype.card_sigma] at hcardle
  have hreal : (Fintype.card low : ℝ) ≤
      ∑ k : Fin (n + 1), (Fintype.card (exact k) : ℝ) := by
    exact_mod_cast hcardle
  have hterm (k : Fin (n + 1)) :
      (Fintype.card (exact k) : ℝ) ≤ K *
        (Real.rpow 2 (k.val + 1) * (P n * G)) := by
    have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
    have hp := hPmono hk
    have h := productGrade_weightedFiber_card_le_minimumMultiplicity
      (hr := hr) (hν := hν) (U := U) (α := α) (A := A)
      (hA := hA) (hm := hm) (M := M) (n := k.val)
    have h' : (Fintype.card (exact k) : ℝ) ≤ K *
        (Real.rpow 2 (k.val + 1) * (P k.val * G)) := by
      simpa [K, G, P, ep, w, hcard, exact] using h
    calc
      _ ≤ K * (Real.rpow 2 (k.val + 1) * (P k.val * G)) := h'
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
        exact mul_le_mul_of_nonneg_right hp hG
  have hsum :
      (∑ k : Fin (n + 1), (Fintype.card (exact k) : ℝ)) ≤
        ∑ k : Fin (n + 1), K *
          (Real.rpow 2 (k.val + 1) * (P n * G)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hterm k
  have hsum' :
      (∑ k : Fin (n + 1), K *
        (Real.rpow 2 (k.val + 1) * (P n * G))) =
      K * (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) * (P n * G) := by
    calc
      _ = K * (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1) * (P n * G)) := by
        symm
        rw [Finset.mul_sum]
      _ = K * ((∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) * (P n * G)) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  have hgeom := sum_rpow_two_succ_le n
  have hPG : 0 ≤ P n * G := mul_nonneg (by positivity) hG
  change (Fintype.card low : ℝ) ≤ K *
      (Real.rpow 2 (n + 2) * (P n * G))
  calc
    _ ≤ ∑ k : Fin (n + 1), (Fintype.card (exact k) : ℝ) := hreal
    _ ≤ ∑ k : Fin (n + 1), K *
        (Real.rpow 2 (k.val + 1) * (P n * G)) := hsum
    _ = K * (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) * (P n * G) := hsum'
    _ ≤ (K * Real.rpow 2 (n + 2)) * (P n * G) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgeom hK) hPG
    _ = K * (Real.rpow 2 (n + 2) * (P n * G)) := by ring

end BrownianSharp.AlignmentFractionalGenericGradeCounts
