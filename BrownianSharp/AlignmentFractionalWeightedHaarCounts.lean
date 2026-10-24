import BrownianSharp.AlignmentFractionalWeightedGrades
import BrownianSharp.AlignmentFractionalPaddingPermutation
import BrownianSharp.FiniteHaarLowDimension
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalWeightedHaarCounts


open BrownianSharp
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalPadding

/-- The integer grade profile of an actual finite tensor-Haar index. -/
def finiteHaarGradeProfile {d M : ℕ} (h : FiniteHaarIndex d M) : Fin d → ℕ :=
  fun i => finiteHaarAxisGrade (h i)

/-- The weighted grade used by an anisotropic fractional integral. -/
def weightedHaarGrade {d M : ℕ} (a : Fin d → ℝ) (r : ℝ)
    (h : FiniteHaarIndex d M) : ℕ :=
  Nat.floor (∑ i : Fin d, (a i / r) * (finiteHaarAxisGrade (h i) : ℝ))

/-- Weighted floor grade of a finite integer profile. -/
def weightedProfileGrade {d : ℕ} (a : Fin d → ℝ) (r : ℝ)
    (s : Fin d → ℕ) : ℕ :=
  Nat.floor (∑ i : Fin d, (a i / r) * (s i : ℝ))

/-- Every one-dimensional grade in a depth-`M` Haar address is at most M. -/
theorem finiteHaarAxisGrade_le_depth {M : ℕ} (h : FiniteHaarAxis M) :
    finiteHaarAxisGrade h ≤ M := by
  cases h with
  | none => simp [finiteHaarAxisGrade]
  | some x =>
      rcases x with ⟨s, j⟩
      simp only [finiteHaarAxisGrade]
      exact Nat.succ_le_of_lt s.isLt

/-- Replacing an actual Haar index by its grades preserves its weighted floor. -/
theorem weightedHaarGrade_eq_profile {d M : ℕ} (a : Fin d → ℝ) (r : ℝ)
    (h : FiniteHaarIndex d M) :
    weightedHaarGrade a r h = weightedProfileGrade a r (finiteHaarGradeProfile h) := rfl

/-- Profiles in the finite depth box. -/
abbrev HaarGradeProfileBox (d M : ℕ) := Fin d → Fin (M + 1)

/-- Split a profile over a concatenated coordinate space into its active and
inactive coordinate blocks. -/
def splitHaarProfileEquiv {ν e M : ℕ} :
    HaarGradeProfileBox (ν + e) M ≃
      ActiveBox ν M × InactiveBox e M where
  toFun s := (fun i => s (Fin.castAdd e i), fun j => s (Fin.natAdd ν j))
  invFun p i :=
    Sum.elim p.1 p.2 (finSumFinEquiv.symm i)
  left_inv s := by
    funext i
    rcases hi : finSumFinEquiv.symm i with j | j
    · have hi' : i = Fin.castAdd e j := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      rw [hi']
      simp [finSumFinEquiv_symm_apply_castAdd]
    · have hi' : i = Fin.natAdd ν j := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      rw [hi']
      simp [finSumFinEquiv_symm_apply_natAdd]
  right_inv p := by
    rcases p with ⟨p, q⟩
    apply Prod.ext
    · funext i
      simp [finSumFinEquiv_symm_apply_castAdd]
    · funext j
      simp [finSumFinEquiv_symm_apply_natAdd]

/-- Reindexing a finite coordinate-grade profile by a coordinate permutation. -/
def permuteHaarProfileEquiv {d M : ℕ} (e : Fin d ≃ Fin d) :
    HaarGradeProfileBox d M ≃ HaarGradeProfileBox d M where
  toFun s i := s (e i)
  invFun s i := s (e.symm i)
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

def profileNat {d M : ℕ} (s : HaarGradeProfileBox d M) : Fin d → ℕ :=
  fun i => (s i).val

theorem weightedProfileGrade_reindex {d M : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (r : ℝ) (s : HaarGradeProfileBox d M) :
    weightedProfileGrade (reindexOrders e a) r
        (profileNat (permuteHaarProfileEquiv e s)) =
      weightedProfileGrade a r (profileNat s) := by
  unfold weightedProfileGrade reindexOrders permuteHaarProfileEquiv profileNat
  apply congrArg Nat.floor
  exact Fintype.sum_equiv e _ _ (by intro i; simp [div_eq_mul_inv, mul_comm])

def weightedProfilePermuteFiberEquiv {d M n : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (r : ℝ) :
    {s : HaarGradeProfileBox d M // weightedProfileGrade a r (profileNat s) = n} ≃
      {s : HaarGradeProfileBox d M //
        weightedProfileGrade (reindexOrders e a) r (profileNat s) = n} where
  toFun s := ⟨permuteHaarProfileEquiv e s.1,
    (weightedProfileGrade_reindex e a r s.1).trans s.2⟩
  invFun s := ⟨permuteHaarProfileEquiv e.symm s.1,
    by simpa [reindexOrders_symm] using
      (weightedProfileGrade_reindex e.symm (reindexOrders e a) r s.1).trans s.2⟩
  left_inv s := by apply Subtype.ext; simp [permuteHaarProfileEquiv]
  right_inv s := by apply Subtype.ext; simp [permuteHaarProfileEquiv]

theorem weightedProfileSum_permute {d M n : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (r : ℝ) :
    (∑ s : {s : HaarGradeProfileBox d M //
        weightedProfileGrade a r (profileNat s) = n},
      (2 : ℝ) ^ (∑ i : Fin d, (profileNat s.1 i : ℕ))) =
    ∑ s : {s : HaarGradeProfileBox d M //
        weightedProfileGrade (reindexOrders e a) r (profileNat s) = n},
      (2 : ℝ) ^ (∑ i : Fin d, (profileNat s.1 i : ℕ)) := by
  classical
  exact Fintype.sum_equiv (weightedProfilePermuteFiberEquiv e a r) _ _ (by
    intro s
    congr 1
    apply Fintype.sum_equiv e.symm _ _
    intro i
    change (s.1 i).val = (s.1 (e (e.symm i))).val
    exact congrArg (fun j => (s.1 j).val) (e.apply_symm_apply i).symm)

theorem weightedProfileGrade_split {ν e M : ℕ} {r : ℝ} (hr : r ≠ 0)
    (w : Fin e → ℝ) (p : ActiveBox ν M × InactiveBox e M) :
    weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
        (profileNat ((splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p)) =
      weightedGradeFloor w p.1 p.2 := by
  apply congrArg Nat.floor
  let s := (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p
  have hsum :
      (∑ i : Fin (ν + e), (paddedOrders r (fun j => r * w j) i / r) * (profileNat s i : ℝ)) =
        (activeGradeNat p.1 : ℝ) + inactiveWeightedGrade w p.2 := by
    calc
      _ = ∑ x : Fin ν ⊕ Fin e,
          (paddedOrders r (fun j => r * w j) (finSumFinEquiv x) / r) *
            (profileNat s (finSumFinEquiv x) : ℝ) := by
            symm
            exact Fintype.sum_equiv finSumFinEquiv _ _ (by intro x; rfl)
      _ = (∑ i : Fin ν, ((p.1 i).val : ℝ)) +
          ∑ j : Fin e, w j * ((p.2 j).val : ℝ) := by
            rw [Fintype.sum_sum_type]
            congr 1
            · apply Fintype.sum_congr
              intro i
              simp [s, paddedOrders, profileNat, splitHaarProfileEquiv,
                finSumFinEquiv_symm_apply_castAdd, hr, mul_div_cancel_left₀]
            · apply Fintype.sum_congr
              intro j
              simp [s, paddedOrders, profileNat, splitHaarProfileEquiv,
                finSumFinEquiv_symm_apply_natAdd, hr, mul_div_cancel_left₀]
      _ = (activeGradeNat p.1 : ℝ) + inactiveWeightedGrade w p.2 := by
            simp [activeGradeNat, inactiveWeightedGrade]
  simpa [weightedProfileGrade, weightedGradeFloor, s] using hsum

def weightedProfileSplitEquiv {ν e M n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (w : Fin e → ℝ) :
    {s : HaarGradeProfileBox (ν + e) M //
      weightedProfileGrade (paddedOrders r (fun j => r * w j)) r (profileNat s) = n} ≃
    {p : ActiveBox ν M × InactiveBox e M // weightedGradeFloor w p.1 p.2 = n} where
  toFun s := by
    let p := splitHaarProfileEquiv s.1
    have hgrade := weightedProfileGrade_split hr w p
    have hsplit : (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p = s.1 := by
      exact (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).left_inv s.1
    rw [hsplit] at hgrade
    exact ⟨p, hgrade.symm.trans s.2⟩
  invFun p := by
    let s := (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p.1
    have hgrade := weightedProfileGrade_split hr w p.1
    exact ⟨s, hgrade.trans p.2⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    rcases hi : finSumFinEquiv.symm i with j | j
    · have hi' : i = Fin.castAdd e j := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      rw [hi']
      simp [splitHaarProfileEquiv, finSumFinEquiv_symm_apply_castAdd]
    · have hi' : i = Fin.natAdd ν j := by
        have h := congrArg finSumFinEquiv hi
        simpa using h
      rw [hi']
      simp [splitHaarProfileEquiv, finSumFinEquiv_symm_apply_natAdd]
  right_inv p := by
    apply Subtype.ext
    simp [splitHaarProfileEquiv]

theorem profileGradeSum_split {ν e M : ℕ}
    (p : ActiveBox ν M × InactiveBox e M) :
    (∑ i : Fin (ν + e),
      (profileNat ((splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p) i : ℕ)) =
      activeGradeNat p.1 + ∑ j : Fin e, (p.2 j).val := by
  calc
    _ = ∑ x : Fin ν ⊕ Fin e,
        (profileNat ((splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm p)
          (finSumFinEquiv x) : ℕ) := by
          symm
          exact Fintype.sum_equiv finSumFinEquiv _ _ (by intro x; rfl)
    _ = _ := by
          rw [Fintype.sum_sum_type]
          simp [activeGradeNat, profileNat, splitHaarProfileEquiv]

theorem paddedProfile_dimension_sum_le {ν e M n : ℕ} {r : ℝ}
    (hr : r ≠ 0) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j) (hν : 0 < ν) :
    (∑ s : {s : HaarGradeProfileBox (ν + e) M //
        weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
          (profileNat s) = n},
      (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) ≤
      Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
  classical
  let E := weightedProfileSplitEquiv (ν := ν) (e := e) (M := M) (n := n) hr w
  let G : ActiveBox ν M × InactiveBox e M → ℝ := fun p =>
    Real.rpow 2 ((activeGradeNat p.1 : ℝ) + inactiveDepth p.2)
  have hsumEq :
      (∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
            (profileNat s) = n},
        (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ))) =
        ∑ p : {p : ActiveBox ν M × InactiveBox e M // weightedGradeFloor w p.1 p.2 = n},
          G p.1 := by
    exact Fintype.sum_equiv E _ _ (by
      intro s
      rw [← Real.rpow_natCast]
      congr 1
      have hp := profileGradeSum_split (E s).1
      have hs :
          (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).symm (E s).1 = s.1 := by
        exact (splitHaarProfileEquiv (ν := ν) (e := e) (M := M)).left_inv s.1
      rw [hs] at hp
      have hp' := congrArg (fun k : ℕ => (k : ℝ)) hp
      rw [hp']
      simp [G, inactiveDepth])
  have hpair :
      (∑ p : {p : ActiveBox ν M × InactiveBox e M //
          weightedGradeFloor w p.1 p.2 = n}, G p.1) =
        ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          if activeGradeNat a + inactiveFloor w b = n then
            Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) else 0 := by
    calc
      _ = ∑ p : ActiveBox ν M × InactiveBox e M,
          if weightedGradeFloor w p.1 p.2 = n then G p else 0 := by
            symm
            rw [← Finset.sum_filter]
            exact Finset.sum_subtype (Finset.univ.filter
              (fun p : ActiveBox ν M × InactiveBox e M => weightedGradeFloor w p.1 p.2 = n))
              (by intro p; simp) (fun p => G p)
      _ = ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
          if activeGradeNat a + inactiveFloor w b = n then
            Real.rpow 2 ((activeGradeNat a : ℝ) + inactiveDepth b) else 0 := by
            simp only [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro a ha
            have hgrade := weightedGradeFloor_eq_active_add_inactiveFloor w
              (fun j => le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt (hw j))) a b
            simp [G, hgrade]
  rw [hsumEq, hpair]
  exact weighted_dimension_slab_sum_le hν w hw

theorem minimumCoordinatePermutation_inactive_lt {ν e : ℕ}
    (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hcard : (minimumIndexSet a r).card = ν)
    (ha : ∀ i, r ≤ a i) (j : Fin e) :
    r < a (minimumCoordinatePermutation a r hcard (Fin.natAdd ν j)) := by
  let ep := minimumCoordinatePermutation a r hcard
  let S := minimumIndexSet a r
  have hmem : ep (Fin.natAdd ν j) ∈ Sᶜ := by
    dsimp [ep, S, minimumCoordinatePermutation]
    rw [finSumFinEquiv_symm_apply_natAdd, finSumEquivOfFinset_inr]
    exact Finset.orderEmbOfFin_mem _ _ _
  have hne : a (ep (Fin.natAdd ν j)) ≠ r := by
    intro heq
    have hnot : ep (Fin.natAdd ν j) ∉ S := Finset.mem_compl.mp hmem
    apply hnot
    simp [S, minimumIndexSet, heq]
  exact lt_of_le_of_ne (ha _) hne.symm

theorem minimumCoordinatePermutation_eq_padded {ν e : ℕ}
    (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hcard : (minimumIndexSet a r).card = ν) (hr : r ≠ 0)
    (ha : ∀ i, r ≤ a i) :
    reindexOrders (minimumCoordinatePermutation a r hcard) a =
      paddedOrders r (fun j => r *
        (a (minimumCoordinatePermutation a r hcard (Fin.natAdd ν j)) / r)) := by
  have hp := reindexOrders_eq_paddedOrders a r hcard
  rw [hp]
  funext i
  rcases hi : finSumFinEquiv.symm i with j | j
  · have hi' : i = Fin.castAdd e j := by
      have h := congrArg finSumFinEquiv hi
      simpa using h
    rw [hi']
    simp [paddedOrders, reindexOrders, minimumCoordinatePermutation_first]
  · have hi' : i = Fin.natAdd ν j := by
      have h := congrArg finSumFinEquiv hi
      simpa using h
    rw [hi']
    simp only [paddedOrders, reindexOrders, finSumFinEquiv_symm_apply_natAdd]
    field_simp [hr]

private theorem finiteHaarGradeProfile_mem_box {d M : ℕ}
    (h : FiniteHaarIndex d M) (i : Fin d) :
    finiteHaarAxisGrade (h i) < M + 1 := by
  exact Nat.lt_succ_of_le (finiteHaarAxisGrade_le_depth (h i))

/-- The weighted-grade fibre of actual Haar addresses is partitioned by its
finite coordinate-grade profile and the corresponding Haar profile fibre. -/
def weightedHaarFiberProfileEquiv {d M : ℕ} (a : Fin d → ℝ) (r : ℝ) (n : ℕ) :
    {h : FiniteHaarIndex d M // weightedHaarGrade a r h = n} ≃
      Σ s : {s : HaarGradeProfileBox d M // weightedProfileGrade a r (profileNat s) = n},
        FiniteHaarProfileFiber (N := M) (profileNat s.1) where
  toFun h :=
    let s : HaarGradeProfileBox d M := fun i =>
      ⟨finiteHaarAxisGrade (h.1 i), finiteHaarGradeProfile_mem_box h.1 i⟩
    ⟨⟨s, by
        have hh := h.2
        simpa [weightedHaarGrade, weightedProfileGrade, finiteHaarGradeProfile,
          profileNat, s] using hh⟩,
      ⟨h.1, by intro i; rfl⟩⟩
  invFun p := ⟨p.2.1, by
    have hp := p.1.2
    have heq : weightedHaarGrade a r p.2.1 =
        weightedProfileGrade a r (profileNat p.1.1) := by
      unfold weightedHaarGrade weightedProfileGrade profileNat
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [p.2.2 i]
      simp [profileNat]
    exact heq.trans hp⟩
  left_inv h := by
    apply Subtype.ext
    rfl
  right_inv p := by
    have hshape : (fun i : Fin d =>
        ⟨finiteHaarAxisGrade (p.2.1 i), finiteHaarGradeProfile_mem_box p.2.1 i⟩) = p.1.1 := by
      funext i
      apply Fin.ext
      exact p.2.2 i
    apply Sigma.ext
    · apply Subtype.ext
      exact hshape
    · change HEq
        (⟨p.2.1, fun i => rfl⟩ : FiniteHaarProfileFiber (N := M)
          (profileNat (fun i : Fin d =>
            ⟨finiteHaarAxisGrade (p.2.1 i), finiteHaarGradeProfile_mem_box p.2.1 i⟩))) p.2
      apply (Subtype.heq_iff_coe_eq (fun b => by
        constructor
        · intro hb i
          change finiteHaarAxisGrade (b i) = profileNat p.1.1 i
          rw [← congrArg profileNat hshape]
          exact hb i
        · intro hb i
          change finiteHaarAxisGrade (b i) = profileNat (fun i : Fin d =>
            ⟨finiteHaarAxisGrade (p.2.1 i), finiteHaarGradeProfile_mem_box p.2.1 i⟩) i
          rw [congrArg profileNat hshape]
          exact hb i)).2
      rfl

/-- A weighted Haar-grade fibre has at most the weighted sum over its
finite grade profiles; each profile fibre contains at most `2^(sum grade)`
addresses. -/
theorem weightedHaarFiber_card_le_profile_sum
    {d M n : ℕ} (a : Fin d → ℝ) (r : ℝ) :
    Fintype.card {h : FiniteHaarIndex d M // weightedHaarGrade a r h = n} ≤
      ∑ s : {s : HaarGradeProfileBox d M // weightedProfileGrade a r (profileNat s) = n},
        2 ^ (∑ i : Fin d, (s.1 i).val) := by
  classical
  rw [Fintype.card_congr (weightedHaarFiberProfileEquiv a r n), Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro s hs
  exact finiteHaarProfileFiber_card_le_pow (N := M) (profileNat s.1)

/-- Uniform weighted-grade count for actual finite tensor-Haar addresses when
the minimum order occurs in `ν` coordinates. The remaining geometric factor
depends only on the fixed order vector, not on the depth or grade. -/
theorem weightedHaarFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (a : Fin (ν + e) → ℝ)
    (hm : Latest.minimumMultiplicity a r ν) :
    let hcard : (minimumIndexSet a r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation a r hcard
    let w : Fin e → ℝ := fun j => a (ep (Fin.natAdd ν j)) / r
    (Fintype.card {h : FiniteHaarIndex (ν + e) M // weightedHaarGrade a r h = n} : ℝ) ≤
      Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
  classical
  unfold Latest.minimumMultiplicity at hm
  have hcard : (minimumIndexSet a r).card = ν := by
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation a r hcard
  let w : Fin e → ℝ := fun j => a (ep (Fin.natAdd ν j)) / r
  have hrne : r ≠ 0 := ne_of_gt hr
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ hr]
    exact minimumCoordinatePermutation_inactive_lt a r hcard hm.1 j
  have hpad : reindexOrders ep a = paddedOrders r (fun j => r * w j) := by
    dsimp [w, ep]
    exact minimumCoordinatePermutation_eq_padded a r hcard hrne hm.1
  have hnat := weightedHaarFiber_card_le_profile_sum (a := a) (r := r) (M := M) (n := n)
  have hreal :
      (Fintype.card {h : FiniteHaarIndex (ν + e) M // weightedHaarGrade a r h = n} : ℝ) ≤
        ∑ s : {s : HaarGradeProfileBox (ν + e) M //
            weightedProfileGrade a r (profileNat s) = n},
          (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) := by
    exact_mod_cast hnat
  calc
    _ ≤ ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade a r (profileNat s) = n},
        (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) := hreal
    _ = ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade (reindexOrders ep a) r (profileNat s) = n},
        (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) :=
          weightedProfileSum_permute ep a r
    _ = ∑ s : {s : HaarGradeProfileBox (ν + e) M //
          weightedProfileGrade (paddedOrders r (fun j => r * w j)) r
            (profileNat s) = n},
        (2 : ℝ) ^ (∑ i : Fin (ν + e), (profileNat s.1 i : ℕ)) := by rw [hpad]
    _ ≤ Real.rpow 2 (n + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) :=
          paddedProfile_dimension_sum_le hrne w hw hν

private def weightedHaarLowFiberEquiv {d M n : ℕ} (a : Fin d → ℝ) (r : ℝ) :
    {h : FiniteHaarIndex d M // weightedHaarGrade a r h ≤ n} ≃
      Σ k : Fin (n + 1), {h : FiniteHaarIndex d M // weightedHaarGrade a r h = k.val} where
  toFun h := ⟨⟨weightedHaarGrade a r h.1, Nat.lt_succ_of_le h.2⟩,
    ⟨h.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by rw [p.2.2]; exact Nat.lt_succ_iff.mp p.1.isLt⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv p := by
    rcases p with ⟨k, ⟨h, hh⟩⟩
    have hgrade : weightedHaarGrade a r h < n + 1 := by
      rw [hh]
      exact k.isLt
    have hk : (⟨weightedHaarGrade a r h, hgrade⟩ : Fin (n + 1)) = k := by
      exact Fin.ext hh
    cases hk
    rfl

private theorem sum_two_pow_succ_le (n : ℕ) :
    (∑ k : Fin (n + 1), (2 : ℝ)^(k.val + 1)) ≤ (2 : ℝ)^(n + 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (2 : ℝ)^(k + 1)) (n + 1)]
  have hgeom : (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) = (2 : ℝ)^(n + 1) - 1 := by
    have h := geom_sum_mul (2 : ℝ) (n + 1)
    nlinarith [h]
  have hshift :
      (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^(k + 1)) =
        2 * (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) := by
    calc
      (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^(k + 1)) =
          ∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k * 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_succ]
      _ = (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) * 2 := by
            rw [Finset.sum_mul]
      _ = 2 * (∑ k ∈ Finset.range (n + 1), (2 : ℝ)^k) := by ring
  rw [hshift, hgeom]
  have hp : (2 : ℝ)^(n + 2) = 2 * (2 : ℝ)^(n + 1) := by
    rw [pow_succ]
    ring
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1)]

/-- Crude cumulative low-grade bound, with the same fixed anisotropic
geometric constant and one additional polynomial factor. -/
theorem weightedHaarLowFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (a : Fin (ν + e) → ℝ)
    (hm : Latest.minimumMultiplicity a r ν) :
    let hcard : (minimumIndexSet a r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation a r hcard
    let w : Fin e → ℝ := fun j => a (ep (Fin.natAdd ν j)) / r
    (Fintype.card {h : FiniteHaarIndex (ν + e) M // weightedHaarGrade a r h ≤ n} : ℝ) ≤
      Real.rpow 2 (n + 2) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
        ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
  classical
  unfold Latest.minimumMultiplicity at hm
  have hcard : (minimumIndexSet a r).card = ν := by
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation a r hcard
  let w : Fin e → ℝ := fun j => a (ep (Fin.natAdd ν j)) / r
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ hr]
    exact minimumCoordinatePermutation_inactive_lt a r hcard hm.1 j
  have hfiber :
      (Fintype.card {h : FiniteHaarIndex (ν + e) M // weightedHaarGrade a r h ≤ n} : ℝ) =
        ∑ k : Fin (n + 1),
          (Fintype.card {h : FiniteHaarIndex (ν + e) M //
            weightedHaarGrade a r h = k.val} : ℝ) := by
    rw [Fintype.card_congr (weightedHaarLowFiberEquiv a r), Fintype.card_sigma]
    simp [Nat.cast_sum]
  have hterm (k : Fin (n + 1)) :
      (Fintype.card {h : FiniteHaarIndex (ν + e) M //
        weightedHaarGrade a r h = k.val} : ℝ) ≤
        Real.rpow 2 (k.val + 1) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
    have h := weightedHaarFiber_card_le_minimumMultiplicity
      (M := M) (n := k.val) hr hν a hm
    have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
    have hpoly : ((k.val + 1 : ℕ) : ℝ)^(ν - 1) ≤ ((n + 1 : ℕ) : ℝ)^(ν - 1) := by
      gcongr
    have hconst : 0 ≤ ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹ := by
      apply Finset.prod_nonneg
      intro j hj
      have hq : Real.rpow 2 (-(w j - 1)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
      exact inv_nonneg.mpr (sub_nonneg.mpr hq.le)
    calc
      _ ≤ Real.rpow 2 (k.val + 1) * (((k.val + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := h
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpoly hconst)
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hsum' :
      (∑ k : Fin (n + 1),
        (Fintype.card {h : FiniteHaarIndex (ν + e) M //
          weightedHaarGrade a r h = k.val} : ℝ)) ≤
      ∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1) *
        (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hterm k
  have hsum :
      (∑ k : Fin (n + 1),
        (Fintype.card {h : FiniteHaarIndex (ν + e) M //
          weightedHaarGrade a r h = k.val} : ℝ)) ≤
      (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) *
        (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
    calc
      _ ≤ ∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1) *
          (((n + 1 : ℕ) : ℝ)^(ν - 1) *
            ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := hsum'
      _ = _ := by rw [Finset.sum_mul]
  rw [hfiber]
  have hgeom :
      (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) ≤ Real.rpow 2 (n + 2) := by
    have h := sum_two_pow_succ_le n
    have hleft :
        (∑ k : Fin (n + 1), Real.rpow 2 (k.val + 1)) =
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
    exact h
  have hconst : 0 ≤ ((n + 1 : ℕ) : ℝ)^(ν - 1) *
      ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹ := by
    have hprod : 0 ≤ ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹ := by
      apply Finset.prod_nonneg
      intro j hj
      have hq : Real.rpow 2 (-(w j - 1)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
      exact inv_nonneg.mpr (sub_nonneg.mpr hq.le)
    exact mul_nonneg (by positivity) hprod
  calc
    _ ≤ (Real.rpow 2 (n + 2)) * (((n + 1 : ℕ) : ℝ)^(ν - 1) *
          ∏ j : Fin e, (1 - Real.rpow 2 (-(w j - 1)))⁻¹) := by
      exact hsum.trans (mul_le_mul_of_nonneg_right hgeom hconst)

end BrownianSharp.AlignmentFractionalWeightedHaarCounts
