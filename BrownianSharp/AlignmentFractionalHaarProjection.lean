import BrownianSharp.AlignmentGaussianFractionalHaar
import BrownianSharp.FiniteHaarLayerEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Finite Haar expansions of the actual unit-interval source projections. -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalHaarProjection

open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalL2

abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

theorem sourceDyadicCell_parent_eq_children (r : ℕ) (j : Fin (2^r)) :
    sourceDyadicCell r j =
      sourceDyadicCell (r+1) (sourceDyadicLeftChild j) ∪
        sourceDyadicCell (r+1) (sourceDyadicRightChild j) := by
  ext x
  constructor
  · intro hx
    change sourceDyadicLeft r j ≤ x ∧ x < sourceDyadicRight r j at hx
    have hleft : sourceDyadicLeft (r+1) (sourceDyadicLeftChild j) ≤ x := by
      simpa [sourceDyadic_leftChild_left_eq] using hx.1
    have hright : x < sourceDyadicRight (r+1) (sourceDyadicRightChild j) := by
      simpa [sourceDyadic_rightChild_right_eq] using hx.2
    have hmid : sourceDyadicRight (r+1) (sourceDyadicLeftChild j) =
        sourceDyadicLeft (r+1) (sourceDyadicRightChild j) :=
      sourceDyadic_leftChild_right_eq_rightChild_left j
    by_cases h : x < sourceDyadicRight (r+1) (sourceDyadicLeftChild j)
    · exact Or.inl ⟨hleft,h⟩
    · exact Or.inr ⟨by rw [← hmid]; exact le_of_not_gt h, hright⟩
  · rintro (hx | hx)
    · exact sourceDyadic_leftChild_subset_parent j hx
    · exact sourceDyadic_rightChild_subset_parent j hx

theorem sourceDyadicCellIndicator_parent_eq_children (r : ℕ)
    (j : Fin (2^r)) :
    sourceDyadicCellIndicator r j =
      sourceDyadicCellIndicator (r+1) (sourceDyadicLeftChild j) +
        sourceDyadicCellIndicator (r+1) (sourceDyadicRightChild j) := by
  apply Lp.ext
  have hp := sourceDyadicCellIndicator_coeFn r j
  have hl := sourceDyadicCellIndicator_coeFn (r+1) (sourceDyadicLeftChild j)
  have hr := sourceDyadicCellIndicator_coeFn (r+1) (sourceDyadicRightChild j)
  have hadd := Lp.coeFn_add
    (sourceDyadicCellIndicator (r+1) (sourceDyadicLeftChild j))
    (sourceDyadicCellIndicator (r+1) (sourceDyadicRightChild j))
  have hsets := sourceDyadicCell_parent_eq_children r j
  filter_upwards [hp, hl, hr, hadd] with x hp hl hr hadd
  rw [hp, hadd, Pi.add_apply, hl, hr]
  change (sourceDyadicCell r j).indicator (fun _ => (1:ℝ)) x =
    (sourceDyadicCell (r+1) (sourceDyadicLeftChild j)).indicator
        (fun _ => (1:ℝ)) x +
      (sourceDyadicCell (r+1) (sourceDyadicRightChild j)).indicator
        (fun _ => (1:ℝ)) x
  rw [hsets, Set.indicator_union_of_disjoint
    (sourceDyadicCells_disjoint (sourceDyadic_leftChild_ne_rightChild j))]

theorem sourceDyadicPiecewiseConstants_le_succ (n : ℕ) :
    sourceDyadicPiecewiseConstants n ≤ sourceDyadicPiecewiseConstants (n+1) := by
  rw [sourceDyadicPiecewiseConstants]
  apply Submodule.span_le.2
  rintro f ⟨j,rfl⟩
  rw [sourceDyadicCellIndicator_parent_eq_children]
  exact add_mem (Submodule.subset_span ⟨sourceDyadicLeftChild j,rfl⟩)
    (Submodule.subset_span ⟨sourceDyadicRightChild j,rfl⟩)

theorem sourceDyadicPiecewiseConstants_mono {n m : ℕ} (hnm : n ≤ m) :
    sourceDyadicPiecewiseConstants n ≤ sourceDyadicPiecewiseConstants m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact le_rfl
  | succ m ih =>
      by_cases h : n ≤ m
      · exact (ih h).trans (sourceDyadicPiecewiseConstants_le_succ m)
      · have hn : n = m+1 := by omega
        subst n
        exact le_rfl

theorem sourceDyadicHaarMother_mem_piecewiseConstants_succ (r : ℕ)
    (j : Fin (2^r)) :
    sourceDyadicHaarMother r j ∈ sourceDyadicPiecewiseConstants (r+1) := by
  rw [sourceDyadicPiecewiseConstants]
  unfold sourceDyadicHaarMother
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact Submodule.subset_span ⟨sourceDyadicLeftChild j,rfl⟩
  · exact Submodule.subset_span ⟨sourceDyadicRightChild j,rfl⟩

theorem sourceDyadicHaarMother_mem_piecewiseConstants {r n : ℕ}
    (hrn : r < n) (j : Fin (2^r)) :
    sourceDyadicHaarMother r j ∈ sourceDyadicPiecewiseConstants n := by
  exact (sourceDyadicPiecewiseConstants_mono (Nat.succ_le_of_lt hrn))
    (sourceDyadicHaarMother_mem_piecewiseConstants_succ r j)

theorem sourceDyadicHaarMother_mem_orthogonal_piecewise (r : ℕ)
    (j : Fin (2^r)) :
    sourceDyadicHaarMother r j ∈ (sourceDyadicPiecewiseConstants r)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro f hf
  rw [sourceDyadicPiecewiseConstants] at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro g ⟨k,rfl⟩
    exact sourceDyadicHaarMother_inner_parent j k
  · simp
  · intro x y hx hy hpx hpy
    rw [inner_add_right, hpx, hpy]
    simp
  · intro a x hx hpx
    rw [inner_smul_right, hpx]
    simp

abbrev SourceHaarIndex (n : ℕ) := Option (Σ r : Fin n, Fin (2^r.val))

noncomputable def sourceHaarFamily (n : ℕ) : SourceHaarIndex n → SourceL2
  | none => sourceDyadicCellIndicator 0 ⟨0, by norm_num⟩
  | some ⟨r,j⟩ => sourceDyadicHaarMother r.val j

theorem sourceHaarIndex_card (n : ℕ) : Fintype.card (SourceHaarIndex n) = 2^n := by
  simpa [SourceHaarIndex, BrownianSharp.FiniteHaarAxis] using
    BrownianSharp.finiteHaarAxis_card n

theorem sourceHaarFamily_mem_piecewiseConstants (n : ℕ)
    (a : SourceHaarIndex n) :
    sourceHaarFamily n a ∈ sourceDyadicPiecewiseConstants n := by
  cases a with
  | none =>
      apply sourceDyadicPiecewiseConstants_mono
      · exact Nat.zero_le _
      · exact Submodule.subset_span ⟨⟨0, by norm_num⟩, rfl⟩
  | some a =>
      rcases a with ⟨r,j⟩
      exact sourceDyadicHaarMother_mem_piecewiseConstants r.isLt j

theorem sourceDyadicHaarMother_cross_level_inner {r s : ℕ}
    (j : Fin (2^r)) (k : Fin (2^s)) (hrs : r ≠ s) :
    inner ℝ (sourceDyadicHaarMother r j) (sourceDyadicHaarMother s k) = 0 := by
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · have hcoarse : sourceDyadicHaarMother r j ∈ sourceDyadicPiecewiseConstants s :=
      sourceDyadicHaarMother_mem_piecewiseConstants hrs j
    have hfine : sourceDyadicHaarMother s k ∈
        (sourceDyadicPiecewiseConstants s)ᗮ :=
      sourceDyadicHaarMother_mem_orthogonal_piecewise s k
    rw [real_inner_comm]
    exact Submodule.inner_left_of_mem_orthogonal hcoarse hfine
  · have hcoarse : sourceDyadicHaarMother s k ∈ sourceDyadicPiecewiseConstants r :=
      sourceDyadicHaarMother_mem_piecewiseConstants hsr k
    have hfine : sourceDyadicHaarMother r j ∈
        (sourceDyadicPiecewiseConstants r)ᗮ :=
      sourceDyadicHaarMother_mem_orthogonal_piecewise r j
    exact Submodule.inner_left_of_mem_orthogonal hcoarse hfine

theorem sourceHaarFamily_orthonormal (n : ℕ) :
    Orthonormal ℝ (sourceHaarFamily n) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  cases a with
  | none =>
      cases b with
      | none =>
          simpa [sourceHaarFamily] using
            (sourceDyadicCellIndicator_inner_self
              (n:=0) (j:=⟨0, by norm_num⟩))
      | some b =>
          rcases b with ⟨r,k⟩
          have horth := sourceDyadicHaarMother_mem_orthogonal_piecewise r.val k
          have hfather : sourceDyadicCellIndicator 0 ⟨0, by norm_num⟩ ∈
              sourceDyadicPiecewiseConstants r.val := by
            apply sourceDyadicPiecewiseConstants_mono
            · exact Nat.zero_le _
            · exact Submodule.subset_span ⟨⟨0, by norm_num⟩, rfl⟩
          rw [real_inner_comm]
          exact Submodule.inner_left_of_mem_orthogonal hfather horth
  | some a =>
      rcases a with ⟨r,j⟩
      cases b with
      | none =>
          have horth := sourceDyadicHaarMother_mem_orthogonal_piecewise r.val j
          have hfather : sourceDyadicCellIndicator 0 ⟨0, by norm_num⟩ ∈
              sourceDyadicPiecewiseConstants r.val := by
            apply sourceDyadicPiecewiseConstants_mono
            · exact Nat.zero_le _
            · exact Submodule.subset_span ⟨⟨0, by norm_num⟩, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hfather horth
      | some b =>
          rcases b with ⟨s,k⟩
          by_cases hrs : r.val = s.val
          · have hrs' : r = s := Fin.ext hrs
            subst s
            simpa [sourceHaarFamily] using
              ((orthonormal_iff_ite.mp
                (sourceDyadicHaarMother_orthonormal r.val)) j k)
          · have hne : (some ⟨r,j⟩ : SourceHaarIndex n) ≠ some ⟨s,k⟩ := by
              intro h
              have h' : (⟨r,j⟩ : Σ t : Fin n, Fin (2^t.val)) = ⟨s,k⟩ :=
                Option.some.inj h
              exact hrs (congrArg (fun z : Σ t : Fin n, Fin (2^t.val) => z.1.val) h')
            rw [if_neg hne]
            exact sourceDyadicHaarMother_cross_level_inner j k hrs

noncomputable def sourceDyadicCellOrthonormal (n : ℕ) (j : Fin (2^n)) : SourceL2 :=
  (Real.sqrt 2 ^ n) • sourceDyadicCellIndicator n j

theorem sourceDyadicCellOrthonormal_orthonormal (n : ℕ) :
    Orthonormal ℝ (sourceDyadicCellOrthonormal n) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  unfold sourceDyadicCellOrthonormal
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  by_cases hij : i=j
  · subst j
    rw [sourceDyadicCellIndicator_inner_self]
    have hscale : (Real.sqrt 2 ^ n)^2 = (2:ℝ)^n := by
      calc
        (Real.sqrt 2 ^ n)^2 = Real.sqrt 2 ^ (n*2) := by rw [← pow_mul]
        _ = Real.sqrt 2 ^ (2*n) := by congr 1 <;> omega
        _ = (Real.sqrt 2 ^ 2)^n := by rw [pow_mul]
        _ = (2:ℝ)^n := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    rw [if_pos rfl]
    calc
      (Real.sqrt 2 ^ n) * ((Real.sqrt 2 ^ n) * (1 / (2:ℝ)^n))
          = (Real.sqrt 2 ^ n)^2 * (1 / (2:ℝ)^n) := by ring
      _ = 1 := by rw [hscale]; field_simp
  · rw [sourceDyadicCellIndicator_orthogonal hij]
    simp [hij]

/-- The father and all strictly coarser mothers form a basis of the actual
depth-`n` piecewise-constant source space.  The proof is finite-dimensional:
the orthonormal family has `2^n` elements, while the cell indicators give an
upper dimension bound of `2^n`. -/
theorem sourceHaarSpan_eq_piecewiseConstants (n : ℕ) :
    Submodule.span ℝ (Set.range (sourceHaarFamily n)) =
      sourceDyadicPiecewiseConstants n := by
  let W : Submodule ℝ SourceL2 := Submodule.span ℝ (Set.range (sourceHaarFamily n))
  have hle : W ≤ sourceDyadicPiecewiseConstants n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact sourceHaarFamily_mem_piecewiseConstants n a
  have hdim : Module.finrank ℝ (sourceDyadicPiecewiseConstants n) ≤ 2^n := by
    have h := finrank_range_le_card (R:=ℝ) (sourceDyadicCellIndicator n)
    change Module.finrank ℝ (sourceDyadicPiecewiseConstants n) ≤
      Fintype.card (Fin (2^n)) at h
    simpa using h
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card
    (sourceHaarFamily_orthonormal n).linearIndependent, sourceHaarIndex_card]
  simpa using hdim

/-- Exact finite Haar expansion of the actual orthogonal source projection. -/
theorem sourceDyadicOrthogonalProjection_eq_haar_sum (n : ℕ) (g : SourceL2) :
    sourceDyadicOrthogonalProjection n g =
      ∑ a : SourceHaarIndex n,
        ⟪g, sourceHaarFamily n a⟫ • sourceHaarFamily n a := by
  let e := sourceHaarFamily n
  have horth : Orthonormal ℝ e := sourceHaarFamily_orthonormal n
  let q := BrownianSharp.finiteOrthonormalProjection e g
  have hmem : q ∈ sourceDyadicPiecewiseConstants n := by
    rw [← sourceHaarSpan_eq_piecewiseConstants n]
    dsimp [q, BrownianSharp.finiteOrthonormalProjection]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hres : g - q ∈ (sourceDyadicPiecewiseConstants n)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    rw [← sourceHaarSpan_eq_piecewiseConstants n] at hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro v ⟨a, rfl⟩
      exact BrownianSharp.finiteProjection_residual_orthogonal e g
        (orthonormal_iff_ite.mp horth) a
    · simp
    · intro x y hx hy hpx hpy
      rw [inner_add_right, hpx, hpy]
      simp
    · intro c x hx hpx
      rw [inner_smul_right, hpx]
      simp
  have hproj := (sourceDyadicPiecewiseConstants n).eq_starProjection_of_mem_orthogonal
    hmem hres
  simpa [sourceDyadicOrthogonalProjection, q,
    BrownianSharp.finiteOrthonormalProjection, e] using hproj

/-- The new Haar mothers at level `n` form the orthogonal increment from
depth `n` to depth `n+1`. -/
def sourceHaarLevelSpan (n : ℕ) : Submodule ℝ SourceL2 :=
  Submodule.span ℝ (Set.range (sourceDyadicHaarMother n))

instance sourceHaarLevelSpan_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (sourceHaarLevelSpan n) := by
  unfold sourceHaarLevelSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem sourceHaarLevelSpan_orthogonal (n : ℕ) :
    sourceHaarLevelSpan n ≤ (sourceDyadicPiecewiseConstants n)ᗮ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact sourceDyadicHaarMother_mem_orthogonal_piecewise n j

theorem sourceHaarLevelSpan_le_piecewiseConstants_succ (n : ℕ) :
    sourceHaarLevelSpan n ≤ sourceDyadicPiecewiseConstants (n+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact sourceDyadicHaarMother_mem_piecewiseConstants_succ n j

theorem sourceHaarLevelSpan_finrank (n : ℕ) :
    Module.finrank ℝ (sourceHaarLevelSpan n) = 2^n := by
  unfold sourceHaarLevelSpan
  rw [finrank_span_eq_card
    (sourceDyadicHaarMother_orthonormal n).linearIndependent]
  simp

theorem sourceDyadicPiecewiseConstants_finrank (n : ℕ) :
    Module.finrank ℝ (sourceDyadicPiecewiseConstants n) = 2^n := by
  rw [← sourceHaarSpan_eq_piecewiseConstants n]
  rw [finrank_span_eq_card
    (sourceHaarFamily_orthonormal n).linearIndependent, sourceHaarIndex_card]

/-- Exact nesting decomposition of the source spaces into the old dyadic
constants and the newly added Haar level. -/
theorem sourceDyadicPiecewiseConstants_succ_eq_sup (n : ℕ) :
    sourceDyadicPiecewiseConstants (n+1) =
      sourceDyadicPiecewiseConstants n ⊔ sourceHaarLevelSpan n := by
  let U := sourceDyadicPiecewiseConstants n
  let V := sourceHaarLevelSpan n
  have hle : U ⊔ V ≤ sourceDyadicPiecewiseConstants (n+1) := by
    apply sup_le
    · exact sourceDyadicPiecewiseConstants_le_succ n
    · exact sourceHaarLevelSpan_le_piecewiseConstants_succ n
  have hinf : U ⊓ V = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxU : x ∈ U := hx.1
      have hxV : x ∈ V := hx.2
      have hxorth : x ∈ Uᗮ := sourceHaarLevelSpan_orthogonal n hxV
      have hxx : inner ℝ x x = 0 :=
        (Submodule.mem_orthogonal' U x).mp hxorth x hxU
      exact (inner_self_eq_zero.mp hxx)
    · exact bot_le
  have hsupdim : Module.finrank ℝ
      ↥(sourceDyadicPiecewiseConstants n ⊔ sourceHaarLevelSpan n) =
        (2^n : ℕ) + 2^n := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq U V
    rw [hinf, finrank_bot] at hdim
    rw [sourceDyadicPiecewiseConstants_finrank, sourceHaarLevelSpan_finrank] at hdim
    simpa [U, V] using hdim
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [sourceDyadicPiecewiseConstants_finrank, hsupdim]
  rw [pow_succ]
  omega

end BrownianSharp.AlignmentFractionalHaarProjection
