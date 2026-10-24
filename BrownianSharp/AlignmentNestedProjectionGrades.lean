import BrownianSharp.AlignmentNestedProjectionEnergy
import Mathlib.Algebra.BigOperators.Fin

/-! Explicit finite graded frames for nested source subspaces. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentNestedProjectionGrades
open AlignmentNestedProjectionBasis AlignmentNestedProjectionFrame
open AlignmentNestedProjectionEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def GradeIndex (U : ℕ → Submodule ℝ E) : ℕ → Type
  | 0 => Fin (Module.finrank ℝ (U 0))
  | n+1 => Fin (Module.finrank ℝ (increment U n))

instance gradeIndexFintype (U : ℕ → Submodule ℝ E) (g : ℕ) :
    Fintype (GradeIndex U g) := by cases g <;> dsimp [GradeIndex] <;> infer_instance

instance gradeIndexDecidableEq (U : ℕ → Submodule ℝ E) (g : ℕ) :
    DecidableEq (GradeIndex U g) := by cases g <;> dsimp [GradeIndex] <;> infer_instance

def gradeFamily (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) :
    ∀ g, GradeIndex U g → E
  | 0, i => by
      letI := hfinite 0
      exact (stdOrthonormalBasis ℝ (U 0) i : E)
  | n+1, i => by
      letI := hfinite (n+1)
      exact (incrementBasis U n i : E)

theorem gradeFamily_orthonormal (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) (g : ℕ) :
    Orthonormal ℝ (gradeFamily U hfinite g) := by
  cases g with
  | zero =>
      letI := hfinite 0
      exact (stdOrthonormalBasis ℝ (U 0)).orthonormal
  | succ n =>
      letI := hfinite (n+1)
      exact (incrementBasis U n).orthonormal

theorem gradeFamily_mem (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (g : ℕ) (i : GradeIndex U g) :
    gradeFamily U hfinite g i ∈ U g := by
  cases g with
  | zero =>
      letI := hfinite 0
      exact (stdOrthonormalBasis ℝ (U 0) i).property
  | succ n =>
      letI := hfinite (n+1)
      exact (incrementBasis U n i).property.1

theorem gradeFamily_inner_of_lt (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1))
    {g h : ℕ} (hgh : g < h) (i : GradeIndex U g) (j : GradeIndex U h) :
    ⟪gradeFamily U hfinite g i, gradeFamily U hfinite h j⟫ = 0 := by
  cases h with
  | zero => omega
  | succ h =>
      letI := hfinite (h+1)
      have hi : gradeFamily U hfinite g i ∈ U h :=
        (monotone_nat_of_le_succ hnested (Nat.le_of_lt_succ hgh))
          (gradeFamily_mem U hfinite g i)
      have hj : gradeFamily U hfinite (h+1) j ∈ (U h)ᗮ :=
        (incrementBasis U h j).property.2
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal' _ _).mp hj _ hi

abbrev GradedFrameIndex (U : ℕ → Submodule ℝ E) (N : ℕ) :=
  Σ g : Fin (N+1), GradeIndex U g.val

def gradedFrame (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) (N : ℕ) :
    GradedFrameIndex U N → E :=
  fun a => gradeFamily U hfinite a.1.val a.2

theorem gradedFrame_orthonormal (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (N : ℕ) :
    Orthonormal ℝ (gradedFrame U hfinite N) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨g,i⟩ ⟨h,j⟩
  by_cases hgh : g = h
  · subst h
    simpa [gradedFrame] using (orthonormal_iff_ite.mp
      (gradeFamily_orthonormal U hfinite g.val)) i j
  · have hne : (⟨g,i⟩ : GradedFrameIndex U N) ≠ ⟨h,j⟩ :=
      fun heq => hgh (congrArg Sigma.fst heq)
    rw [if_neg hne]
    change ⟪gradeFamily U hfinite g.val i, gradeFamily U hfinite h.val j⟫ = 0
    have hv : g.val ≠ h.val := fun heq => hgh (Fin.ext heq)
    rcases lt_or_gt_of_ne hv with hlt | hlt
    · exact gradeFamily_inner_of_lt U hfinite hnested hlt i j
    · rw [real_inner_comm]
      exact gradeFamily_inner_of_lt U hfinite hnested hlt j i

theorem gradedFrame_mem (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (N : ℕ) (a : GradedFrameIndex U N) :
    gradedFrame U hfinite N a ∈ U N :=
  (monotone_nat_of_le_succ hnested (Nat.le_of_lt_succ a.1.isLt))
    (gradeFamily_mem U hfinite _ _)

theorem gradedFrameIndex_card_eq_finrank (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (N : ℕ) :
    Fintype.card (GradedFrameIndex U N) = Module.finrank ℝ (U N) := by
  have hsum : ∀ N, (∑ g : Fin (N+1), Fintype.card (GradeIndex U g.val)) =
      Module.finrank ℝ (U N) := by
    intro N
    induction N with
    | zero => simp [GradeIndex]
    | succ N ih =>
        rw [Fin.sum_univ_castSucc]
        change (∑ g : Fin (N+1), Fintype.card (GradeIndex U g.val)) +
          Fintype.card (GradeIndex U (N+1)) = _
        rw [ih]
        change Module.finrank ℝ (U N) + Fintype.card
          (Fin (Module.finrank ℝ (increment U N))) = _
        rw [Fintype.card_fin]
        exact (increment_finrank_recurrence U hfinite hnested N).symm
  simpa only [Fintype.card_sigma] using hsum N

theorem gradedFrame_span_eq (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (N : ℕ) :
    Submodule.span ℝ (Set.range (gradedFrame U hfinite N)) = U N := by
  have horth := gradedFrame_orthonormal U hfinite hnested N
  have hle : Submodule.span ℝ (Set.range (gradedFrame U hfinite N)) ≤ U N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact gradedFrame_mem U hfinite hnested N a
  letI := hfinite N
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card horth.linearIndependent,
    gradedFrameIndex_card_eq_finrank U hfinite hnested N]

theorem gradeIndex_card_le_of_growth (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    (hnested : ∀ n, U n ≤ U (n+1)) {A : ℕ}
    (hgrowth : ∀ n, Module.finrank ℝ (U n) ≤ A*2^n) (g : ℕ) :
    Fintype.card (GradeIndex U g) ≤ A*2^g := by
  cases g with
  | zero => simpa [GradeIndex] using hgrowth 0
  | succ n =>
      simpa [GradeIndex] using increment_finrank_le_of_growth U hfinite hnested hgrowth n

end BrownianSharp.AlignmentNestedProjectionGrades
