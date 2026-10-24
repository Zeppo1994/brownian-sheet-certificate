import BrownianSharp.AlignmentNestedProjectionBasis
import BrownianSharp.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite global orthonormal frames assembled from the father space and the
successive orthogonal increments of a nested finite-dimensional filtration. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionFrame

open BrownianSharp.AlignmentNestedProjectionBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Recursive index for the basis of `U 0`, followed by each new increment. -/
def FrameIndex (U : ℕ → Submodule ℝ E) : ℕ → Type
  | 0 => Fin (Module.finrank ℝ ↥(U 0))
  | n+1 => FrameIndex U n ⊕ Fin (Module.finrank ℝ ↥(increment U n))

instance frameIndexFintype (U : ℕ → Submodule ℝ E) :
    ∀ n, Fintype (FrameIndex U n) := by
  intro n
  induction n with
  | zero => change Fintype (Fin _); infer_instance
  | succ n ih =>
      change Fintype (FrameIndex U n ⊕ Fin _)
      letI := ih
      infer_instance

instance frameIndexDecidableEq (U : ℕ → Submodule ℝ E) :
    ∀ n, DecidableEq (FrameIndex U n) := by
  intro n
  induction n with
  | zero => change DecidableEq (Fin _); infer_instance
  | succ n ih =>
      change DecidableEq (FrameIndex U n ⊕ Fin _)
      letI := ih
      infer_instance

/-- The global levelwise orthonormal family, viewed in the ambient Hilbert
space. -/
noncomputable def nestedFrame (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n)) :
    ∀ n, FrameIndex U n → E
  | 0, i => by
      letI := hfinite 0
      exact (stdOrthonormalBasis ℝ (U 0) i : E)
  | n+1, Sum.inl i => nestedFrame U hfinite n i
  | n+1, Sum.inr i => by
      letI := hfinite (n+1)
      letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
      exact (stdOrthonormalBasis ℝ (increment U n) i : E)

theorem nestedFrame_mem (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) :
    ∀ n (i : FrameIndex U n), nestedFrame U hfinite n i ∈ U n := by
  intro n
  induction n with
  | zero =>
      intro i
      letI := hfinite 0
      exact (stdOrthonormalBasis ℝ (U 0) i).2
  | succ n ih =>
      intro i
      cases i with
      | inl i => exact hnested n (ih i)
      | inr i =>
          letI := hfinite (n+1)
          letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
          exact (incrementBasis U n i).property.1

theorem nestedFrame_orthonormal (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) :
    ∀ n, Orthonormal ℝ (nestedFrame U hfinite n) := by
  intro n
  induction n with
  | zero =>
      letI := hfinite 0
      change Orthonormal ℝ
        (fun i : Fin (Module.finrank ℝ ↥(U 0)) =>
          (stdOrthonormalBasis ℝ (U 0) i : E))
      exact (stdOrthonormalBasis ℝ (U 0)).orthonormal
  | succ n ih =>
      classical
      rw [orthonormal_iff_ite]
      intro a b
      rcases a with a | a
      · rcases b with b | b
        · change ⟪nestedFrame U hfinite n a, nestedFrame U hfinite n b⟫ =
            (if Sum.inl a = Sum.inl b then (1 : ℝ) else 0)
          simp only [Sum.inl.injEq]
          exact (orthonormal_iff_ite.mp ih) a b
        · letI := hfinite (n+1)
          letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
          have ha : nestedFrame U hfinite n a ∈ U n := nestedFrame_mem U hfinite hnested n a
          have hb : nestedFrame U hfinite (n+1) (Sum.inr b) ∈ increment U n := by
            simpa [nestedFrame] using (incrementBasis U n b).property
          have hinc : increment U n ≤ (U n)ᗮ := inf_le_right
          have hborth : nestedFrame U hfinite (n+1) (Sum.inr b) ∈ (U n)ᗮ :=
            hinc hb
          have h := (Submodule.mem_orthogonal' (U n)
            (nestedFrame U hfinite (n+1) (Sum.inr b))).mp
              hborth (nestedFrame U hfinite n a) ha
          rw [real_inner_comm]
          simpa [nestedFrame] using h
      · rcases b with b | b
        · letI := hfinite (n+1)
          letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
          have ha : nestedFrame U hfinite (n+1) (Sum.inr a) ∈ increment U n := by
            simpa [nestedFrame] using (incrementBasis U n a).property
          have hb : nestedFrame U hfinite n b ∈ U n := nestedFrame_mem U hfinite hnested n b
          have h := (Submodule.mem_orthogonal' (U n)
            (nestedFrame U hfinite (n+1) (Sum.inr a))).mp
              (show nestedFrame U hfinite (n+1) (Sum.inr a) ∈ (U n)ᗮ from
                (show increment U n ≤ (U n)ᗮ from inf_le_right) ha)
              (nestedFrame U hfinite n b) hb
          simpa [nestedFrame] using h
        · letI := hfinite (n+1)
          letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
          change ⟪(incrementBasis U n a : E), (incrementBasis U n b : E)⟫ =
            (if Sum.inr a = Sum.inr b then (1 : ℝ) else 0)
          simp only [Sum.inr.injEq]
          exact (orthonormal_iff_ite.mp (incrementBasis U n).orthonormal) a b

theorem increment_finrank_recurrence (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (n : ℕ) :
    Module.finrank ℝ ↥(U (n+1)) =
      Module.finrank ℝ ↥(U n) + Module.finrank ℝ ↥(increment U n) := by
  letI := hfinite n
  letI := hfinite (n+1)
  letI : FiniteDimensional ℝ ↥(increment U n) := increment_finiteDimensional U n
  have hdecomp := succ_eq_sup_increment U n (hnested n)
  have hinf : U n ⊓ increment U n = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxorth : x ∈ (U n)ᗮ := (show increment U n ≤ (U n)ᗮ from inf_le_right) hx.2
      have hxx := (Submodule.mem_orthogonal' (U n) x).mp hxorth x hx.1
      have hx0 : x = 0 := inner_self_eq_zero.mp hxx
      simpa [hx0]
    · intro x hx
      have hx0 : x = 0 := by simpa using hx
      simpa [hx0]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (U n) (increment U n)
  rw [hinf, finrank_bot] at hdim
  have hdim' : Module.finrank ℝ ↥(U n ⊔ increment U n) =
      Module.finrank ℝ ↥(U n) + Module.finrank ℝ ↥(increment U n) := by omega
  have hdim'' := congrArg (fun V : Submodule ℝ E => Module.finrank ℝ ↥V) hdecomp
  exact hdim''.trans hdim'

theorem frameIndex_card_eq_finrank (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) :
    ∀ n, Fintype.card (FrameIndex U n) = Module.finrank ℝ ↥(U n) := by
  intro n
  induction n with
  | zero => simp [FrameIndex]
  | succ n ih =>
      change Fintype.card (FrameIndex U n ⊕ Fin (Module.finrank ℝ ↥(increment U n))) = _
      rw [Fintype.card_sum, ih, Fintype.card_fin]
      exact (increment_finrank_recurrence U hfinite hnested n).symm

theorem nestedFrame_span_eq (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) :
    ∀ n, Submodule.span ℝ (Set.range (nestedFrame U hfinite n)) = U n := by
  intro n
  have horth := nestedFrame_orthonormal U hfinite hnested n
  have hcard := frameIndex_card_eq_finrank U hfinite hnested n
  have hle : Submodule.span ℝ (Set.range (nestedFrame U hfinite n)) ≤ U n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact nestedFrame_mem U hfinite hnested n i
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card horth.linearIndependent, hcard]

/-- Exact expansion of each nested orthogonal projection using the assembled
finite global frame. -/
theorem starProjection_eq_frame_sum (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (n : ℕ) (x : E) :
    (U n).starProjection x =
      ∑ i : FrameIndex U n, ⟪x,nestedFrame U hfinite n i⟫ •
        nestedFrame U hfinite n i := by
  let e := nestedFrame U hfinite n
  have horth : Orthonormal ℝ e := nestedFrame_orthonormal U hfinite hnested n
  let q := BrownianSharp.finiteOrthonormalProjection e x
  have hmem : q ∈ U n := by
    rw [← nestedFrame_span_eq U hfinite hnested n]
    dsimp [q, BrownianSharp.finiteOrthonormalProjection]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  have hres : x-q ∈ (U n)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    rw [← nestedFrame_span_eq U hfinite hnested n] at hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro z ⟨i,rfl⟩
      exact BrownianSharp.finiteProjection_residual_orthogonal e x
        (orthonormal_iff_ite.mp horth) i
    · simp
    · intro y z hy hz hpy hpz
      rw [inner_add_right, hpy, hpz]
      simp
    · intro c y hy hpy
      rw [inner_smul_right, hpy]
      simp
  have hproj := (U n).eq_starProjection_of_mem_orthogonal hmem hres
  simpa [q, e, BrownianSharp.finiteOrthonormalProjection] using hproj

end BrownianSharp.AlignmentNestedProjectionFrame
