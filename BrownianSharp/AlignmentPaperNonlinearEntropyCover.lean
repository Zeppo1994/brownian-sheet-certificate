import BrownianSharp.Carl
import Mathlib.Data.Set.Card.Arithmetic

/-! A finite-family volumetric cover, for adaptive approximants.

Each member of the source union may use its own subspace.  This is the
finite-dimensional coding step needed when the sparse head depends on the
input; it does not replace that family by one fixed subspace. -/

noncomputable section
open Set
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperNonlinearEntropyCover

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def familyBallSource {Q : ℕ} (V : Fin Q → Submodule ℝ X) (R : ℝ) : Set X :=
  ⋃ i, HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
    (V i) R

/-- A bounded ball in a finite union of labelled finite-dimensional spaces has
an ambient cover whose count is the number of labels times the usual
volumetric count.  The labels can vary with the point being covered. -/
theorem exists_family_submodule_ball_cover (Q : ℕ)
    (V : Fin Q → Submodule ℝ X)
    [∀ i, FiniteDimensional ℝ (V i)]
    [∀ i, CompleteSpace (V i)] [∀ i, MeasurableSpace (V i)]
    [∀ i, BorelSpace (V i)]
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ C : Set X, C.Finite ∧
      C.encard ≤ (Q : ℕ∞) *
        ↑(Nat.ceil ((1 + 2 * R / ε) ^
          (Finset.univ.sup fun i : Fin Q => Module.finrank ℝ (V i)))) ∧
      Metric.IsCover (NNReal.mk ε hε.le) (familyBallSource V R) C := by
  classical
  let r : ℕ := Finset.univ.sup fun i : Fin Q => Module.finrank ℝ (V i)
  let P : Fin Q → Carl.CoverPiece X := fun i => Classical.choose
    (Carl.exists_submodule_ball_piece_general (V i) hR hε)
  let C₀ : Fin Q → Set X := fun i => (P i).centers
  have hC₀ (i : Fin Q) :
      (C₀ i).Finite ∧
        Metric.IsCover (NNReal.mk ε hε.le)
          (HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
            (V i) R) (C₀ i) ∧
        (C₀ i).encard ≤
          ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ (V i))) := by
    have hp := Classical.choose_spec
      (Carl.exists_submodule_ball_piece_general (V i) hR hε)
    have hP : (P i).source =
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V i) R ∧
        (P i).radius = NNReal.mk ε hε.le ∧
        (P i).centers.encard ≤
          ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ (V i))) := by
      simpa [P] using hp
    have hcoveri : Metric.IsCover (NNReal.mk ε hε.le)
        (HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V i) R) (P i).centers := by
      simpa only [hP.1, hP.2.1] using (P i).cover
    exact ⟨(P i).centers_finite,
      by simpa [C₀, hP.1] using hcoveri,
      hP.2.2⟩
  let C : Set X := ⋃ i, C₀ i
  refine ⟨C, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun i => (hC₀ i).1
  · calc
      C.encard ≤ ∑ i : Fin Q, (C₀ i).encard := by
        simpa [C] using Set.encard_iUnion_le_of_fintype C₀
      _ ≤ ∑ i : Fin Q,
          ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ (V i))) :=
        Finset.sum_le_sum fun i _ => (hC₀ i).2.2
      _ ≤ ∑ _i : Fin Q, ↑(Nat.ceil ((1 + 2 * R / ε) ^ r)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast Nat.ceil_mono (show
          (1 + 2 * R / ε) ^ Module.finrank ℝ (V i) ≤
            (1 + 2 * R / ε) ^ r from by
              have hbase : 1 ≤ 1 + 2 * R / ε := by
                have hdiv : 0 ≤ 2 * R / ε :=
                  div_nonneg (by positivity) hε.le
                linarith
              have hi : Module.finrank ℝ (V i) ≤
                  Finset.univ.sup (fun j : Fin Q => Module.finrank ℝ (V j)) :=
                Finset.le_sup
                  (f := fun j : Fin Q => Module.finrank ℝ (V j))
                  (Finset.mem_univ i)
              exact (pow_le_pow_right₀ hbase hi))
      _ = (Q : ℕ∞) * ↑(Nat.ceil ((1 + 2 * R / ε) ^ r)) := by
        simp [Finset.sum_const, nsmul_eq_mul, r]
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    obtain ⟨y, hy, hdist⟩ := (hC₀ i).2.1 hxi
    refine ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hdist⟩

/-- Package the adaptive family cover as one Carl increment. -/
theorem exists_family_submodule_ball_piece (Q : ℕ)
    (V : Fin Q → Submodule ℝ X)
    [∀ i, FiniteDimensional ℝ (V i)]
    [∀ i, CompleteSpace (V i)] [∀ i, MeasurableSpace (V i)]
    [∀ i, BorelSpace (V i)]
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ p : Carl.CoverPiece X,
      p.source = familyBallSource V R ∧
      p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤ (Q : ℕ∞) *
        ↑(Nat.ceil ((1 + 2 * R / ε) ^
          (Finset.univ.sup fun i : Fin Q => Module.finrank ℝ (V i)))) := by
  obtain ⟨C, hC, hcard, hcover⟩ :=
    exists_family_submodule_ball_cover Q V hR hε
  exact ⟨⟨familyBallSource V R, C, NNReal.mk ε hε.le, hcover, hC⟩,
    rfl, rfl, hcard⟩

/-! The next theorem is the nonlinear (input-dependent) telescoping step.
The approximant at each scale may be selected from a different subspace for
each input.  Only the corresponding increment sets and their finite covers
are fixed in advance. -/

/-- Entropy cover from adaptive approximants and finite increment covers.
`A j x` need not lie in one common subspace as `x` varies; the choices are
encoded by the supplied source sets `S j`. -/
theorem entropyNumber_le_of_adaptive_increment_chain
    (K : Set X) (L k : ℕ)
    (A : Fin (L + 1) → {x : X // x ∈ K} → X)
    (S : Fin L → Set X) (tail : Set X)
    (pieces : List (Carl.CoverPiece X)) (exponents : List ℕ)
    (hstart : ∀ x : {x : X // x ∈ K}, A 0 x = 0)
    (hstep : ∀ (j : Fin L) (x : {x : X // x ∈ K}),
      A j.succ x - A j.castSucc x ∈ S j)
    (htail : ∀ x : {x : X // x ∈ K}, (x : X) - A (Fin.last L) x ∈ tail)
    (hsources : pieces.map Carl.CoverPiece.source =
      ({0} :: List.ofFn S ++ [tail]))
    (hcounts : List.Forall₂
      (fun p exponent => p.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
      pieces exponents)
    (hexponent : exponents.sum ≤ k - 1) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ Carl.sumRadii pieces := by
  have hchain : ∀ x ∈ K, ∃ approximants : List X,
      List.Forall₂ (fun z p => z ∈ p.source)
        (Carl.chainIncrements x approximants) pieces := by
    intro x hx
    let x' : {x : X // x ∈ K} := ⟨x, hx⟩
    refine ⟨List.ofFn (fun j : Fin (L + 1) => A j x'), ?_⟩
    have htail' := Carl.forall₂_tailIncrements_ofFn
      (fun j => A j x') S tail (fun j => hstep j x') (htail x')
    have hrel : List.Forall₂ (fun z T => z ∈ T)
        (Carl.chainIncrements x (List.ofFn (fun j : Fin (L + 1) => A j x')))
        ({0} :: List.ofFn S ++ [tail]) := by
      have hfirst : A 0 x' ∈ ({0} : Set X) := by simp [hstart x']
      simpa [Carl.chainIncrements, hstart x'] using
        (List.Forall₂.cons (R := fun z T => z ∈ T) hfirst htail')
    apply (List.forall₂_map_right_iff
      (R := fun z T => z ∈ T) (f := Carl.CoverPiece.source)).mp
    rw [hsources]
    exact hrel
  exact Carl.entropyNumber_le_of_dyadic_approximation_chain
    K pieces k exponents hchain hcounts hexponent

end BrownianSharp.AlignmentPaperNonlinearEntropyCover
