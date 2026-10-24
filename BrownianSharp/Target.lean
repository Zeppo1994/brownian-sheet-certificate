import BrownianSharp.PredictableSigns
import BrownianSharp.QuarterScale
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Choose.Basic

/-!
# The finite-digit target of the quarter-gain certification

Here `D = d - 1` and `N = n + 1`. Critical profiles have first/transverse total
depth `N - 1`; the drift consists of a scalar and strictly smaller total depths.
`FiniteQuarterGainStatement` is an unproved proposition, not an axiom or a
theorem declaration. Its equivalence to the rectangular Haar formulation also
remains an explicit bridge obligation.
-/

open scoped BigOperators

namespace HaarQuarter

abbrev CoefficientField (D N : ℕ) := Fin N → BoundedProfile D N → SignCube D N → ℝ

def IsCriticalProfile {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Prop :=
  l.val + grade (naturalProfile v) = N - 1

def IsCoarseProfile {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Prop :=
  l.val + grade (naturalProfile v) < N - 1

instance {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Decidable (IsCriticalProfile l v) :=
  inferInstanceAs (Decidable (l.val + grade (naturalProfile v) = N - 1))

instance {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Decidable (IsCoarseProfile l v) :=
  inferInstanceAs (Decidable (l.val + grade (naturalProfile v) < N - 1))

def CriticalFieldLegal {D N : ℕ} (α : CoefficientField D N) : Prop :=
  ∀ l v, IsCriticalProfile l v → LegalCoefficient l.val (naturalProfile v) (α l v)

def CoarseFieldLegal {D N : ℕ} (b : CoefficientField D N) : Prop :=
  ∀ l v, IsCoarseProfile l v → LegalCoefficient l.val (naturalProfile v) (b l v)

def firstDigit {D N : ℕ} (x : SignCube D N) (l : Fin N) : ℝ := sign (x.first l)

noncomputable def criticalPolynomial {D N : ℕ} (α : CoefficientField D N)
    (x : SignCube D N) : ℝ := by
  classical
  exact ∑ l, ∑ v, if IsCriticalProfile l v then
    α l v x * firstDigit x l * profileWord x v else 0

noncomputable def coarsePolynomial {D N : ℕ} (b₀ : ℝ) (b : CoefficientField D N)
    (x : SignCube D N) : ℝ := by
  classical
  exact b₀ + ∑ l, ∑ v, if IsCoarseProfile l v then
    b l v x * firstDigit x l * profileWord x v else 0

noncomputable def criticalMass {D N : ℕ} (α : CoefficientField D N) : ℝ := by
  classical
  exact mean (fairCubeLaw D N) (fun x =>
    ∑ l, ∑ v, if IsCriticalProfile l v then |α l v x| else 0)

def shapeCount (D N : ℕ) : ℕ := Nat.choose (N - 1 + D) D

noncomputable def cubeSupNorm {D N : ℕ} (F : SignCube D N → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => |F x|)

theorem cubeSupNorm_pointwise {D N : ℕ} (F : SignCube D N → ℝ) (x : SignCube D N) :
    |F x| ≤ cubeSupNorm F := Finset.le_sup' (f := fun x => |F x|) (Finset.mem_univ x)

theorem cubeSupNorm_nonneg {D N : ℕ} (F : SignCube D N → ℝ) : 0 ≤ cubeSupNorm F :=
  (abs_nonneg (F ⟨fun _ => false, fun _ _ => false⟩)).trans (cubeSupNorm_pointwise F _)

theorem normalizedQuery_bound {D N : ℕ} (F : SignCube D N → ℝ)
    (hK : 0 < cubeSupNorm F) (x : SignCube D N) : |F x / cubeSupNorm F| ≤ 1 := by
  rw [abs_div, abs_of_pos hK]
  exact (div_le_iff₀ hK).mpr (by simpa using cubeSupNorm_pointwise F x)

theorem criticalMass_nonneg {D N : ℕ} (α : CoefficientField D N) : 0 ≤ criticalMass α := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg (le_of_lt ((fairCubeLaw D N).positive x))
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro v hv
  split_ifs
  · exact abs_nonneg _
  · exact le_refl 0

/-- The full strict-quarter finite-digit gain to be proved. The common depth
threshold precedes all coefficient fields and all postchosen drifts. -/
def FiniteQuarterGainStatement : Prop :=
  ∀ D : ℕ, 2 ≤ D →
    ∀ η : ℝ, 0 < η → η < 1 / 4 →
      ∀ c : ℝ, 0 < c → c < 1 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
          ∀ α : CoefficientField D N, CriticalFieldLegal α →
            ∀ (b₀ : ℝ) (b : CoefficientField D N), CoarseFieldLegal b →
              c * (N : ℝ) ^ η * criticalMass α / Real.sqrt (shapeCount D N : ℝ) ≤
                cubeSupNorm (fun x => criticalPolynomial α x + coarsePolynomial b₀ b x)

end HaarQuarter
