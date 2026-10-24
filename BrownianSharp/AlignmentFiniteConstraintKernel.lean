import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! A finite family of linear jet constraints removes at most its cardinality
from the dimension of a coefficient space. -/

namespace BrownianSharp.AlignmentFiniteConstraintKernel

/-- Bundle a finite family of scalar linear constraints as one linear map. -/
def finiteConstraintMap {D m : ℕ}
    (L : Fin m → (Fin D → ℝ) →ₗ[ℝ] ℝ) :
    (Fin D → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun c j := L j c
  map_add' c e := by
    ext j
    exact map_add (L j) c e
  map_smul' a c := by
    ext j
    exact map_smul (L j) a c

/-- The common kernel of `m` scalar linear constraints in `D` real
coefficients has dimension at least `D-m`. -/
theorem finiteConstraintKernel_finrank_lower {D m : ℕ}
    (L : Fin m → (Fin D → ℝ) →ₗ[ℝ] ℝ) :
    D - m ≤ Module.finrank ℝ (finiteConstraintMap L).ker := by
  classical
  let f := finiteConstraintMap L
  have hdim := f.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ m := by
    calc
      Module.finrank ℝ (LinearMap.range f) ≤
          Module.finrank ℝ (Fin m → ℝ) := (LinearMap.range f).finrank_le
      _ = m := by simp
  change Module.finrank ℝ (LinearMap.range (finiteConstraintMap L)) ≤ m at hrange
  have hsource : Module.finrank ℝ (Fin D → ℝ) = D := by simp
  rw [hsource] at hdim
  change Module.finrank ℝ (LinearMap.range (finiteConstraintMap L)) +
    Module.finrank ℝ (finiteConstraintMap L).ker = D at hdim
  omega

end BrownianSharp.AlignmentFiniteConstraintKernel
