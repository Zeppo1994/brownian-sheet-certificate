import BrownianSharp.Ehrhard
import BrownianSharp.GaussianGridStatistics
import BrownianSharp.GaussianMomentRoot
import BrownianSharp.NativeMatrix
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual-statistic Gaussian lower tails

The first theorem packages the complete elementary/measure-theoretic PV
argument for an actual observable. Its only analytic input is concavity of the
Gaussian-quantile transform of its strict CDF. The later specialization
derives that input for the normalized finite-grid moment from the same
set-level Ehrhard theorem used for its p-th root.
-/

open MeasureTheory ProbabilityTheory
open BrownianSharp.Concentration

namespace BrownianSharp

/-- A positive-measure level set is excluded by the atomlessness premise. -/
theorem measureReal_strictLevel_eq_weakLevel_of_null
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (hAtom : ∀ r, μ {ω | X ω = r} = 0)
    (a : ℝ) : μ.real {ω | X ω < a} = μ.real {ω | X ω ≤ a} := by
  let L : Set Ω := {ω | X ω < a}
  let Z : Set Ω := {ω | X ω = a}
  let C : Set Ω := {ω | X ω ≤ a}
  have hdisj : Disjoint L Z := by
    rw [Set.disjoint_left]
    intro ω hωL hωZ
    simp only [L, Z, Set.mem_setOf_eq] at hωL hωZ
    linarith
  have hunion : L ∪ Z = C := by
    ext ω
    simp only [L, Z, C, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hlt : X ω < a
      · exact Or.inl hlt
      · right
        linarith
  have hZmeas : MeasurableSet Z := by
    change MeasurableSet (X ⁻¹' ({a} : Set ℝ))
    exact hXmeas (measurableSet_singleton a)
  have hsum := measureReal_union hdisj hZmeas
    (measure_ne_top μ _) (measure_ne_top μ _)
  have hzero : μ.real Z = 0 := by
    change (μ Z).toReal = 0
    rw [show Z = {ω | X ω = a} by rfl, hAtom a]
    simp
  calc
    μ.real L = μ.real L + μ.real Z := by rw [hzero, add_zero]
    _ = μ.real (L ∪ Z) := hsum.symm
    _ = μ.real C := by rw [hunion]

/-- The set-level Ehrhard theorem supplies transformed-CDF concavity for any
measurable convex observable whose strict levels are atomless. This generic
bridge is used for both the finite-grid root and its normalized p-th moment. -/
theorem transformed_cdf_concave_of_set_ehrhard
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hXconvex : ConvexOn ℝ Set.univ X)
    (hXmeas : Measurable X) (hAtom : ∀ r, μ {x | X x = r} = 0)
    (F G : ℝ → ℝ)
    (hF : ∀ s, F s = μ.real {x | X x < s})
    (hFRange : ∀ s, 0 < s → 0 < F s ∧ F s < 1)
    (hEhrhard : GaussianEhrhard E μ)
    (hG : ∀ s, G s = cdfGaussianQuantile F s) :
    ConcaveOn ℝ (Set.Ioi 0) G := by
  classical
  have hrep : ∀ s, 0 < s → F s = standardGaussianCDF (G s) := by
    intro s hs
    rw [hG]
    exact cdfGaussianQuantile_representation F (hFRange s hs).1 (hFRange s hs).2
  have hMass : ∀ s ∈ Set.Ioi (0 : ℝ), ∀ u ∈ Set.Ioi (0 : ℝ),
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        standardGaussianCDF (a • G s + b • G u) ≤ F (a • s + b • u) := by
    intro s hs u hu a b ha hb hab
    let Ks : Set E := {x | X x ≤ s}
    let Ku : Set E := {x | X x ≤ u}
    have hKsconv : Convex ℝ Ks := by
      simpa [Ks] using hXconvex.convex_le s
    have hKuconv : Convex ℝ Ku := by
      simpa [Ku] using hXconvex.convex_le u
    have hmassS : μ.real Ks = F s := by
      calc
        μ.real Ks = μ.real {x | X x < s} :=
          (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom s).symm
        _ = F s := (hF s).symm
    have hmassU : μ.real Ku = F u := by
      calc
        μ.real Ku = μ.real {x | X x < u} :=
          (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom u).symm
        _ = F u := (hF u).symm
    have hFs := hFRange s hs
    have hFu := hFRange u hu
    have hset := hEhrhard Ks Ku hKsconv hKuconv a b ha hb hab
      (by rw [hmassS]; exact hFs.1) (by rw [hmassS]; exact hFs.2)
      (by rw [hmassU]; exact hFu.1) (by rw [hmassU]; exact hFu.2)
    have hquantS : standardGaussianQuantile (μ.real Ks) = G s := by
      simpa [cdfGaussianQuantile, hmassS] using (hG s).symm
    have hquantU : standardGaussianQuantile (μ.real Ku) = G u := by
      simpa [cdfGaussianQuantile, hmassU] using (hG u).symm
    have hsubset : weightedMinkowski a Ks b Ku ⊆
        {z | X z ≤ a * s + b * u} := by
      intro z hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      change X x ≤ s at hx
      change X y ≤ u at hy
      have hconv := hXconvex.2 (Set.mem_univ x) (Set.mem_univ y)
        ha.le hb.le hab
      have hle : X (a • x + b • y) ≤ a * X x + b * X y := by
        simpa [smul_eq_mul] using hconv
      calc
        X (a • x + b • y) ≤ a * X x + b * X y := hle
        _ ≤ a * s + b * u := add_le_add
          (mul_le_mul_of_nonneg_left hx ha.le)
          (mul_le_mul_of_nonneg_left hy hb.le)
    have hmono : μ.real (weightedMinkowski a Ks b Ku) ≤ F (a * s + b * u) := by
      calc
        μ.real (weightedMinkowski a Ks b Ku) ≤
            μ.real {z | X z ≤ a * s + b * u} := MeasureTheory.measureReal_mono hsubset
        _ = μ.real {z | X z < a * s + b * u} :=
            (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom _).symm
        _ = F (a * s + b * u) := (hF _).symm
    rw [hquantS, hquantU] at hset
    have hfinal := hset.trans hmono
    simpa [smul_eq_mul] using hfinal
  apply transformed_cdf_concave_of_ehrhard_mass F G hrep hMass

end BrownianSharp
