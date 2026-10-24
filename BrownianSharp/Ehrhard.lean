import BrownianSharp.Concentration

/-!
# Ehrhard interface for finite-grid homogeneous convex statistics

This file isolates the geometric theorem still needed by the Brownian
concentration argument. It does not postulate Ehrhard as an axiom: the
conditional theorem below takes the classical set-level Ehrhard inequality as
an explicit argument and proves that it supplies the mass interpolation
premise used by the Paouris--Valettas reduction.
-/

namespace BrownianSharp.Concentration

open MeasureTheory ProbabilityTheory

/-- The affine Minkowski combination of two sets, written in witness form so
that no measurability assumptions are hidden in its definition. -/
def weightedMinkowski {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (A : Set E) (b : ℝ) (B : Set E) : Set E :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = a • x + b • y}

/-- Set-level finite-dimensional Ehrhard inequality in the quantile form needed
here. This is the remaining geometric theorem: in applications, `μ` is the
standard product Gaussian measure and `A`, `B` are convex sublevel sets. -/
def GaussianEhrhard (E : Type*) [MeasurableSpace E] [AddCommGroup E]
    [Module ℝ E] (μ : Measure E) : Prop :=
  ∀ A B : Set E, Convex ℝ A → Convex ℝ B →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      0 < μ.real A → μ.real A < 1 → 0 < μ.real B → μ.real B < 1 →
        standardGaussianCDF
            (a * standardGaussianQuantile (μ.real A) +
             b * standardGaussianQuantile (μ.real B)) ≤
          μ.real (weightedMinkowski a A b B)

/-- A closed root sublevel has the same Gaussian mass as the strict CDF level,
provided the root has no atom at that level. -/
theorem finiteGridRoot_closed_sublevel_mass_eq_cdf
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ)
    (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (hXmeas : Measurable (finiteGridRoot p A))
    (hAtom : ∀ r, μ {x | finiteGridRoot p A x = r} = 0)
    (s : ℝ) :
    μ.real {x | finiteGridRoot p A x ≤ s} =
      μ.real {x | finiteGridRoot p A x < s} := by
  let L : Set (κ → ℝ) := {x | finiteGridRoot p A x < s}
  let Z : Set (κ → ℝ) := {x | finiteGridRoot p A x = s}
  let C : Set (κ → ℝ) := {x | finiteGridRoot p A x ≤ s}
  have hdisj : Disjoint L Z := by
    rw [Set.disjoint_left]
    intro x hxL hxZ
    simp only [L, Z, Set.mem_setOf_eq] at hxL hxZ
    linarith
  have hunion : L ∪ Z = C := by
    ext x
    simp only [L, Z, C, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hx | hx) <;> linarith
    · intro hx
      by_cases hlt : finiteGridRoot p A x < s
      · exact Or.inl hlt
      · right
        have hge : s ≤ finiteGridRoot p A x := le_of_not_gt hlt
        linarith
  have hZmeas : MeasurableSet Z := by
    change MeasurableSet ((finiteGridRoot p A) ⁻¹' ({s} : Set ℝ))
    exact hXmeas (measurableSet_singleton s)
  have hsum := measureReal_union hdisj hZmeas
    (measure_ne_top μ _) (measure_ne_top μ _)
  have hzero : μ.real Z = 0 := by
    change (μ Z).toReal = 0
    rw [show Z = {x | finiteGridRoot p A x = s} by rfl, hAtom s]
    simp
  calc
    μ.real C = μ.real (L ∪ Z) := by rw [← hunion]
    _ = μ.real L + μ.real Z := hsum
    _ = μ.real L := by rw [hzero, add_zero]

/-- The level sublevels of the finite-grid root are convex. This follows from
the already-certified convexity of the root itself. -/
theorem finiteGridRoot_sublevel_convex
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (s : ℝ) :
    Convex ℝ {x : κ → ℝ | finiteGridRoot p A x ≤ s} := by
  simpa using (finiteGridRoot_convexOn p hp A).convex_le s

/-- Ehrhard for arbitrary convex sets implies the exact mass-level inequality
for the finite-grid root. The proof uses convexity to put the Minkowski sum of
two sublevels inside the interpolated sublevel and atomlessness to switch
between closed-set mass and the strict CDF. Thus no distributional or
quantile-representation hypotheses are left implicit in the reduction. -/
theorem finiteGridRoot_ehrhard_mass_of_set_ehrhard
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ)
    (hnonzero : ∃ i k, A i k ≠ 0)
    (hEhrhard : GaussianEhrhard (κ → ℝ)
      (Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1))) :
    let μ : Measure (κ → ℝ) :=
      Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1)
    let X : (κ → ℝ) → ℝ := finiteGridRoot p A
    let F : ℝ → ℝ := fun s => μ.real {x | X x < s}
    let G : ℝ → ℝ := cdfGaussianQuantile F
    ∀ s ∈ Set.Ioi (0 : ℝ), ∀ u ∈ Set.Ioi (0 : ℝ),
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        standardGaussianCDF (a • G s + b • G u) ≤ F (a • s + b • u) := by
  classical
  let μ : Measure (κ → ℝ) :=
    Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1)
  let X : (κ → ℝ) → ℝ := finiteGridRoot p A
  let F : ℝ → ℝ := fun s => μ.real {x | X x < s}
  let G : ℝ → ℝ := cdfGaussianQuantile F
  have hXmeas : Measurable X := (finiteGridRoot_continuous p hp A).measurable
  have hAtom : ∀ r, μ {x | X x = r} = 0 := by
    intro r
    exact finiteGridRoot_all_levels_standardGaussian_measure_zero_of_nonzero_entry
      p hp A hnonzero r
  change ∀ s ∈ Set.Ioi (0 : ℝ), ∀ u ∈ Set.Ioi (0 : ℝ),
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        standardGaussianCDF (a • G s + b • G u) ≤ F (a • s + b • u)
  intro s hs u hu a b ha hb hab
  let Ks : Set (κ → ℝ) := {x | X x ≤ s}
  let Ku : Set (κ → ℝ) := {x | X x ≤ u}
  have hKsconv : Convex ℝ Ks := by
    simpa [Ks, X] using finiteGridRoot_sublevel_convex p hp A s
  have hKuconv : Convex ℝ Ku := by
    simpa [Ku, X] using finiteGridRoot_sublevel_convex p hp A u
  have hmassS : μ.real Ks = F s := by
    dsimp [Ks, F, X]
    exact finiteGridRoot_closed_sublevel_mass_eq_cdf p hp A μ hXmeas hAtom s
  have hmassU : μ.real Ku = F u := by
    dsimp [Ku, F, X]
    exact finiteGridRoot_closed_sublevel_mass_eq_cdf p hp A μ hXmeas hAtom u
  have hFs := finiteGridRoot_cdf_between_zero_one p hp A
    (finiteGridRoot_exists_pos_of_nonzero_entry p hp A hnonzero) hs
  have hFu := finiteGridRoot_cdf_between_zero_one p hp A
    (finiteGridRoot_exists_pos_of_nonzero_entry p hp A hnonzero) hu
  have hmassS0 : 0 < μ.real Ks := by rw [hmassS]; exact hFs.1
  have hmassS1 : μ.real Ks < 1 := by rw [hmassS]; exact hFs.2
  have hmassU0 : 0 < μ.real Ku := by rw [hmassU]; exact hFu.1
  have hmassU1 : μ.real Ku < 1 := by rw [hmassU]; exact hFu.2
  have hset := hEhrhard Ks Ku hKsconv hKuconv a b ha hb hab
    hmassS0 hmassS1 hmassU0 hmassU1
  have hquantS : standardGaussianQuantile (μ.real Ks) = G s := by
    simp [G, cdfGaussianQuantile, hmassS]
  have hquantU : standardGaussianQuantile (μ.real Ku) = G u := by
    simp [G, cdfGaussianQuantile, hmassU]
  have hsubset : weightedMinkowski a Ks b Ku ⊆
      {z | X z ≤ a * s + b * u} := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    change X x ≤ s at hx
    change X y ≤ u at hy
    have hconv := (finiteGridRoot_convexOn p hp A).2
      (by trivial : x ∈ Set.univ) (by trivial : y ∈ Set.univ)
      ha.le hb.le hab
    have hle : X (a • x + b • y) ≤ a * X x + b * X y := by
      simpa [smul_eq_mul] using hconv
    change X (a • x + b • y) ≤ a * s + b * u
    calc
      X (a • x + b • y) ≤ a * X x + b * X y := hle
      _ ≤ a * s + b * u := add_le_add (mul_le_mul_of_nonneg_left hx ha.le)
            (mul_le_mul_of_nonneg_left hy hb.le)
  have hmono : μ.real (weightedMinkowski a Ks b Ku) ≤ F (a * s + b * u) := by
    calc
      μ.real (weightedMinkowski a Ks b Ku) ≤
          μ.real {z | X z ≤ a * s + b * u} := MeasureTheory.measureReal_mono hsubset
      _ = μ.real {z | X z < a * s + b * u} :=
          finiteGridRoot_closed_sublevel_mass_eq_cdf p hp A μ hXmeas hAtom _
      _ = F (a * s + b * u) := rfl
  rw [hquantS, hquantU] at hset
  have hfinal := hset.trans hmono
  simpa [smul_eq_mul] using hfinal

end BrownianSharp.Concentration
