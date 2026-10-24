import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-! Uniform finite-family convergence from geometric squared-error bounds. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace BrownianSharp.AlignmentUniformGeometricApproximation

theorem uniform_small_of_squared_geometric
    {ι T : Type*} [Fintype ι] (err : ι → ℕ → T → ℝ)
    (C q : ι → ℝ) (hq0 : ∀ i, 0≤q i) (hq1 : ∀ i, q i<1)
    (herr0 : ∀ i n t, 0≤err i n t)
    (herr : ∀ i n t, (err i n t)^2≤C i*(q i)^n)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ n : ℕ, ∀ i t, err i n t≤δ := by
  classical
  have hlim (i : ι) : Tendsto (fun n : ℕ => C i*(q i)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (hq0 i) (hq1 i)).const_mul (C i)
  have hsmall (i : ι) : ∃ N : ℕ, ∀ n≥N, C i*(q i)^n<δ^2 := by
    have he := (hlim i).eventually (Iio_mem_nhds (sq_pos_of_pos hδ))
    exact Filter.eventually_atTop.mp he
  choose N hN using hsmall
  let n := Finset.univ.sup N
  refine ⟨n,?_⟩
  intro i t
  have hin : N i≤n := Finset.le_sup (Finset.mem_univ i)
  have he : (err i n t)^2≤δ^2 := (herr i n t).trans (hN i n hin).le
  exact (sq_le_sq₀ (herr0 i n t) hδ.le).mp he

end BrownianSharp.AlignmentUniformGeometricApproximation
