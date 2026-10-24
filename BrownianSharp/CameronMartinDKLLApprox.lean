import BrownianSharp.CameronMartin
import BrownianSharp.KolmogorovWidth

/-!
# Uniform approximants give actual Cameron--Martin width bounds

This module isolates the deterministic reduction needed by the DKLL upper
bound.  The remaining analytic task is to construct a finite-dimensional
subspace of the *continuous-path ambient space* with a uniform approximation
estimate for the anchored integration image.  Once such an estimate is
available, the conclusion concerns the actual restricted-cube set, by the
proved identification `KdUnitCube_eq_Kd`.
-/

noncomputable section

namespace BrownianSharp.CameronMartin

open HaarQuarter

theorem kolmogorovWidth_KdUnitCube_le_of_uniform_approximation
    (d m : ℕ) (V : Submodule ℝ C(BrownianCubeAnchor d, ℝ))
    {ε : ℝ}
    (hV : Module.rank ℝ V ≤ (m : Cardinal))
    (happrox : ∀ g : AmbientL2 d, ‖g‖ ≤ 1 →
      ∃ v : V, ‖anchoredIntegrationPath g - (v : C(BrownianCubeAnchor d, ℝ))‖ ≤ ε) :
    TheoremD.Width.kolmogorovWidth (KdUnitCube d) m ≤ ENNReal.ofReal ε := by
  rw [KdUnitCube_eq_Kd d]
  unfold TheoremD.Width.kolmogorovWidth
  refine (iInf_le _ ⟨V, hV⟩).trans ?_
  unfold TheoremD.Width.approximationError
  apply iSup_le
  intro f
  obtain ⟨g, hg, hgf⟩ := f.property
  rw [← hgf]
  obtain ⟨v, herror⟩ := happrox g hg
  calc
    Metric.infEDist (anchoredIntegrationPath g) (V : Set C(BrownianCubeAnchor d, ℝ)) ≤
        edist (anchoredIntegrationPath g) (v : C(BrownianCubeAnchor d, ℝ)) :=
      Metric.infEDist_le_edist_of_mem v.property
    _ = ENNReal.ofReal
        (dist (anchoredIntegrationPath g) (v : C(BrownianCubeAnchor d, ℝ))) :=
      edist_dist _ _
    _ = ENNReal.ofReal
        ‖anchoredIntegrationPath g - (v : C(BrownianCubeAnchor d, ℝ))‖ := by
      rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal herror

end BrownianSharp.CameronMartin
