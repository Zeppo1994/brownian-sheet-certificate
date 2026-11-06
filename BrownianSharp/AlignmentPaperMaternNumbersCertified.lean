import BrownianSharp.AlignmentPaperMaternFinal

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperMaternNumbersCertified
open AlignmentOperatorNumbers AlignmentPaperGaussianFeatureBridge

/-- The entropy and strict-index Kolmogorov part of Corollary 5.3. Constants
precede all probability-space realizations. The small-deviation equivalence
is deliberately not included in this statement. -/
def MaternCMNumbersStatement : Prop :=
  ∀ (d:ℕ), 2≤d → ∀ (κ c:Fin d→ℝ) (h:ℝ),
    (∀i,0<κ i) → (∀i,0<c i) → 0<h →
    ∃ ce Ce cw Cw:ℝ, 0<ce ∧ 0<Ce ∧ 0<cw ∧ 0<Cw ∧
      ∃ k₀:ℕ, 3≤k₀ ∧
        ∀ {Ω:Type*} [MeasurableSpace Ω] {P:Measure Ω} [IsProbabilityMeasure P]
          (X:HaarQuarter.BrownianCubeAnchor d→Ω→ℝ)
          (hX:∀x,MemLp (X x) 2 P)
          (hmean:∀x,∫ω,X x ω∂P=0)
          (hcov:∀x y,cov[X x,X y;P]=
            ∏i,c i*AlignmentMaternSpectralFeature.stationaryCovariance
              (κ i) h (x.val i) (y.val i)),
          ∀ k:ℕ,k₀≤k →
            ENNReal.ofReal (ce*logarithmicIndexRate (h+1/2)
              ((h+1/2)*(d-1:ℕ)+1/2) k)≤
                HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hX) ∧
            HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hX)≤
              ENNReal.ofReal (Ce*logarithmicIndexRate (h+1/2)
                ((h+1/2)*(d-1:ℕ)+1/2) k) ∧
            ENNReal.ofReal (cw*logarithmicIndexRate (h+1/2)
              ((h+1/2)*(d-1:ℕ)+1/2) k)≤
                operatorKolmogorovNumber (intrinsicGaussianCMUnitBall X hX) k ∧
            operatorKolmogorovNumber (intrinsicGaussianCMUnitBall X hX) k≤
              ENNReal.ofReal (Cw*logarithmicIndexRate (h+1/2)
                ((h+1/2)*(d-1:ℕ)+1/2) k)

theorem maternCMNumbers_certified : MaternCMNumbersStatement := by
  intro d hd κ c h hκ hc hh
  obtain ⟨ce,Ce,hce,hCe,ke,hke,he⟩ :=
    AlignmentPaperMaternUpper.maternRawSpectral_intrinsicCM_entropy_two_sided
      hd κ c h hκ hc hh
  obtain ⟨cw,Cw,hcw,hCw,kw,hkw,hw⟩ :=
    AlignmentPaperMaternFinal.maternRawSpectral_intrinsicCM_operator_width_two_sided
      hd κ c h hκ hc hh
  refine ⟨ce,Ce,cw,Cw,hce,hCe,hcw,hCw,max ke kw,
    hkw.trans (le_max_right _ _),?_⟩
  intro Ω hΩ P hP X hX hmean hcov k hk
  have he':=he X hX hmean hcov k ((le_max_left _ _).trans hk)
  have hw':=hw X hX hmean hcov k ((le_max_right _ _).trans hk)
  exact ⟨he'.1,he'.2,hw'.1,hw'.2⟩

end BrownianSharp.AlignmentPaperMaternNumbersCertified
