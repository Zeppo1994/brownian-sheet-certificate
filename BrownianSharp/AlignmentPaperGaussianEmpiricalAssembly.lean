import BrownianSharp.AlignmentPaperGaussianCodebooks
import BrownianSharp.AlignmentPaperEmpiricalGoodTail
import BrownianSharp.AlignmentPaperCompactTubes
import BrownianSharp.AlignmentPaperGaussianEnlargementTail

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperGaussianEmpiricalAssembly
open AlignmentCompactFeatureBall AlignmentPaperCompactTubes
open AlignmentPaperEmpiricalWasserstein

/-- The actual feature net, tube probability and fourth moment together
control iid empirical Wasserstein error. The tube-mass premise is displayed
explicitly; the unconditional Gaussian enlargement provider is separate. -/
theorem expected_empirical_bound_of_feature_tube_mass
    {α Ω H : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α,ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P=0)
    (K : C(α,H)) (a : α) (ha : K a≠0)
    (hcov : ∀ x y, cov[fun ω => F ω x,fun ω => F ω y;P]=inner ℝ (K x) (K y))
    (R : ℝ) (hR : 0<R) (ε : ℝ≥0) (hε : 0<ε) (φ s : ℝ)
    (hφ : 0≤φ) (hs : 0≤s) (hRlarge : Real.sqrt (2*φ)+s≤R)
    (hp1 : (P.map F).real (Metric.closedBall 0 (ε:ℝ))<1)
    (hlog : -Real.log ((P.map F).real (Metric.closedBall 0 (ε:ℝ)))≤φ)
    (hmass : Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile
        ((P.map F).real (Metric.closedBall 0 (ε:ℝ)))+R) ≤
      (P.map F).real (closedTube ((fun f:C(α,ℝ)=>R • f) '' featureBall K) ε))
    (M4 : ℝ≥0∞)
    (hM4 : (∫⁻ f:C(α,ℝ), edist f 0^4 ∂P.map F)≤M4) :
    ∃ N : ℕ, 0<N ∧ (N:ℝ)≤Real.exp (R^2/2+φ)+1 ∧
      ∀ m : ℕ, ∀ hm : 0<m,
        (∫⁻ x:Fin m→C(α,ℝ), wassersteinTwo (P.map F) (empiricalMeasure m hm x)
          ∂iidSampleLaw (P.map F) m) ≤
        ennrealSqrt (3*((2:ℝ≥0∞)*
          ((ENNReal.ofReal (3*(ε:ℝ)))^2+ennrealSqrt M4*
            ennrealSqrt (ENNReal.ofReal (Real.exp (-s^2/2))))+
          (ENNReal.ofReal (2*R*‖K‖))^2*
            ENNReal.ofReal ((1/2:ℝ)*Real.sqrt ((N:ℝ)/m)))) := by
  classical
  let μ := P.map F
  let KR := (fun f:C(α,ℝ)=>R • f) '' featureBall K
  let G := closedTube KR (ε:ℝ)
  have hp : 0<μ.real (Metric.closedBall 0 (ε:ℝ)) :=
    AlignmentPaperMaternSmallBall.centered_path_closedBall_pos F hF hX hmean ε hε
  obtain ⟨N,hN,c,⟨i₀,hi₀⟩,hc,hcover,hcard⟩ :=
    AlignmentPaperGaussianCodebooks.featurePathLaw_exists_codebook
      F hF hX hmean K a ha hcov R hR ε hε φ hp hlog
  have hcpt : IsCompact KR := (featureBall_isCompact K).image (by fun_prop)
  have hzero : (0:C(α,ℝ)) ∈ featureBall K := by
    refine ⟨0,by simp,?_⟩
    ext x
    simp [featurePath]
  have hne : KR.Nonempty := ⟨0,0,hzero,by simp⟩
  have hG : MeasurableSet G := (closedTube_isClosed hcpt hne ε).measurableSet
  have htail : μ Gᶜ≤ENNReal.ofReal (Real.exp (-s^2/2)) :=
    AlignmentPaperGaussianEnlargementTail.complement_le_of_enlargement
      μ hG hp hp1 hφ hlog hs hRlarge hmass
  have hcoverG : ∀ f ∈ G, ∃ i:Fin N, edist f (c i)≤ENNReal.ofReal (3*(ε:ℝ)) := by
    rintro f ⟨g,hg,hfg⟩
    obtain ⟨i,hi⟩ := hcover g hg
    refine ⟨i,?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hgi : dist g (c i)≤2*(ε:ℝ) := by simpa [dist_eq_norm] using hi
    calc
      dist f (c i)≤dist f g+dist g (c i) := dist_triangle _ _ _
      _ ≤ (ε:ℝ)+2*(ε:ℝ) := add_le_add hfg hgi
      _ = 3*(ε:ℝ) := by ring
  have hdiam : ∀ i j, edist (c i) (c j)^2≤(ENNReal.ofReal (2*R*‖K‖))^2 := by
    intro i j
    apply pow_le_pow_left₀ bot_le _ 2
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal
      (AlignmentPaperGaussianFeatureNets.scaled_featureBall_diameter_le K R hR.le (hc i) (hc j))
  refine ⟨N,hN,hcard,?_⟩
  intro m hm
  exact AlignmentPaperEmpiricalGoodTail.expected_empirical_wassersteinTwo_le_good_tail
    μ m hm N hN c i₀ hi₀ G hG (ENNReal.ofReal (3*(ε:ℝ))) M4
      (ENNReal.ofReal (Real.exp (-s^2/2))) (ENNReal.ofReal (2*R*‖K‖)) hcoverG hM4 htail hdiam

end BrownianSharp.AlignmentPaperGaussianEmpiricalAssembly
