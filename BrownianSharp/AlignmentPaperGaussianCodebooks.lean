import BrownianSharp.AlignmentPaperGaussianFeatureNets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperGaussianCodebooks
open AlignmentCompactFeatureBall

/-- A finite net of the dilated Cameron--Martin ball can be indexed as an
actual codebook containing zero, at the cost of one extra representative. -/
theorem featurePathLaw_exists_codebook
    {α Ω H : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α,ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P=0)
    (K : C(α,H)) (a : α) (ha : K a ≠ 0)
    (hcov : ∀ x y, cov[fun ω => F ω x,fun ω => F ω y;P]=inner ℝ (K x) (K y))
    (R : ℝ) (hR : 0 < R) (ε : ℝ≥0) (hε : 0 < ε) (φ : ℝ)
    (hp : 0 < (P.map F).real (Metric.closedBall 0 (ε:ℝ)))
    (hφ : -Real.log ((P.map F).real (Metric.closedBall 0 (ε:ℝ))) ≤ φ) :
    ∃ N : ℕ, ∃ hN : 0 < N, ∃ c : Fin N → C(α,ℝ),
      (∃ i₀, c i₀=0) ∧
      (∀ i, c i ∈ (fun f : C(α,ℝ) => R • f) '' featureBall K) ∧
      (∀ f ∈ (fun h : C(α,ℝ) => R • h) '' featureBall K,
        ∃ i, ‖f-c i‖ ≤ 2*(ε:ℝ)) ∧
      (N:ℝ) ≤ Real.exp (R^2/2+φ)+1 := by
  classical
  obtain ⟨S,hSsub,hSfin,hScover,hbudget⟩ :=
    AlignmentPaperGaussianFeatureNets.featurePathLaw_exists_net
      F hF hX hmean K a ha hcov R hR ε hε
  letI := hSfin.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let c : Fin (n+1) → C(α,ℝ) := Fin.cases 0 (fun i => (e i).val)
  have hzero : (0:C(α,ℝ)) ∈ featureBall K := by
    refine ⟨0, by simp, ?_⟩
    ext x
    simp [AlignmentCompactFeatureBall.featurePath]
  refine ⟨n+1, by omega, c, ⟨0,rfl⟩, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨0,hzero,by simp [c]⟩
    · exact hSsub (e j).property
  · intro f hf
    obtain ⟨s,hs,hfs⟩ := hScover hf
    refine ⟨(e.symm ⟨s,hs⟩).succ, ?_⟩
    have hdist : ‖f-s‖ ≤ 2*(ε:ℝ) := by
      change edist f s ≤ ((2*ε:ℝ≥0):ℝ≥0∞) at hfs
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*(ε:ℝ))).mp
      simpa only [edist_dist, dist_eq_norm, ENNReal.coe_mul, ENNReal.coe_ofNat,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_coe_nnreal] using hfs
    simpa [c] using hdist
  · have hcard := AlignmentPaperGaussianFeatureNets.cardinal_le_exp_of_shift_budget
      (N := Nat.card S) (a := R^2/2) hp (by simpa [neg_div] using hbudget) hφ
    have hn : (n:ℝ) ≤ Real.exp (R^2/2+φ) := by
      simpa [n, Nat.card_eq_fintype_card] using hcard
    push_cast
    linarith

end BrownianSharp.AlignmentPaperGaussianCodebooks
