import BrownianSharp.AlignmentPaperQuantizationAtomicBridge
import BrownianSharp.AlignmentPaperEmpiricalCellLift
import BrownianSharp.AlignmentPaperContinuousGaussianFernique
import BrownianSharp.BrownianSheetOnCube
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentGaussianBochner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Deterministic adaptive integration and first-order quantization

This file formalizes the sequential exact-evaluation model and the two
geometric ingredients of the deterministic integration identity.
-/

open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperDeterministicIntegration

universe u

variable {X : Type u} [MetricSpace X]

/-- A deterministic query tree with exactly `n` exact evaluations. At each
node it chooses a point from the previous responses; at depth zero it returns
a real number. Repeated queries are permitted. -/
inductive QueryTree (X : Type u) : ℕ → Type u
  | output : ℝ → QueryTree X 0
  | query {n : ℕ} : X → (ℝ → QueryTree X n) → QueryTree X (n + 1)

/-- A deterministic sequential algorithm using at most the indicated number
of evaluations. `stop` can occur at any remaining budget. -/
inductive AtMostQueryTree (X : Type u) : ℕ → Type u
  | stop {n : ℕ} : ℝ → AtMostQueryTree X n
  | query {n : ℕ} : X → (ℝ → AtMostQueryTree X n) →
      AtMostQueryTree X (n + 1)

/-- Run a query tree on an integrand. -/
def run : {n : ℕ} → QueryTree X n → (X → ℝ) → ℝ
  | 0, .output y, _ => y
  | n + 1, .query x next, f => run (next (f x)) f

def runAtMost : {n : ℕ} → AtMostQueryTree X n → (X → ℝ) → ℝ
  | _, .stop y, _ => y
  | n + 1, .query x next, f => runAtMost (next (f x)) f

def asAtMost : {n : ℕ} → QueryTree X n → AtMostQueryTree X n
  | 0, .output y => .stop y
  | n + 1, .query x next => .query x (fun r => asAtMost (next r))

theorem runAtMost_asAtMost {n : ℕ} (A : QueryTree X n) (f : X → ℝ) :
    runAtMost (asAtMost A) f = run A f := by
  induction A with
  | output y => rfl
  | @query n x next ih => simp [asAtMost, runAtMost, run, ih]

/-- Ask for every value of a fixed finite codebook, then apply an arbitrary
deterministic rule to the response vector. -/
def queryAll : {n : ℕ} → (Fin n → X) → ((Fin n → ℝ) → ℝ) →
    QueryTree X n
  | 0, _, out => .output (out (fun i => Fin.elim0 i))
  | n + 1, c, out =>
      .query (c 0) (fun r =>
        queryAll (fun i => c i.succ) (fun v => out (Fin.cases r v)))

theorem run_queryAll {n : ℕ} (c : Fin n → X) (out : (Fin n → ℝ) → ℝ)
    (f : X → ℝ) :
    run (queryAll c out) f = out (fun i => f (c i)) := by
  induction n with
  | zero =>
      change out (fun i => Fin.elim0 i) = out (fun i => f (c i))
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [queryAll, run]
      rw [ih]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl

noncomputable def codebookQuadratureResponse
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) (c : Fin m → X)
    (v : Fin m → ℝ) : ℝ :=
  ∫ x, v (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex
    hm c x) ∂μ

noncomputable def codebookQuadratureTree
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) (c : Fin m → X) :
    QueryTree X m :=
  queryAll c (codebookQuadratureResponse hm μ c)

theorem run_codebookQuadratureTree
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) (c : Fin m → X)
    (f : X → ℝ) :
    run (codebookQuadratureTree hm μ c) f =
      ∫ x, f (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
        hm c x) ∂μ := by
  rw [codebookQuadratureTree, run_queryAll]
  rfl

theorem integrable_codebookProjection_comp
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) [IsFiniteMeasure μ]
    (c : Fin m → X) (f : X → ℝ) :
    Integrable (fun x => f (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
      hm c x)) μ := by
  let q := fun x => f (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
    hm c x)
  let qvals : Fin m → ℝ := fun i => f (c i)
  have hq : Measurable q :=
    (measurable_of_finite qvals).comp
      (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hm c)
  let M := ∑ i : Fin m, |f (c i)|
  have hbound : ∀ x, ‖q x‖ ≤ M := by
    intro x
    rw [Real.norm_eq_abs]
    calc
      |q x| = |f (c (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex
          hm c x))| := rfl
      _ ≤ ∑ i : Fin m, |f (c i)| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin m => |f (c i)|)
          (fun i hi => abs_nonneg _) (Finset.mem_univ _)
  exact (integrable_const M).mono' hq.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

theorem integrable_lipschitz_of_firstMoment
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (x₀ : X)
    (hM1 : Integrable (fun x => dist x x₀) μ)
    (f : X → ℝ) (hLip : LipschitzWith 1 f) :
    Integrable f μ := by
  have hmeas : Measurable f := hLip.continuous.measurable
  have hbound : ∀ x, ‖f x‖ ≤ ‖f x₀‖ + dist x x₀ := by
    intro x
    calc
      ‖f x‖ = ‖f x₀ + (f x - f x₀)‖ := by congr 1 <;> ring
      _ ≤ ‖f x₀‖ + ‖f x - f x₀‖ := norm_add_le _ _
      _ ≤ ‖f x₀‖ + dist x x₀ := by
        gcongr
        simpa [Real.dist_eq] using hLip.dist_le_mul x x₀
  have hmajor : Integrable (fun x : X => ‖f x₀‖ + dist x x₀) μ :=
    (integrable_const ‖f x₀‖).add hM1
  exact hmajor.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

theorem integrable_codebookDistortion_toReal_of_firstMoment
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) (c : Fin m → X)
    (hM1 : ∀ z : X, Integrable (fun x => dist x z) μ) :
    Integrable (fun x =>
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal) μ := by
  let p := BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
    hm c
  have hmeas : Measurable (fun x =>
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal) :=
    ENNReal.measurable_toReal.comp
      (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable
        hm c)
  have hpoint (x : X) :
      ‖(BrownianSharp.finiteCodebookDistortion hm c x).toReal‖ ≤
        dist x (c ⟨0, hm⟩) := by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal =
          (edist x (p x)).toReal := by
            rw [BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection_edist_eq]
      _ = dist x (p x) := (dist_edist x (p x)).symm
      _ ≤ dist x (c ⟨0, hm⟩) := by
        have hmin := BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex_minimal
          hm c x ⟨0, hm⟩
        calc
          dist x (p x) = (edist x (p x)).toReal := dist_edist x (p x)
          _ ≤ (edist x (c ⟨0, hm⟩)).toReal :=
            ENNReal.toReal_mono (edist_ne_top _ _) hmin
          _ = dist x (c ⟨0, hm⟩) := (dist_edist x _).symm
  exact (hM1 (c ⟨0, hm⟩)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hpoint)

theorem finiteCodebookDistortion_ne_top
    {X : Type u} [MetricSpace X] {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (x : X) :
    BrownianSharp.finiteCodebookDistortion hm c x ≠ ⊤ := by
  apply ne_top_of_le_ne_top (edist_ne_top x (c ⟨0, hm⟩))
  unfold BrownianSharp.finiteCodebookDistortion
  exact Finset.inf'_le _ (Finset.mem_univ (⟨0, hm⟩ : Fin m))

/-- Integrands in the deterministic integration class. -/
def OneLipschitzIntegrand (X : Type u) [MetricSpace X] :=
  {f : X → ℝ // LipschitzWith 1 f}

/-- Worst-case integration error over all real 1-Lipschitz integrands. -/
noncomputable def worstCaseIntegrationError
    {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {m : ℕ} (A : AtMostQueryTree X m) : ℝ≥0∞ :=
  ⨆ f : OneLipschitzIntegrand X,
    ENNReal.ofReal |(∫ x, f.1 x ∂μ) - runAtMost A f.1|

/-- Deterministic minimax integration error for algorithms using at most m
exact point evaluations. -/
noncomputable def deterministicIntegrationMinimax
    {X : Type u} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (m : ℕ) : ℝ≥0∞ :=
  ⨅ A : AtMostQueryTree X m, worstCaseIntegrationError μ A

theorem ofReal_integral_codebookDistortion_eq
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) (c : Fin m → X)
    (hD : Integrable (fun x =>
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal) μ) :
    ENNReal.ofReal (∫ x,
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal ∂μ) =
      ∫⁻ x, BrownianSharp.finiteCodebookDistortion hm c x ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] fun x =>
      (BrownianSharp.finiteCodebookDistortion hm c x).toReal :=
    Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg
  calc
    ENNReal.ofReal (∫ x,
        (BrownianSharp.finiteCodebookDistortion hm c x).toReal ∂μ) =
        ∫⁻ x, ENNReal.ofReal
          ((BrownianSharp.finiteCodebookDistortion hm c x).toReal) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hD hnonneg
    _ = ∫⁻ x, BrownianSharp.finiteCodebookDistortion hm c x ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      exact ENNReal.ofReal_toReal (finiteCodebookDistortion_ne_top hm c x)

theorem worstCase_codebookQuadratureTree_le
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (μ : Measure X) [IsFiniteMeasure μ]
    (c : Fin m → X)
    (hM1 : ∀ z : X, Integrable (fun x => dist x z) μ) :
    worstCaseIntegrationError μ
      (asAtMost (codebookQuadratureTree hm μ c)) ≤
      ∫⁻ x, BrownianSharp.finiteCodebookDistortion hm c x ∂μ := by
  apply iSup_le
  intro f
  let z₀ := c ⟨0, hm⟩
  have hfint := integrable_lipschitz_of_firstMoment μ z₀ (hM1 z₀) f.1 f.2
  have hpint := integrable_codebookProjection_comp hm μ c f.1
  have hdint := integrable_codebookDistortion_toReal_of_firstMoment hm μ c hM1
  have herror :
      |(∫ x, f.1 x ∂μ) -
        (∫ x, f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
          hm c x) ∂μ)| ≤
        ∫ x, (BrownianSharp.finiteCodebookDistortion hm c x).toReal ∂μ := by
    rw [← integral_sub hfint hpint]
    calc
      |∫ x, f.1 x -
          f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
            hm c x) ∂μ| ≤
          ∫ x, |f.1 x -
            f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
              hm c x)| ∂μ := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (fun x => f.1 x -
                f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
                  hm c x)))
      _ ≤ ∫ x, (BrownianSharp.finiteCodebookDistortion hm c x).toReal ∂μ := by
        apply integral_mono (hfint.sub hpint).abs hdint
        intro x
        let p := BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
          hm c x
        have hLip := f.2.dist_le_mul x p
        have hdist : dist x p =
            (BrownianSharp.finiteCodebookDistortion hm c x).toReal := by
          calc
            dist x p = (edist x p).toReal := dist_edist x p
            _ = (BrownianSharp.finiteCodebookDistortion hm c x).toReal := by
              rw [BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection_edist_eq]
        simpa [p, Real.dist_eq, hdist] using hLip
  have hcost := ofReal_integral_codebookDistortion_eq hm μ c hdint
  have hrun : runAtMost (asAtMost (codebookQuadratureTree hm μ c)) f.1 =
      ∫ x, f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
        hm c x) ∂μ := by
    rw [runAtMost_asAtMost, run_codebookQuadratureTree]
  rw [hrun]
  calc
    ENNReal.ofReal |(∫ x, f.1 x ∂μ) -
        (∫ x, f.1 (BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
          hm c x) ∂μ)| ≤
        ENNReal.ofReal (∫ x,
          (BrownianSharp.finiteCodebookDistortion hm c x).toReal ∂μ) :=
      ENNReal.ofReal_le_ofReal herror
    _ = ∫⁻ x, BrownianSharp.finiteCodebookDistortion hm c x ∂μ := hcost

/-- Pad a stopping algorithm to exactly `n` calls by repeating a fixed point
and ignoring the dummy responses. -/
def padAtMost : {n : ℕ} → AtMostQueryTree X n → X → QueryTree X n
  | 0, .stop y, _ => .output y
  | n + 1, .stop y, x₀ =>
      .query x₀ (fun _ => padAtMost (.stop y) x₀)
  | n + 1, .query x next, x₀ =>
      .query x (fun r => padAtMost (next r) x₀)

theorem run_padAtMost {n : ℕ} (A : AtMostQueryTree X n) (x₀ : X)
    (f : X → ℝ) : run (padAtMost A x₀) f = runAtMost A f := by
  induction n with
  | zero => cases A; rfl
  | succ n ih =>
      cases A with
      | stop y =>
          simp [padAtMost, run, runAtMost, ih]
      | @query n x next =>
          simp [padAtMost, run, runAtMost, ih]

/-- The same zero-response query path indexed by the exact evaluation
budget. -/
def zeroQueries : {n : ℕ} → QueryTree X n → Fin n → X
  | 0, .output _, i => Fin.elim0 i
  | n + 1, .query x next, i => Fin.cases x (zeroQueries (next 0)) i

/-- The algorithm's output on its zero-response branch. -/
def zeroRun : {n : ℕ} → QueryTree X n → ℝ
  | 0, .output y => y
  | n + 1, .query _ next => zeroRun (next 0)

theorem run_eq_zeroRun_of_zeroQueries {n : ℕ} (A : QueryTree X n) (f : X → ℝ)
    (hvanish : ∀ i : Fin n, f (zeroQueries A i) = 0) :
    run A f = zeroRun A := by
  induction A with
  | output y => rfl
  | @query n x next ih =>
      have hx : f x = 0 := hvanish 0
      have htail : ∀ j : Fin n, f (zeroQueries (next 0) j) = 0 := by
        intro j
        exact hvanish j.succ
      simp [run, zeroRun, zeroQueries, hx, ih 0 htail]

noncomputable def zeroQueryDistance {n : ℕ} (A : QueryTree X n) (x : X) : ℝ :=
  Metric.infDist x (Set.range (zeroQueries A))

theorem zeroQueryDistance_eq_codebookDistortion_toReal
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {n : ℕ} (hn : 0 < n) (A : QueryTree X n) (x : X) :
    zeroQueryDistance A x =
      (BrownianSharp.finiteCodebookDistortion hn (zeroQueries A) x).toReal := by
  let c := zeroQueries A
  let p := BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection
    hn c x
  have hp : p ∈ Set.range c := ⟨
    BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex hn c x, rfl⟩
  have hle : Metric.infDist x (Set.range c) ≤ dist x p :=
    Metric.infDist_le_dist_of_mem hp
  have hge : dist x p ≤ Metric.infDist x (Set.range c) := by
    letI : Nonempty (Set.range c) :=
      ⟨⟨c ⟨0, hn⟩, ⟨⟨0, hn⟩, rfl⟩⟩⟩
    rw [Metric.infDist_eq_iInf]
    change dist x p ≤ ⨅ y : Set.range c, dist x y
    apply le_ciInf
    intro y
    rcases y with ⟨y, ⟨i, rfl⟩⟩
    have hmin := BrownianSharp.AlignmentPaperQuantizationAtomicBridge.nearestIndex_minimal
      hn c x i
    calc
      dist x p = (edist x p).toReal := dist_edist x p
      _ ≤ (edist x (c i)).toReal :=
        ENNReal.toReal_mono (edist_ne_top _ _) hmin
      _ = dist x (c i) := (dist_edist x (c i)).symm
  calc
    zeroQueryDistance A x = Metric.infDist x (Set.range c) := rfl
    _ = dist x p := le_antisymm hle hge
    _ = (edist x p).toReal := dist_edist x p
    _ = (BrownianSharp.finiteCodebookDistortion hn c x).toReal := by
      congr 1
      exact BrownianSharp.AlignmentPaperQuantizationAtomicBridge.codebookProjection_edist_eq
        hn c x

theorem zeroQueryDistance_lintegral_eq_codebookDistortion
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {n : ℕ} (hn : 0 < n) (A : QueryTree X n) (μ : Measure X)
    (hd : Integrable (zeroQueryDistance A) μ) :
    ENNReal.ofReal (∫ x, zeroQueryDistance A x ∂μ) =
      ∫⁻ x, BrownianSharp.finiteCodebookDistortion hn
        (zeroQueries A) x ∂μ := by
  have hpoint (x : X) :
      ENNReal.ofReal (zeroQueryDistance A x) =
        BrownianSharp.finiteCodebookDistortion hn (zeroQueries A) x := by
    rw [zeroQueryDistance_eq_codebookDistortion_toReal hn A x]
    exact ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top (edist_ne_top x (zeroQueries A ⟨0, hn⟩))
        (by
          unfold BrownianSharp.finiteCodebookDistortion
          exact Finset.inf'_le _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))))
  calc
    ENNReal.ofReal (∫ x, zeroQueryDistance A x ∂μ) =
        ∫⁻ x, ENNReal.ofReal (zeroQueryDistance A x) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hd
        (ae_of_all μ fun x => Metric.infDist_nonneg)
    _ = ∫⁻ x, BrownianSharp.finiteCodebookDistortion hn
        (zeroQueries A) x ∂μ :=
      lintegral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- The positive and negative distance-to-zero-transcript integrands are
indistinguishable to the adaptive algorithm: every queried value is zero. -/
theorem adaptive_zero_branch_distance_witness {n : ℕ} (hn : 0 < n)
    (A : QueryTree X n) :
    ∃ f g : X → ℝ,
      f = zeroQueryDistance A ∧ g = -zeroQueryDistance A ∧
      LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      (∀ i : Fin n, f (zeroQueries A i) = 0 ∧
        g (zeroQueries A i) = 0) ∧
      run A f = run A g := by
  let f : X → ℝ := zeroQueryDistance A
  let g : X → ℝ := -zeroQueryDistance A
  have hf : LipschitzWith 1 f := by
    change LipschitzWith 1 (fun x => Metric.infDist x (Set.range (zeroQueries A)))
    exact Metric.lipschitz_infDist_pt _
  have hg : LipschitzWith 1 g := by
    simpa [g] using hf.neg
  have hv : ∀ i : Fin n, f (zeroQueries A i) = 0 ∧
      g (zeroQueries A i) = 0 := by
    intro i
    have hz : zeroQueryDistance A (zeroQueries A i) = 0 := by
      apply Metric.infDist_zero_of_mem
      exact ⟨i, rfl⟩
    simp [f, g, hz]
  refine ⟨f,g,rfl,rfl,hf,hg,hv,?_⟩
  rw [run_eq_zeroRun_of_zeroQueries A f (fun i => (hv i).1)]
  rw [run_eq_zeroRun_of_zeroQueries A g (fun i => (hv i).2)]

/-- For every adaptive algorithm, the two zero-branch witnesses have opposite
integrals. Their common algorithm output therefore incurs error at least the
integral of the distance to the zero-branch query set on one of them. -/
theorem adaptive_integration_error_lower_witness
    {X : Type u} [MetricSpace X] [MeasurableSpace X] {n : ℕ} (hn : 0 < n)
    (μ : Measure X) (A : QueryTree X n)
    (hd : Integrable (zeroQueryDistance A) μ) :
    ∃ f g : X → ℝ,
      LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      Integrable f μ ∧ Integrable g μ ∧
      (|(∫ x, f x ∂μ) - run A f| ≥
        (∫ x, zeroQueryDistance A x ∂μ) ∨
      |(∫ x, g x ∂μ) - run A g| ≥
        (∫ x, zeroQueryDistance A x ∂μ)) := by
  obtain ⟨f,g,hfeq,hgeq,hf,hg,hzero,hout⟩ :=
    adaptive_zero_branch_distance_witness hn A
  have hfint : Integrable f μ := by
    simpa [hfeq] using hd
  have hgint : Integrable g μ := by
    simpa [hgeq] using hd.neg
  let I := ∫ x, zeroQueryDistance A x ∂μ
  have hI : 0 ≤ I := by
    apply integral_nonneg
    intro x
    exact Metric.infDist_nonneg
  have hplus : (∫ x, f x ∂μ) = I := by
    rw [hfeq]
  have hminus : (∫ x, g x ∂μ) = -I := by
    rw [hgeq]
    simp only [Pi.neg_apply, integral_neg]
    rfl
  have hmax : I ≤ max
      |(∫ x, f x ∂μ) - run A f|
      |(∫ x, g x ∂μ) - run A g| := by
    rw [hplus, hminus, hout.symm]
    by_cases hy : 0 ≤ run A f
    · have hsecond : I ≤ |-I - run A f| := by
        rw [abs_of_nonpos]
        · nlinarith
        · nlinarith
      exact hsecond.trans (le_max_right _ _)
    · have hfirst : I ≤ |I - run A f| := by
        rw [abs_of_nonneg]
        · linarith
        · linarith
      exact hfirst.trans (le_max_left _ _)
  refine ⟨f, ⟨g, ?_⟩⟩
  refine And.intro hf ?_
  refine And.intro hg ?_
  refine And.intro hfint ?_
  refine And.intro hgint ?_
  by_cases hfirst : I ≤ |(∫ x, f x ∂μ) - run A f|
  · exact Or.inl hfirst
  · right
    by_contra hsecond
    have hlt₁ : |(∫ x, f x ∂μ) - run A f| < I := lt_of_not_ge hfirst
    have hlt₂ : |(∫ x, g x ∂μ) - run A g| < I := lt_of_not_ge hsecond
    have hmax' : max
        |(∫ x, f x ∂μ) - run A f|
        |(∫ x, g x ∂μ) - run A g| < I := max_lt hlt₁ hlt₂
    exact (not_lt_of_ge hmax) hmax'

/-- The worst error of any adaptive exact-evaluation tree is at least the
first-order quantization error of its integration law. -/
theorem quantizationQ1_le_adaptive_twoWitness_max
    {X : Type u} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    {n : ℕ} (hn : 0 < n) (μ : Measure X) (A : QueryTree X n)
    (hd : Integrable (zeroQueryDistance A) μ) :
    ∃ f g : X → ℝ, LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      Integrable f μ ∧ Integrable g μ ∧
      BrownianSharp.quantizationQ1 μ n hn ≤ ENNReal.ofReal
        (max |(∫ x, f x ∂μ) - run A f|
          |(∫ x, g x ∂μ) - run A g|) := by
  obtain ⟨f,g,hf,hg,hfi,hgi,hlarge⟩ :=
    adaptive_integration_error_lower_witness hn μ A hd
  let I := ∫ x, zeroQueryDistance A x ∂μ
  have hI : I ≤ max |(∫ x, f x ∂μ) - run A f|
      |(∫ x, g x ∂μ) - run A g| := by
    rcases hlarge with h | h
    · exact h.trans (le_max_left _ _)
    · exact h.trans (le_max_right _ _)
  have hcost := zeroQueryDistance_lintegral_eq_codebookDistortion hn A μ hd
  have hquant : BrownianSharp.quantizationQ1 μ n hn ≤ ENNReal.ofReal I := by
    calc
      BrownianSharp.quantizationQ1 μ n hn ≤
          ∫⁻ x, BrownianSharp.finiteCodebookDistortion hn
            (zeroQueries A) x ∂μ := by
              unfold BrownianSharp.quantizationQ1
              exact iInf_le _ (zeroQueries A)
      _ = ENNReal.ofReal I := hcost.symm
  refine ⟨f,g,hf,hg,hfi,hgi,?_⟩
  exact hquant.trans (ENNReal.ofReal_le_ofReal hI)

theorem quantizationQ1_le_deterministicIntegrationMinimax
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) (m : ℕ) (hm : 0 < m) (x₀ : X)
    (hM1 : ∀ z : X, Integrable (fun x => dist x z) μ) :
    BrownianSharp.quantizationQ1 μ m hm ≤
      deterministicIntegrationMinimax μ m := by
  unfold deterministicIntegrationMinimax
  apply le_iInf
  intro A
  let T := padAtMost A x₀
  have hD : Integrable (zeroQueryDistance T) μ := by
    have heq : zeroQueryDistance T =
        fun x => (BrownianSharp.finiteCodebookDistortion hm (zeroQueries T) x).toReal := by
      funext x
      exact zeroQueryDistance_eq_codebookDistortion_toReal hm T x
    rw [heq]
    exact integrable_codebookDistortion_toReal_of_firstMoment hm μ
      (zeroQueries T) hM1
  obtain ⟨f,g,hf,hg,hfi,hgi,hlarge⟩ :=
    quantizationQ1_le_adaptive_twoWitness_max hm μ T hD
  have hq : BrownianSharp.quantizationQ1 μ m hm ≤ ENNReal.ofReal
      (max |(∫ x, f x ∂μ) - runAtMost A f|
        |(∫ x, g x ∂μ) - runAtMost A g|) := by
    change BrownianSharp.quantizationQ1 μ m hm ≤ ENNReal.ofReal
      (max |(∫ x, f x ∂μ) - run (padAtMost A x₀) f|
        |(∫ x, g x ∂μ) - run (padAtMost A x₀) g|) at hlarge
    simpa only [run_padAtMost] using hlarge
  have hfirst : ENNReal.ofReal |(∫ x, f x ∂μ) - runAtMost A f| ≤
      worstCaseIntegrationError μ A :=
    le_iSup_of_le ⟨f,hf⟩ le_rfl
  have hsecond : ENNReal.ofReal |(∫ x, g x ∂μ) - runAtMost A g| ≤
      worstCaseIntegrationError μ A :=
    le_iSup_of_le ⟨g,hg⟩ le_rfl
  calc
    BrownianSharp.quantizationQ1 μ m hm ≤ ENNReal.ofReal
        (max |(∫ x, f x ∂μ) - runAtMost A f|
          |(∫ x, g x ∂μ) - runAtMost A g|) := hq
    _ = max (ENNReal.ofReal |(∫ x, f x ∂μ) - runAtMost A f|)
        (ENNReal.ofReal |(∫ x, g x ∂μ) - runAtMost A g|) := by
          rw [ENNReal.ofReal_max]
    _ ≤ worstCaseIntegrationError μ A := max_le hfirst hsecond

theorem deterministicIntegrationMinimax_le_quantizationQ1
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ) (hm : 0 < m)
    (hM1 : ∀ z : X, Integrable (fun x => dist x z) μ) :
    deterministicIntegrationMinimax μ m ≤
      BrownianSharp.quantizationQ1 μ m hm := by
  unfold deterministicIntegrationMinimax BrownianSharp.quantizationQ1
  apply le_iInf
  intro c
  let A := asAtMost (codebookQuadratureTree hm μ c)
  calc
    (⨅ A : AtMostQueryTree X m, worstCaseIntegrationError μ A) ≤
        worstCaseIntegrationError μ A := iInf_le _ A
    _ ≤ ∫⁻ x, BrownianSharp.finiteCodebookDistortion hm c x ∂μ :=
      worstCase_codebookQuadratureTree_le hm μ c hM1

/-- The deterministic minimax error for adaptive exact evaluations equals the
first-order optimal quantization error. The upper rule is nonadaptive Voronoi
quadrature; the lower bound allows arbitrary response-dependent query trees. -/
theorem deterministicIntegration_eq_quantizationQ1
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ) (hm : 0 < m) (x₀ : X)
    (hM1 : ∀ z : X, Integrable (fun x => dist x z) μ) :
    deterministicIntegrationMinimax μ m =
      BrownianSharp.quantizationQ1 μ m hm := by
  apply le_antisymm
  · exact deterministicIntegrationMinimax_le_quantizationQ1 μ m hm hM1
  · exact quantizationQ1_le_deterministicIntegrationMinimax μ m hm x₀ hM1

/-- Actual centered continuous Gaussian path laws satisfy the finite-first-
moment premise automatically by the proved fourth-moment/Fernique result. -/
theorem centeredGaussianPath_deterministicIntegration_eq_quantizationQ1
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α,ℝ)) (hF : Measurable F)
    (hX : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (m : ℕ) (hm : 0 < m) :
    deterministicIntegrationMinimax (P.map F) m =
      BrownianSharp.quantizationQ1 (P.map F) m hm := by
  have hF4 :=
    BrownianSharp.AlignmentPaperContinuousGaussianFernique.centeredGaussian_path_memLp_fourth
      F hF hX hmean
  have hFint : Integrable F P :=
    hF4.integrable (by norm_num : (1 : ENNReal) ≤ 4)
  have hM1 : ∀ z : C(α,ℝ),
      Integrable (fun f => dist f z) (P.map F) := by
    intro z
    have hsource : Integrable (fun ω => dist (F ω) z) P := by
      have hsub := hFint.sub (integrable_const z)
      simpa [dist_eq_norm] using hsub.norm
    have hmeas : AEStronglyMeasurable (fun f : C(α,ℝ) => dist f z) (P.map F) :=
      (continuous_id.dist continuous_const).measurable.aestronglyMeasurable
    exact (integrable_map_measure hmeas hF.aemeasurable).mpr hsource
  exact deterministicIntegration_eq_quantizationQ1
    (P.map F) m hm 0 hM1

end BrownianSharp.AlignmentPaperDeterministicIntegration
