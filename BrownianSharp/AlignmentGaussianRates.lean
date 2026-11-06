import BrownianSharp.BrownianSheetOnCube
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Gaussian sheet rate alignment

This file checks the exponent arithmetic in the three Gaussian clauses of
`thm:main`.  The analytic entropy-to-small-ball correspondence remains an
explicit premise: this module does not import or assume a theorem by citation.
-/

namespace BrownianSharp.AlignmentGaussianRates

open MeasureTheory ProbabilityTheory HaarQuarter

noncomputable section

/-- Integrate a continuous cube path once from zero in coordinate `i`.
The fixed interval substitution `u = x_i * v` keeps the integral over
`[0,1]`; this representation also handles the face `x_i = 0` directly. -/
def integrateCoordinatePath {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) : C(BrownianCubeAnchor d, ℝ) := by
  let g : BrownianCubeAnchor d → ℝ → ℝ := fun x v =>
    x.val i * brownianCubeGlobalExtension f
      (Function.update x.val i (x.val i * v))
  have hupdate : Continuous (fun p : BrownianCubeAnchor d × ℝ =>
      Function.update p.1.val i (p.1.val i * p.2)) := by
    apply continuous_pi
    intro j
    have hval : Continuous (fun p : BrownianCubeAnchor d × ℝ => p.1.val j) := by
      exact (continuous_apply j).comp
        (continuous_subtype_val.comp continuous_fst)
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact hval.mul continuous_snd
    · simpa [Function.update_of_ne hji]
        using hval
  have hg : Continuous g.uncurry := by
    have hcoord : Continuous (fun p : BrownianCubeAnchor d × ℝ => p.1.val i) := by
      exact (continuous_apply i).comp
        (continuous_subtype_val.comp continuous_fst)
    have harg : Continuous (fun p : BrownianCubeAnchor d × ℝ =>
        brownianCubeGlobalExtension f
          (Function.update p.1.val i (p.1.val i * p.2))) :=
      (brownianCubeGlobalExtension f).continuous.comp hupdate
    exact hcoord.mul harg
  have hcont : Continuous (fun x => ∫ v in Set.Icc (0 : ℝ) 1, g x v ∂volume) :=
    continuous_parametric_integral_of_continuous hg
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  exact ⟨fun x => ∫ v in Set.Icc (0 : ℝ) 1, g x v ∂volume, hcont⟩

@[simp] theorem integrateCoordinatePath_apply {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) (x : BrownianCubeAnchor d) :
    integrateCoordinatePath i f x =
      ∫ v in Set.Icc (0 : ℝ) 1,
        x.val i * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v)) ∂volume := rfl

/-- The fixed-interval definition is exactly integration from zero to the
requested coordinate, by the affine substitution u = x_i v. -/
theorem integrateCoordinatePath_eq_intervalIntegral {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) (x : BrownianCubeAnchor d) :
    integrateCoordinatePath i f x =
      ∫ u in (0 : ℝ)..x.val i,
        brownianCubeGlobalExtension f (Function.update x.val i u) := by
  let H : ℝ → ℝ := fun u =>
    brownianCubeGlobalExtension f (Function.update x.val i u)
  rw [integrateCoordinatePath_apply]
  rw [integral_const_mul]
  change x.val i * (∫ v in Set.Icc (0 : ℝ) 1, H (x.val i * v) ∂volume) = _
  calc
    x.val i * (∫ v in Set.Icc (0 : ℝ) 1, H (x.val i * v) ∂volume) =
        x.val i • (∫ v in (0 : ℝ)..1, H (x.val i * v)) := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rfl
    _ = ∫ u in x.val i * 0..x.val i * 1, H u := by
          simpa [smul_eq_mul] using
            (intervalIntegral.smul_integral_comp_mul_left
              (f := H) (a := (0 : ℝ)) (b := 1) (c := x.val i))
    _ = ∫ u in (0 : ℝ)..x.val i, H u := by simp

/-- One coordinate integration is a contraction in the uniform norm. -/
theorem integrateCoordinatePath_norm_le {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) :
    ‖integrateCoordinatePath i f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le_of_nonempty
    (f := integrateCoordinatePath i f)).2
  intro x
  let integrand : ℝ → ℝ := fun v =>
    x.val i * brownianCubeGlobalExtension f
      (Function.update x.val i (x.val i * v))
  have hint : IntegrableOn integrand (Set.Icc (0 : ℝ) 1) volume := by
    have hc : ContinuousOn integrand (Set.Icc (0 : ℝ) 1) := by
      dsimp [integrand]
      exact (show Continuous (fun v : ℝ =>
        x.val i * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v)) ) from by fun_prop).continuousOn
    exact hc.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hconst : IntegrableOn (fun _ : ℝ => ‖f‖) (Set.Icc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  have hbound : ∀ v ∈ Set.Icc (0 : ℝ) 1, |integrand v| ≤ ‖f‖ := by
    intro v hv
    have hxi := x.property i
    have hext : ‖brownianCubeGlobalExtension f
        (Function.update x.val i (x.val i * v))‖ ≤ ‖f‖ := by
      rw [brownianCubeGlobalExtension_apply]
      exact f.norm_coe_le_norm _
    have hnorm : |integrand v| = |x.val i| *
        ‖brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v))‖ := by
      simp [integrand, Real.norm_eq_abs, abs_mul]
    rw [hnorm]
    have hxiabs : |x.val i| ≤ 1 := by rw [abs_of_nonneg hxi.1]; exact hxi.2
    nlinarith [norm_nonneg (brownianCubeGlobalExtension f
      (Function.update x.val i (x.val i * v)))]
  calc
    ‖integrateCoordinatePath i f x‖ ≤
        ∫ v in Set.Icc (0 : ℝ) 1, |integrand v| ∂volume := by
          rw [Real.norm_eq_abs, integrateCoordinatePath_apply]
          change |∫ v, integrand v ∂(volume.restrict (Set.Icc (0 : ℝ) 1))| ≤ _
          exact abs_integral_le_integral_abs
    _ ≤ ∫ v in Set.Icc (0 : ℝ) 1, ‖f‖ ∂volume :=
        setIntegral_mono_on (show IntegrableOn (fun v => |integrand v|)
          (Set.Icc (0 : ℝ) 1) volume from hint.norm)
          hconst measurableSet_Icc hbound
    _ = ‖f‖ := by simp

/-- Coordinate integration is linear in its input path. -/
theorem integrateCoordinatePath_add {d : ℕ} (i : Fin d)
    (f g : C(BrownianCubeAnchor d, ℝ)) :
    integrateCoordinatePath i (f + g) =
      integrateCoordinatePath i f + integrateCoordinatePath i g := by
  ext x
  simp only [ContinuousMap.add_apply, integrateCoordinatePath_apply]
  have hfi : IntegrableOn
      (fun v : ℝ => x.val i * brownianCubeGlobalExtension f
        (Function.update x.val i (x.val i * v))) (Set.Icc 0 1) volume := by
    apply (show Continuous (fun v : ℝ => x.val i * brownianCubeGlobalExtension f
      (Function.update x.val i (x.val i * v)) ) from by fun_prop).continuousOn
      |>.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hgi : IntegrableOn
      (fun v : ℝ => x.val i * brownianCubeGlobalExtension g
        (Function.update x.val i (x.val i * v))) (Set.Icc 0 1) volume := by
    apply (show Continuous (fun v : ℝ => x.val i * brownianCubeGlobalExtension g
      (Function.update x.val i (x.val i * v)) ) from by fun_prop).continuousOn
      |>.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hsum : ∀ v : ℝ,
      x.val i * brownianCubeGlobalExtension (f + g)
          (Function.update x.val i (x.val i * v)) =
        x.val i * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v)) +
        x.val i * brownianCubeGlobalExtension g
          (Function.update x.val i (x.val i * v)) := by
    intro v
    simp [brownianCubeGlobalExtension]
    ring
  rw [show (fun v : ℝ => x.val i * brownianCubeGlobalExtension (f + g)
      (Function.update x.val i (x.val i * v)) ) =
      (fun v => x.val i * brownianCubeGlobalExtension f
        (Function.update x.val i (x.val i * v)) +
        x.val i * brownianCubeGlobalExtension g
          (Function.update x.val i (x.val i * v))) from funext hsum]
  rw [integral_add hfi hgi]

theorem integrateCoordinatePath_smul {d : ℕ} (i : Fin d) (c : ℝ)
    (f : C(BrownianCubeAnchor d, ℝ)) :
    integrateCoordinatePath i (c • f) = c • integrateCoordinatePath i f := by
  ext x
  simp only [ContinuousMap.smul_apply, smul_eq_mul,
    integrateCoordinatePath_apply]
  have hext (z : Fin d → ℝ) :
      brownianCubeGlobalExtension (c • f) z = c * brownianCubeGlobalExtension f z := by
    simp [brownianCubeGlobalExtension]
  simp_rw [hext]
  calc
    (∫ v in Set.Icc (0 : ℝ) 1,
        x.val i * (c * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v))) ∂volume) =
      ∫ v in Set.Icc (0 : ℝ) 1,
        c * (x.val i * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v))) ∂volume := by
            congr 1
            funext v
            ring
    _ = c * (∫ v in Set.Icc (0 : ℝ) 1,
        x.val i * brownianCubeGlobalExtension f
          (Function.update x.val i (x.val i * v)) ∂volume) := by
            calc
              _ = ∫ v in Set.Icc (0 : ℝ) 1,
                    c • (x.val i * brownianCubeGlobalExtension f
                      (Function.update x.val i (x.val i * v))) ∂volume := by
                    congr 1
              _ = c • (∫ v in Set.Icc (0 : ℝ) 1,
                    x.val i * brownianCubeGlobalExtension f
                      (Function.update x.val i (x.val i * v)) ∂volume) := by
                    rw [integral_smul]
              _ = _ := rfl

/-- The one-coordinate integration operator is 1-Lipschitz, hence continuous
as a map on the continuous-path Banach space. -/
theorem integrateCoordinatePath_continuous {d : ℕ} (i : Fin d) :
    Continuous (fun f : C(BrownianCubeAnchor d, ℝ) => integrateCoordinatePath i f) := by
  have hlip : LipschitzWith 1
      (fun f : C(BrownianCubeAnchor d, ℝ) => integrateCoordinatePath i f) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro f g
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : integrateCoordinatePath i f - integrateCoordinatePath i g =
        integrateCoordinatePath i (f - g) := by
      symm
      calc
        integrateCoordinatePath i (f - g) =
            integrateCoordinatePath i (f + (-1 : ℝ) • g) := by
              congr 1
              ext x
              simpa [smul_eq_mul] using sub_eq_add_neg (f x) (g x)
        _ = integrateCoordinatePath i f + integrateCoordinatePath i ((-1 : ℝ) • g) :=
          integrateCoordinatePath_add i f _
        _ = integrateCoordinatePath i f + (-1 : ℝ) • integrateCoordinatePath i g := by
          rw [integrateCoordinatePath_smul]
        _ = integrateCoordinatePath i f - integrateCoordinatePath i g := by
          simpa using (sub_eq_add_neg
            (integrateCoordinatePath i f) (integrateCoordinatePath i g)).symm
    rw [hsub]
    simpa using integrateCoordinatePath_norm_le i (f - g)
  exact hlip.continuous

/-- Repeat the one-coordinate Riemann--Liouville integration operator. -/
def iterateCoordinatePath {d : ℕ} (i : Fin d) :
    ℕ → C(BrownianCubeAnchor d, ℝ) → C(BrownianCubeAnchor d, ℝ)
  | 0, f => f
  | n + 1, f => integrateCoordinatePath i (iterateCoordinatePath i n f)

/-- Apply the requested number of integrations in each coordinate, in the
canonical order of `Fin d`. -/
def integrateSheetPath {d : ℕ} (m : Fin d → ℕ)
    (f : C(BrownianCubeAnchor d, ℝ)) : C(BrownianCubeAnchor d, ℝ) :=
  (Finset.univ.toList : List (Fin d)).foldl
    (fun g i => iterateCoordinatePath i (m i) g) f

theorem iterateCoordinatePath_continuous {d : ℕ} (i : Fin d) :
    ∀ n, Continuous (iterateCoordinatePath i n) := by
  intro n
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
      exact (integrateCoordinatePath_continuous i).comp ih

private theorem foldl_integrateCoordinatePath_continuous {d : ℕ}
    (m : Fin d → ℕ) (l : List (Fin d)) :
    Continuous (fun f : C(BrownianCubeAnchor d, ℝ) =>
      l.foldl (fun g i => iterateCoordinatePath i (m i) g) f) := by
  induction l with
  | nil => exact continuous_id
  | cons i l ih =>
      change Continuous (fun f =>
        l.foldl (fun g j => iterateCoordinatePath j (m j) g)
          (iterateCoordinatePath i (m i) f))
      exact ih.comp (iterateCoordinatePath_continuous i (m i))

theorem integrateSheetPath_continuous {d : ℕ} (m : Fin d → ℕ) :
    Continuous (fun f : C(BrownianCubeAnchor d, ℝ) => integrateSheetPath m f) := by
  exact foldl_integrateCoordinatePath_continuous m (Finset.univ.toList)

@[simp] theorem integrateSheetPath_zero {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) :
    integrateSheetPath (fun _ : Fin d => 0) f = f := by
  change (Finset.univ.toList : List (Fin d)).foldl (fun g _ => g) f = f
  simp

end

/-- One-dimensional fractional Brownian covariance on nonnegative times. -/
noncomputable def fractionalCoordinateCovariance (H s t : ℝ) : ℝ :=
  (s ^ (2 * H) + t ^ (2 * H) - |s - t| ^ (2 * H)) / 2

/-- The covariance kernel of a fractional Brownian sheet with coordinate
Hurst parameters `H`. -/
noncomputable def fractionalSheetCovariance {d : ℕ}
    (H : Fin d → ℝ) (s t : BrownianCubeAnchor d) : ℝ :=
  ∏ i, fractionalCoordinateCovariance (H i) (s.val i) (t.val i)

/-- Continuous-path fractional Brownian sheet interface on the anchored cube.
This is a realization interface; existence and the small-ball theorem remain
separate analytic statements. -/
structure FractionalBrownianSheetOnCube (d : ℕ) (Ω : Type*)
    [MeasurableSpace Ω] (P : Measure Ω) where
  H : Fin d → ℝ
  hH : ∀ i, 0 < H i ∧ H i < 1
  path : Ω → C(BrownianCubeAnchor d, ℝ)
  measurable_path : Measurable path
  gaussian : IsGaussianProcess
    (fun x : BrownianCubeAnchor d => fun ω => path ω x) P
  mean_zero : ∀ x, ∫ ω, path ω x ∂P = 0
  covariance : ∀ x y,
    cov[fun ω => path ω x, fun ω => path ω y; P] =
      fractionalSheetCovariance H x y

/-- At Hurst parameter one half, the fractional covariance is `min(s,t)` on
nonnegative times. -/
theorem fractionalCoordinateCovariance_half (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    fractionalCoordinateCovariance (1 / 2) s t = min s t := by
  unfold fractionalCoordinateCovariance
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num]
  simp only [Real.rpow_one]
  by_cases h : s ≤ t
  · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
    ring
  · have h' : t ≤ s := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr h'), min_eq_right h']
    ring

/-- View a standard Brownian sheet as a fractional sheet with constant
Hurst vector `1/2`, preserving its probability space and path map. -/
noncomputable def FractionalBrownianSheetOnCube.ofBrownian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) : FractionalBrownianSheetOnCube d Ω P := by
  refine ⟨fun _ => 1 / 2, ?_, B.path, B.measurable_path, B.gaussian,
    B.mean_zero, ?_⟩
  · intro i
    constructor <;> norm_num
  · intro x y
    rw [B.covariance]
    unfold fractionalSheetCovariance
    apply Finset.prod_congr rfl
    intro i hi
    exact (fractionalCoordinateCovariance_half (x.val i) (y.val i)
      (x.property i).1 (y.property i).1).symm

/-- A fractional sheet with every Hurst parameter equal to one half is a
Brownian sheet on the same probability space, with the identical path map. -/
noncomputable def FractionalBrownianSheetOnCube.toBrownian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P)
    (hhalf : ∀ i, B.H i = 1 / 2) : BrownianSheetOnCube d Ω P := by
  refine ⟨B.path, B.measurable_path, B.gaussian, B.mean_zero, ?_⟩
  intro x y
  rw [B.covariance]
  unfold fractionalSheetCovariance
  apply Finset.prod_congr rfl
  intro i hi
  rw [hhalf i]
  exact fractionalCoordinateCovariance_half (x.val i) (y.val i)
    (x.property i).1 (y.property i).1

@[simp] theorem FractionalBrownianSheetOnCube.toBrownian_path
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P)
    (hhalf : ∀ i, B.H i = 1 / 2) :
    (B.toBrownian hhalf).path = B.path := rfl

@[simp] theorem FractionalBrownianSheetOnCube.toBrownian_eval
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P)
    (hhalf : ∀ i, B.H i = 1 / 2)
    (x : BrownianCubeAnchor d) (ω : Ω) :
    (B.toBrownian hhalf).eval x ω = B.path ω x := rfl

@[simp] theorem FractionalBrownianSheetOnCube.ofBrownian_path
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) :
    (FractionalBrownianSheetOnCube.ofBrownian B).path = B.path := rfl

/-- Covariance of a one-dimensional Brownian motion integrated `m` times
from zero. Each recursion integrates once in each covariance argument. -/
noncomputable def integratedCoordinateCovariance : ℕ → ℝ → ℝ → ℝ
  | 0, s, t => min s t
  | m + 1, s, t =>
      ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..t,
        integratedCoordinateCovariance m u v

@[simp] theorem integratedCoordinateCovariance_zero (s t : ℝ) :
    integratedCoordinateCovariance 0 s t = min s t := rfl

/-- Continuous-path realization interface for the sheet integrated `m_i`
times in coordinate `i`. The covariance field records repeated integration
of the Brownian covariance. -/
structure IntegratedBrownianSheetOnCube (d : ℕ) (Ω : Type*)
    [MeasurableSpace Ω] (P : Measure Ω) where
  m : Fin d → ℕ
  base : BrownianSheetOnCube d Ω P

noncomputable def IntegratedBrownianSheetOnCube.ofBrownian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) : IntegratedBrownianSheetOnCube d Ω P :=
  ⟨fun _ => 0, B⟩

/-- The concrete sample path obtained by integrating each realized Brownian
sheet path the prescribed number of times in every coordinate. -/
noncomputable def integrateBrownianSheetPath {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    Ω → C(BrownianCubeAnchor d, ℝ) := fun ω => integrateSheetPath m (B.path ω)

noncomputable def IntegratedBrownianSheetOnCube.path
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : IntegratedBrownianSheetOnCube d Ω P) :
    Ω → C(BrownianCubeAnchor d, ℝ) :=
  integrateBrownianSheetPath X.base X.m

theorem IntegratedBrownianSheetOnCube.measurable_path
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : IntegratedBrownianSheetOnCube d Ω P) :
    Measurable X.path :=
  (integrateSheetPath_continuous X.m).measurable.comp X.base.measurable_path

@[simp] theorem IntegratedBrownianSheetOnCube.ofBrownian_path
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) :
    (IntegratedBrownianSheetOnCube.ofBrownian B).path = B.path := by
  funext ω
  exact integrateSheetPath_zero (B.path ω)

theorem measurable_integrateBrownianSheetPath
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    Measurable (integrateBrownianSheetPath B m) :=
  (integrateSheetPath_continuous m).measurable.comp B.measurable_path

@[simp] theorem integrateBrownianSheetPath_apply
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (ω : Ω) (x : BrownianCubeAnchor d) :
    integrateBrownianSheetPath B m ω x = integrateSheetPath m (B.path ω) x := rfl

end BrownianSharp.AlignmentGaussianRates
