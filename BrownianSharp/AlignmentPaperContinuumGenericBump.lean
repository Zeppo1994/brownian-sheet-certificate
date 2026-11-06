import BrownianSharp.AlignmentPaperContinuumGoodRegion
import BrownianSharp.AlignmentPaperContinuumHulls
import BrownianSharp.AlignmentPaperGenericContinuumVariance
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Geometry for an arbitrary continuous unit bump supported in the unit
interval. This module begins the parameterized core behind the concrete
smooth-atom continuum argument. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperContinuumGenericBump

open BrownianSharp.AlignmentPaperContinuumGoodRegion
open BrownianSharp.AlignmentPaperContinuumHulls

/-- Continuous unit-height atom with support in the open unit interval. -/
structure AdmissibleBump where
  atom : ℝ → ℝ
  continuous : Continuous atom
  support_subset : Function.support atom ⊆ Set.Ioo (0 : ℝ) 1
  abs_le_one : ∀ x, |atom x| ≤ 1
  nonzero : ∃ x, atom x ≠ 0

namespace AdmissibleBump

theorem eq_zero_of_outside (ψ : AdmissibleBump) {x : ℝ}
    (hx : x ≤ 0 ∨ 1 ≤ x) : ψ.atom x = 0 := by
  by_contra hne
  have hxSupport : x ∈ Function.support ψ.atom := by simpa using hne
  have h := ψ.support_subset hxSupport
  rcases hx with hx | hx <;> simp only [Set.mem_Ioo] at h <;> linarith

theorem square_hasCompactSupport (ψ : AdmissibleBump) :
    HasCompactSupport (fun x : ℝ => ψ.atom x ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  have hne : ψ.atom x ^ 2 ≠ 0 := by simpa using hx
  have hψ : ψ.atom x ≠ 0 := by
    intro hz
    apply hne
    simp [hz]
  have hs := ψ.support_subset (by simpa using hψ)
  exact ⟨le_of_lt hs.1, hs.2.le⟩

def squareIntegral (ψ : AdmissibleBump) : ℝ :=
  ∫ x : ℝ, ψ.atom x ^ 2

theorem square_integrable (ψ : AdmissibleBump) :
    Integrable (fun x : ℝ => ψ.atom x ^ 2) volume :=
  (ψ.continuous.pow 2).integrable_of_hasCompactSupport
    ψ.square_hasCompactSupport

theorem squareIntegral_pos (ψ : AdmissibleBump) : 0 < squareIntegral ψ := by
  rcases ψ.nonzero with ⟨x, hx⟩
  have hcont : Continuous (fun t : ℝ => ψ.atom t ^ 2) := ψ.continuous.pow 2
  have hcompact : HasCompactSupport (fun t : ℝ => ψ.atom t ^ 2) :=
    ψ.square_hasCompactSupport
  apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcompact
  · intro t
    exact sq_nonneg _
  · exact pow_ne_zero 2 hx

theorem squareIntegral_le_one (ψ : AdmissibleBump) : squareIntegral ψ ≤ 1 := by
  let g : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ))
  have hpoint : ∀ x : ℝ, ψ.atom x ^ 2 ≤ g x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · have habs := ψ.abs_le_one x
      simpa [g, hx] using (sq_le_one_iff_abs_le_one (ψ.atom x)).2 habs
    · have hz : ψ.atom x = 0 := by
        have hx' : x < 0 ∨ 1 < x := by
          by_cases h0 : 0 ≤ x
          · right
            exact lt_of_not_ge (fun h1 => hx ⟨h0, h1⟩)
          · exact Or.inl (lt_of_not_ge h0)
        apply ψ.eq_zero_of_outside
        rcases hx' with h | h
        · exact Or.inl h.le
        · exact Or.inr h.le
      simp [g, hx, hz]
  have hg : Integrable g volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (μ := volume) (s := Set.Icc (0 : ℝ) 1)
      (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc])
  have hle := integral_mono ψ.square_integrable hg hpoint
  have hgint : (∫ x : ℝ, g x) = 1 := by
    simp [g, integral_indicator, Real.volume_Icc]
  rw [← squareIntegral, hgint] at hle
  exact hle

/-- The existing paper atom is an admissible instance of this abstract
support and normalization interface. -/
def smoothAtomAdmissible : AdmissibleBump where
  atom := smoothAtom
  continuous := smoothAtom_contDiff.continuous
  support_subset := by
    intro x hx
    have hne : smoothAtom x ≠ 0 := by simpa using hx
    constructor
    · by_contra h
      exact hne (smoothAtom_support x (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hne (smoothAtom_support x (Or.inr (le_of_not_gt h)))
  abs_le_one := smoothAtom_abs_le_one
  nonzero := ⟨1 / 2, smoothAtom_nonzero⟩

end AdmissibleBump

/-- One rescaled tensor bump at a layer address. -/
def cubeBumpAtom {d n : ℕ} (ψ : AdmissibleBump) (x : Fin d → ℝ)
    (a : LayerIndex d n) : ℝ :=
  ∏ i : Fin d, ψ.atom ((2 : ℝ) ^ layerIndexDepth a i * x i -
    (layerIndexCell a i : ℝ))

def cubeBumpEnergy {d n : ℕ} (ψ : AdmissibleBump) (x : Fin d → ℝ) : ℝ :=
  ∑ a : LayerIndex d n, cubeBumpAtom ψ x a ^ 2

def cubeBumpEnergyMean {d n : ℕ} (ψ : AdmissibleBump) : ℝ :=
  ∫ x : Fin d → ℝ, cubeBumpEnergy (d := d) (n := n) ψ x ∂cubeLebesgue d

def cubeBumpGoodSet {d n : ℕ} (ψ : AdmissibleBump) : Set (Fin d → ℝ) :=
  {x | x ∈ cubeSet d ∧
    cubeBumpEnergy (d := d) (n := n) ψ x ≥ cubeBumpEnergyMean (d := d) (n := n) ψ / 2}

def cubeBumpGoodMeasure {d n : ℕ} (ψ : AdmissibleBump) : Measure (Fin d → ℝ) :=
  (cubeLebesgue d).restrict (cubeBumpGoodSet (d := d) (n := n) ψ)

def cubeBumpGoodRow {d n : ℕ} (ψ : AdmissibleBump) (x : Fin d → ℝ) :
    LayerIndex d n → ℝ :=
  fun a => cubeBumpAtom ψ x a /
    Real.sqrt (cubeBumpEnergy (d := d) (n := n) ψ x)

private theorem bump_sq_integral_translate (ψ : AdmissibleBump) (m : ℝ) :
    (∫ x : ℝ, ψ.atom (x - m) ^ 2) = ψ.squareIntegral := by
  let T : ℝ → ℝ := fun x => x - m
  have hT : Measure.map T volume = volume := by
    change Measure.map (fun x : ℝ => x + -m) volume = volume
    exact MeasureTheory.map_add_right_eq_self volume (-m)
  have hmap := MeasureTheory.integral_map
    (μ := volume) (φ := T) (f := fun y : ℝ => ψ.atom y ^ 2)
    (by fun_prop) (by
      rw [hT]
      exact (ψ.continuous.pow 2).aestronglyMeasurable)
  calc
    (∫ x : ℝ, ψ.atom (x - m) ^ 2) =
        ∫ y : ℝ, ψ.atom y ^ 2 ∂Measure.map T volume := hmap.symm
    _ = ψ.squareIntegral := by rw [hT, AdmissibleBump.squareIntegral]

theorem bump_sq_scaled_translate_integral (ψ : AdmissibleBump)
    (s m : ℕ) :
    (∫ x : ℝ, ψ.atom ((2 : ℝ) ^ s * x - m) ^ 2) =
      ((2 : ℝ) ^ s)⁻¹ * ψ.squareIntegral := by
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => ψ.atom (y - (m : ℝ)) ^ 2) ((2 : ℝ) ^ s)
  have htrans := bump_sq_integral_translate ψ (m : ℝ)
  have hscale' :
      (∫ x : ℝ, ψ.atom ((2 : ℝ) ^ s * x - m) ^ 2) =
        |((2 : ℝ) ^ s)⁻¹| * (∫ y : ℝ, ψ.atom (y - m) ^ 2) := by
    simpa [smul_eq_mul, sub_eq_add_neg, mul_comm] using hscale
  rw [hscale', htrans]
  rw [abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 ^ s))]

private theorem bump_sq_scaled_translate_support (ψ : AdmissibleBump)
    (s m : ℕ) (hm : m < 2 ^ s) (x : ℝ)
    (hx : x ≤ 0 ∨ 1 ≤ x) :
    ψ.atom ((2 : ℝ) ^ s * x - m) ^ 2 = 0 := by
  have hout : (2 : ℝ) ^ s * x - (m : ℝ) ≤ 0 ∨
      1 ≤ (2 : ℝ) ^ s * x - (m : ℝ) := by
    rcases hx with hx | hx
    · left
      have hp : 0 ≤ (2 : ℝ) ^ s := by positivity
      have hm0 : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    · right
      have hp : (2 : ℝ) ^ s = (2 ^ s : ℕ) := by norm_cast
      have hs : m + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hm
      have hs' : (m : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hs
      have hp' : 0 < (2 : ℝ) ^ s := by positivity
      nlinarith
  rw [ψ.eq_zero_of_outside hout]
  norm_num

theorem bump_sq_scaled_translate_integral_cube (ψ : AdmissibleBump)
    (s m : ℕ) (hm : m < 2 ^ s) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      ψ.atom ((2 : ℝ) ^ s * x - m) ^ 2) =
      ((2 : ℝ) ^ s)⁻¹ * ψ.squareIntegral := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact bump_sq_scaled_translate_integral ψ s m
  · intro x hx
    have hout : x ≤ 0 ∨ 1 ≤ x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact Or.inl hx.le
      · exact Or.inr hx.le
    exact bump_sq_scaled_translate_support ψ s m hm x hout

private theorem bump_sq_cell_sum_integral (ψ : AdmissibleBump) (s : ℕ) :
    (∑ j : Fin (2 ^ s),
      ∫ x in Set.Icc (0 : ℝ) 1,
        ψ.atom ((2 : ℝ) ^ s * x - (j.val : ℕ)) ^ 2) = ψ.squareIntegral := by
  have hterm (j : Fin (2 ^ s)) :
      (∫ x in Set.Icc (0 : ℝ) 1,
        ψ.atom ((2 : ℝ) ^ s * x - (j.val : ℕ)) ^ 2) =
        ((2 : ℝ) ^ s)⁻¹ * ψ.squareIntegral :=
    bump_sq_scaled_translate_integral_cube ψ s j.val j.isLt
  calc
    _ = ∑ j : Fin (2 ^ s), ((2 : ℝ) ^ s)⁻¹ * ψ.squareIntegral := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = (2 ^ s : ℝ) * ((2 : ℝ) ^ s)⁻¹ * ψ.squareIntegral := by simp
    _ = ψ.squareIntegral := by
      have hp : (2 : ℝ) ^ s ≠ 0 := by positivity
      field_simp

private theorem sum_pi_prod_generic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) = ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

theorem cubeBumpShape_integral_eq_mass_pow {d n : ℕ} (ψ : AdmissibleBump)
    (r : Shape d n) :
    (∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
      ∫ x : Fin d → ℝ, cubeBumpAtom ψ x ⟨r, j⟩ ^ 2 ∂cubeLebesgue d) =
      ψ.squareIntegral ^ d := by
  classical
  let ν : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)
  calc
    _ = ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
        ∏ i : Fin d,
          ∫ t : ℝ in Set.Icc (0 : ℝ) 1,
            ψ.atom ((2 : ℝ) ^ r.1 i * t - (j i).val) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [cubeLebesgue_eq_pi]
          change (∫ x : Fin d → ℝ,
            (∏ i : Fin d,
              ψ.atom ((2 : ℝ) ^ r.1 i * x i - (j i).val)) ^ 2
              ∂Measure.pi ν) = _
          have hprod (x : Fin d → ℝ) :
              (∏ i : Fin d,
                ψ.atom ((2 : ℝ) ^ r.1 i * x i - (j i).val)) ^ 2 =
              ∏ i : Fin d,
                ψ.atom ((2 : ℝ) ^ r.1 i * x i - (j i).val) ^ 2 := by
            rw [Finset.prod_pow]
          rw [show (fun x : Fin d → ℝ =>
              (∏ i : Fin d,
                ψ.atom ((2 : ℝ) ^ r.1 i * x i - (j i).val)) ^ 2) =
              (fun x => ∏ i : Fin d,
                ψ.atom ((2 : ℝ) ^ r.1 i * x i - (j i).val) ^ 2) from by
              funext x
              exact hprod x]
          exact integral_fintype_prod_eq_prod
            (fun i t => ψ.atom ((2 : ℝ) ^ r.1 i * t - (j i).val) ^ 2)
    _ = ∏ i : Fin d,
        ∑ a : Fin (2 ^ r.1 i),
          ∫ t : ℝ in Set.Icc (0 : ℝ) 1,
            ψ.atom ((2 : ℝ) ^ r.1 i * t - a.val) ^ 2 := by
          exact sum_pi_prod_generic
            (ι := Fin d) (α := fun i => Fin (2 ^ r.1 i))
            (fun i a => ∫ t : ℝ in Set.Icc (0 : ℝ) 1,
              ψ.atom ((2 : ℝ) ^ r.1 i * t - (a.val : ℕ)) ^ 2)
    _ = ∏ i : Fin d, ψ.squareIntegral := by
          apply Finset.prod_congr rfl
          intro i hi
          exact bump_sq_cell_sum_integral ψ (r.1 i)
    _ = _ := by simp

theorem cubeBumpAtom_continuous {d n : ℕ} (ψ : AdmissibleBump)
    (a : LayerIndex d n) : Continuous (fun x : Fin d → ℝ => cubeBumpAtom ψ x a) := by
  unfold cubeBumpAtom
  apply continuous_finsetProd
  intro i hi
  exact ψ.continuous.comp ((continuous_const.mul (continuous_apply i)).sub continuous_const)

theorem cubeBumpAtom_abs_le_one {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (a : LayerIndex d n) : |cubeBumpAtom ψ x a| ≤ 1 := by
  unfold cubeBumpAtom
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin d, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi; exact ψ.abs_le_one _
    _ = 1 := by simp

theorem cubeBumpAtom_sq_integrable {d n : ℕ} (ψ : AdmissibleBump)
    (a : LayerIndex d n) :
    Integrable (fun x : Fin d → ℝ => cubeBumpAtom ψ x a ^ 2) (cubeLebesgue d) := by
  letI : IsProbabilityMeasure (cubeLebesgue d) := cubeLebesgue_probability d
  exact Integrable.of_bound
    ((cubeBumpAtom_continuous ψ a).pow 2 |>.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (cubeBumpAtom ψ x a))]
      have habs := cubeBumpAtom_abs_le_one ψ x a
      have hsq := (sq_le_one_iff_abs_le_one _).2 habs
      exact hsq)

theorem cubeBumpEnergyMean_eq_sum_atom_integrals {d n : ℕ}
    (ψ : AdmissibleBump) :
    cubeBumpEnergyMean (d := d) (n := n) ψ = ∑ a : LayerIndex d n,
      ∫ x : Fin d → ℝ, cubeBumpAtom ψ x a ^ 2 ∂cubeLebesgue d := by
  unfold cubeBumpEnergyMean cubeBumpEnergy
  rw [integral_finsetSum Finset.univ
    (fun a ha => cubeBumpAtom_sq_integrable ψ a)]

theorem cubeBumpEnergyMean_eq_layerCount_mass_pow {d n : ℕ}
    (ψ : AdmissibleBump) (hd : 0 < d) :
    cubeBumpEnergyMean (d := d) (n := n) ψ =
      hyperbolicCount d n * ψ.squareIntegral ^ d := by
  rw [cubeBumpEnergyMean_eq_sum_atom_integrals (d := d) (n := n) ψ,
    Fintype.sum_sigma]
  calc
    (∑ r : Shape d n,
      ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
        ∫ x : Fin d → ℝ, cubeBumpAtom ψ x ⟨r, j⟩ ^ 2 ∂cubeLebesgue d) =
      ∑ _r : Shape d n, ψ.squareIntegral ^ d := by
        apply Finset.sum_congr rfl
        intro r hr
        exact cubeBumpShape_integral_eq_mass_pow ψ r
    _ = (Fintype.card (Shape d n) : ℝ) * ψ.squareIntegral ^ d := by simp
    _ = _ := by
      rw [show (Fintype.card (Shape d n) : ℝ) = hyperbolicCount d n by
        rw [hyperbolicCount]
        exact_mod_cast shape_card d n hd]

theorem cubeBumpAtom_factor_nonzero {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (a : LayerIndex d n) (h : cubeBumpAtom ψ x a ≠ 0)
    (i : Fin d) :
    ψ.atom ((2 : ℝ) ^ layerIndexDepth a i * x i -
      (layerIndexCell a i : ℝ)) ≠ 0 := by
  unfold cubeBumpAtom at h
  exact (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)

theorem cubeBumpAtom_nonzero_address {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (a : LayerIndex d n) (h : cubeBumpAtom ψ x a ≠ 0)
    (i : Fin d) :
    (layerIndexCell a i : ℝ) < (2 : ℝ) ^ layerIndexDepth a i * x i ∧
      (2 : ℝ) ^ layerIndexDepth a i * x i < (layerIndexCell a i : ℝ) + 1 := by
  have hz := cubeBumpAtom_factor_nonzero ψ x a h i
  have harg : 0 < (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i ∧
      (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i < 1 := by
    by_contra hn
    have hout : (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i ≤ 0 ∨
        1 ≤ (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i := by
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    exact hz (ψ.eq_zero_of_outside hout)
  constructor <;> linarith

theorem cubeBumpAtom_unique_address {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (a b : LayerIndex d n)
    (hab : layerIndexDepth a = layerIndexDepth b)
    (ha : cubeBumpAtom ψ x a ≠ 0) (hb : cubeBumpAtom ψ x b ≠ 0) : a = b := by
  have hcell : layerIndexCell a = layerIndexCell b := by
    funext i
    have hA := cubeBumpAtom_nonzero_address ψ x a ha i
    have hB := cubeBumpAtom_nonzero_address ψ x b hb i
    have hdepth := congrArg (fun r : Fin d → ℕ => r i) hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsucc : (layerIndexCell a i : ℝ) + 1 ≤
        (layerIndexCell b i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [← hdepth] at hB
      linarith
    · have hsucc : (layerIndexCell b i : ℝ) + 1 ≤
        (layerIndexCell a i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [hdepth] at hA
      linarith
  have hshape : a.1.1 = b.1.1 := by
    apply Finsupp.ext
    intro i
    exact congrArg (fun r : Fin d → ℕ => r i) hab
  cases a with
  | mk ra ja =>
    cases b with
    | mk rb jb =>
      have hrs : ra = rb := Subtype.ext hshape
      subst rb
      have hj : ja = jb := by
        funext i
        apply Fin.ext
        exact congrArg (fun f : Fin d → ℕ => f i) hcell
      subst jb
      rfl

private theorem sum_sq_le_one_of_disjoint_support {α : Type*} [Fintype α]
    (f : α → ℝ) (hf : ∀ a, |f a| ≤ 1)
    (hpair : ∀ a b, a ≠ b → f a * f b = 0) : (∑ a, f a ^ 2) ≤ 1 := by
  classical
  by_cases hz : ∀ a, f a = 0
  · simp [hz]
  · push_neg at hz
    obtain ⟨a₀, ha₀⟩ := hz
    have hvanish : ∀ b, b ≠ a₀ → f b = 0 := by
      intro b hba
      have hmul := hpair a₀ b hba.symm
      rcases mul_eq_zero.mp hmul with h | h
      · exact (ha₀ h).elim
      · exact h
    rw [Finset.sum_eq_single_of_mem a₀ (Finset.mem_univ a₀)]
    · have hnonneg : 0 ≤ |f a₀| := abs_nonneg _
      nlinarith [hf a₀, hnonneg, sq_abs (f a₀)]
    · intro b hb hba
      rw [hvanish b hba]
      norm_num

theorem cubeBumpShapeEnergy_le_one {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (r : Shape d n) :
    (∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
      cubeBumpAtom ψ x ⟨r, j⟩ ^ 2) ≤ 1 := by
  apply sum_sq_le_one_of_disjoint_support
  · intro j
    exact cubeBumpAtom_abs_le_one ψ x ⟨r, j⟩
  · intro j k hjk
    by_contra hne
    have hu : cubeBumpAtom ψ x ⟨r, j⟩ ≠ 0 := by
      intro hz
      exact hne (by simp [hz])
    have hv : cubeBumpAtom ψ x ⟨r, k⟩ ≠ 0 := by
      intro hz
      exact hne (by simp [hz])
    have heq := cubeBumpAtom_unique_address ψ x ⟨r, j⟩ ⟨r, k⟩ rfl hu hv
    exact hjk (by injection heq)

theorem cubeBumpEnergy_le_layerCount {d n : ℕ} (ψ : AdmissibleBump)
    (hd : 0 < d) (x : Fin d → ℝ) :
    cubeBumpEnergy (d := d) (n := n) ψ x ≤ hyperbolicCount d n := by
  classical
  unfold cubeBumpEnergy
  rw [Fintype.sum_sigma]
  calc
    (∑ r : Shape d n,
      ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
        cubeBumpAtom ψ x ⟨r, j⟩ ^ 2) ≤
      ∑ _r : Shape d n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact cubeBumpShapeEnergy_le_one ψ x r
    _ = (Fintype.card (Shape d n) : ℝ) := by simp
    _ = hyperbolicCount d n := by
      rw [hyperbolicCount]
      exact_mod_cast shape_card d n hd

theorem cubeBumpEnergy_continuous {d n : ℕ} (ψ : AdmissibleBump) :
    Continuous (cubeBumpEnergy (d := d) (n := n) ψ) := by
  unfold cubeBumpEnergy
  apply continuous_finsetSum
  intro a ha
  exact (cubeBumpAtom_continuous ψ a).pow 2

theorem cubeBumpGoodSet_measurable {d n : ℕ} (ψ : AdmissibleBump) :
    MeasurableSet (cubeBumpGoodSet (d := d) (n := n) ψ) := by
  have hcube : MeasurableSet (cubeSet d) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have henergy : MeasurableSet
      ((cubeBumpEnergy (d := d) (n := n) ψ) ⁻¹'
        Set.Ici (cubeBumpEnergyMean (d := d) (n := n) ψ / 2)) :=
    (cubeBumpEnergy_continuous ψ).measurable measurableSet_Ici
  simpa [cubeBumpGoodSet, Set.inter_def] using hcube.inter henergy

theorem cubeBumpEnergy_integrable {d n : ℕ} (ψ : AdmissibleBump) :
    Integrable (cubeBumpEnergy (d := d) (n := n) ψ) (cubeLebesgue d) := by
  unfold cubeBumpEnergy
  exact integrable_finsetSum Finset.univ (fun a ha => cubeBumpAtom_sq_integrable ψ a)

theorem cubeBumpGoodRow_unit {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (hx : 0 < cubeBumpEnergy (d := d) (n := n) ψ x) :
    ∑ a : LayerIndex d n, (cubeBumpGoodRow ψ x a) ^ 2 = 1 := by
  unfold cubeBumpGoodRow cubeBumpEnergy
  simp_rw [div_pow]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a ha => sq_nonneg (cubeBumpAtom ψ x a))]
  exact div_self (ne_of_gt hx)

theorem cubeBumpGoodRow_unit_on_goodSet {d n : ℕ} (ψ : AdmissibleBump)
    (hd : 0 < d) (x : Fin d → ℝ)
    (hx : x ∈ cubeBumpGoodSet (d := d) (n := n) ψ) :
    ∑ a : LayerIndex d n, (cubeBumpGoodRow ψ x a) ^ 2 = 1 := by
  have hmeanPos : 0 < cubeBumpEnergyMean (d := d) (n := n) ψ := by
    rw [cubeBumpEnergyMean_eq_layerCount_mass_pow ψ hd]
    exact mul_pos (by
      rw [hyperbolicCount]
      exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1))
      (pow_pos ψ.squareIntegral_pos d)
  exact cubeBumpGoodRow_unit ψ x (lt_of_lt_of_le (half_pos hmeanPos) hx.2)

private def cubeBumpBadSet {d n : ℕ} (ψ : AdmissibleBump) : Set (Fin d → ℝ) :=
  {x | cubeBumpEnergy (d := d) (n := n) ψ x <
    cubeBumpEnergyMean (d := d) (n := n) ψ / 2}

/-- The actual good region has at least half the one-atom tensor mass. -/
theorem cubeBumpGoodMeasure_lower {d n : ℕ} (ψ : AdmissibleBump) (hd : 0 < d) :
    ENNReal.ofReal (ψ.squareIntegral ^ d / 2) ≤
      cubeBumpGoodMeasure (d := d) (n := n) ψ Set.univ := by
  classical
  let I : ℝ := ψ.squareIntegral
  let S : ℝ := hyperbolicCount d n
  let q : ℝ := I ^ d
  let μ : Measure (Fin d → ℝ) := cubeLebesgue d
  let bad : Set (Fin d → ℝ) := cubeBumpBadSet (d := d) (n := n) ψ
  let deficit : (Fin d → ℝ) → ℝ := fun x =>
    S - cubeBumpEnergy (d := d) (n := n) ψ x
  let B : ℝ := S - cubeBumpEnergyMean (d := d) (n := n) ψ / 2
  let scaled : (Fin d → ℝ) → ℝ := fun x => deficit x / B
  have hIpos : 0 < I := by dsimp [I]; exact ψ.squareIntegral_pos
  have hIle : I ≤ 1 := by dsimp [I]; exact ψ.squareIntegral_le_one
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    exact pow_le_one₀ (le_of_lt hIpos) hIle
  have hSpos : 0 < S := by
    dsimp [S, hyperbolicCount]
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hmean : cubeBumpEnergyMean (d := d) (n := n) ψ = S * q := by
    dsimp [S, q, I]
    rw [cubeBumpEnergyMean_eq_layerCount_mass_pow ψ hd]
  have hBpos : 0 < B := by
    dsimp [B]
    rw [hmean]
    nlinarith [hSpos, hqle]
  have henergyBound : ∀ x : Fin d → ℝ,
      cubeBumpEnergy (d := d) (n := n) ψ x ≤ S := by
    intro x
    simpa [S] using cubeBumpEnergy_le_layerCount ψ hd x
  have hbadmeas : MeasurableSet bad := by
    dsimp [bad, cubeBumpBadSet]
    exact measurableSet_lt (cubeBumpEnergy_continuous ψ).measurable measurable_const
  have hdeficitInt : Integrable deficit μ := by
    dsimp [deficit]
    exact (integrable_const S).sub (cubeBumpEnergy_integrable ψ)
  have hscaledInt : Integrable scaled μ := by
    simpa [scaled, div_eq_mul_inv, mul_comm] using hdeficitInt.const_mul B⁻¹
  have hscaledNonneg : 0 ≤ᵐ[μ] scaled := by
    filter_upwards with x
    dsimp [scaled, deficit]
    exact div_nonneg (sub_nonneg.mpr (henergyBound x)) (le_of_lt hBpos)
  have hmarkov := hscaledInt.measure_le_integral hscaledNonneg
    (s := bad) (by
      intro x hx
      change cubeBumpEnergy (d := d) (n := n) ψ x <
        cubeBumpEnergyMean (d := d) (n := n) ψ / 2 at hx
      change 1 ≤ (S - cubeBumpEnergy (d := d) (n := n) ψ x) / B
      rw [one_le_div hBpos]
      dsimp [B]
      rw [hmean]
      linarith)
  have hdeficitMean : ∫ x, deficit x ∂μ = S * (1 - q) := by
    dsimp [deficit, μ]
    rw [integral_sub (integrable_const S) (cubeBumpEnergy_integrable ψ)]
    rw [integral_const]
    have hmass : (cubeLebesgue d).real Set.univ = 1 := by simp [cubeLebesgue_univ]
    rw [hmass, one_smul]
    change S - cubeBumpEnergyMean (d := d) (n := n) ψ = S * (1 - q)
    rw [hmean]
    ring
  have hscaledMean : ∫ x, scaled x ∂μ ≤ 1 - q / 2 := by
    dsimp [scaled]
    rw [show (fun x => deficit x / B) = fun x => B⁻¹ * deficit x by
        funext x; ring,
      integral_const_mul, hdeficitMean]
    have hB : B = S * (1 - q / 2) := by
      dsimp [B]
      rw [hmean]
      ring
    rw [hB]
    have hden : 0 < 1 - q / 2 := by nlinarith [hqle]
    have hratio : (1 - q) / (1 - q / 2) ≤ 1 - q / 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [sq_nonneg q]
    calc
      (S * (1 - q / 2))⁻¹ * (S * (1 - q)) =
          (1 - q) / (1 - q / 2) := by field_simp
      _ ≤ 1 - q / 2 := hratio
  have hbadBound : μ bad ≤ ENNReal.ofReal (1 - q / 2) := by
    calc
      μ bad ≤ ENNReal.ofReal (∫ x, scaled x ∂μ) := hmarkov
      _ ≤ ENNReal.ofReal (1 - q / 2) := ENNReal.ofReal_le_ofReal hscaledMean
  have hbadNe : μ bad ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hbadBound (ENNReal.ofReal_lt_top))
  have hbadLeOne : μ bad ≤ 1 := by
    calc
      μ bad ≤ ENNReal.ofReal (1 - q / 2) := hbadBound
      _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [hqle])
  have hgoodEq :
      cubeBumpGoodMeasure (d := d) (n := n) ψ Set.univ = μ badᶜ := by
    rw [show cubeBumpGoodMeasure (d := d) (n := n) ψ Set.univ =
      cubeLebesgue d (cubeBumpGoodSet (d := d) (n := n) ψ) by simp [cubeBumpGoodMeasure]]
    rw [show μ badᶜ = cubeLebesgue d badᶜ by rfl]
    rw [cubeLebesgue]
    rw [Measure.restrict_apply (cubeBumpGoodSet_measurable ψ)]
    rw [Measure.restrict_apply hbadmeas.compl]
    congr 1
    ext x
    simp only [cubeBumpGoodSet, cubeBumpBadSet, bad, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
    tauto
  rw [hgoodEq, measure_compl hbadmeas hbadNe, measure_univ]
  apply (ENNReal.le_sub_iff_add_le_right hbadNe hbadLeOne).2
  calc
    ENNReal.ofReal (q / 2) + μ bad = μ bad + ENNReal.ofReal (q / 2) := add_comm _ _
    _ ≤ ENNReal.ofReal (1 - q / 2) + ENNReal.ofReal (q / 2) :=
      by gcongr
    _ = 1 := by
      have hleft : 0 ≤ q / 2 := by positivity
      have hright : 0 ≤ 1 - q / 2 := by linarith [hqle]
      rw [← ENNReal.ofReal_add hright hleft]
      rw [show (1 - q / 2) + q / 2 = 1 by ring, ENNReal.ofReal_one]

private theorem no_common_deeper_dyadic_cell_of_halves
    {k c l m : ℕ} {x y : ℝ} (hkl : k < l)
    (hx : x ∈ HaarQuarter.realDyadicLeftHalf k c)
    (hy : y ∈ HaarQuarter.realDyadicRightHalf k c)
    (hcx : x ∈ HaarQuarter.realDyadicCell l m)
    (hcy : y ∈ HaarQuarter.realDyadicCell l m) : False := by
  have hkl' : k + 1 ≤ l := by omega
  let q := l - (k + 1)
  have hl : l = (k + 1) + q := by dsimp [q]; omega
  have hpow : (2 : ℝ) ^ l = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ q := by
    rw [hl, pow_add]
  have hden0 : 0 < (2 : ℝ) ^ (k + 1) := by positivity
  have hden : 0 < (2 : ℝ) ^ l := by positivity
  simp only [HaarQuarter.realDyadicLeftHalf, Set.mem_Ico] at hx
  simp only [HaarQuarter.realDyadicRightHalf, Set.mem_Ico] at hy
  push_cast at hx hy
  simp only [HaarQuarter.realDyadicCell, Set.mem_Ico] at hcx hcy
  have hxscale : x * (2 : ℝ) ^ (k + 1) < (2 * c + 1 : ℝ) :=
    (lt_div_iff₀ hden0).mp hx.2
  have hyscale : (2 * c + 1 : ℝ) ≤ y * (2 : ℝ) ^ (k + 1) :=
    (div_le_iff₀ hden0).mp hy.1
  have hxlarge : x * (2 : ℝ) ^ l <
      (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) := by
    rw [hpow]
    have h := mul_lt_mul_of_pos_right hxscale (by positivity : 0 < (2:ℝ)^q)
    push_cast at h ⊢
    nlinarith
  have hylarge : (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) ≤
      y * (2 : ℝ) ^ l := by
    rw [hpow]
    have h := mul_le_mul_of_nonneg_right hyscale (by positivity : 0 ≤ (2:ℝ)^q)
    push_cast at h ⊢
    nlinarith
  have hmlow : (m : ℝ) ≤ x * (2 : ℝ) ^ l := (div_le_iff₀ hden).mp hcx.1
  have hmyhigh : y * (2 : ℝ) ^ l < (m : ℝ) + 1 := by
    have h := (lt_div_iff₀ hden).mp hcy.2
    push_cast at h ⊢
    nlinarith
  have hm_lt : (m : ℝ) < (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) := by linarith
  have hq_lt : (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) < (m : ℝ) + 1 := by linarith
  have hmNat : m < (2 * c + 1) * 2 ^ q := by exact_mod_cast hm_lt
  have hqNat : (2 * c + 1) * 2 ^ q < m + 1 := by exact_mod_cast hq_lt
  omega

private theorem no_common_deeper_dyadic_cell_of_pair
    {k c l m : ℕ} {x y : ℝ} (hkl : k < l)
    (hp : (x, y) ∈ BrownianSharp.AlignmentPaperContinuumHulls.oneDyadicOppositeHalfPair k c)
    (hx : x ∈ HaarQuarter.realDyadicCell l m)
    (hy : y ∈ HaarQuarter.realDyadicCell l m) : False := by
  rcases hp with hp | hp
  · exact no_common_deeper_dyadic_cell_of_halves hkl hp.1 hp.2 hx hy
  · exact no_common_deeper_dyadic_cell_of_halves hkl hp.2 hp.1 hy hx

theorem cubeBumpAtom_coordinate_mem_realDyadicCell
    {d n : ℕ} (ψ : AdmissibleBump) (x : Fin d → ℝ)
    (a : LayerIndex d n) (ha : cubeBumpAtom ψ x a ≠ 0) (i : Fin d) :
    x i ∈ HaarQuarter.realDyadicCell (layerIndexDepth a i) (layerIndexCell a i) := by
  have hfactor : ψ.atom ((2 : ℝ) ^ layerIndexDepth a i * x i -
      (layerIndexCell a i : ℝ)) ≠ 0 := cubeBumpAtom_factor_nonzero ψ x a ha i
  have harg : 0 < (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i ∧
      (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i < 1 := by
    by_contra h
    have hout : (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i ≤ 0 ∨
        1 ≤ (2 : ℝ) ^ layerIndexDepth a i * x i - layerIndexCell a i := by
      rcases not_and_or.mp h with h | h
      · exact Or.inl (le_of_not_gt h)
      · exact Or.inr (le_of_not_gt h)
    exact hfactor (ψ.eq_zero_of_outside hout)
  have hp : 0 < (2 : ℝ) ^ layerIndexDepth a i := by positivity
  have hpow : (2 : ℝ) ^ layerIndexDepth a i =
      ((2 ^ layerIndexDepth a i : ℕ) : ℝ) := by norm_cast
  rw [HaarQuarter.realDyadicCell, Set.mem_Ico]
  constructor
  · apply (div_le_iff₀ hp).2
    rw [hpow]
    push_cast
    nlinarith [harg.1]
  · apply (lt_div_iff₀ hp).2
    rw [hpow]
    push_cast
    nlinarith [harg.2]

theorem cubeBumpAtom_mem_realDyadicBox {d n : ℕ} (ψ : AdmissibleBump)
    (x : Fin d → ℝ) (a : LayerIndex d n) (ha : cubeBumpAtom ψ x a ≠ 0) :
    x ∈ BrownianSharp.AlignmentPaperContinuumHulls.realDyadicBox a := by
  intro i
  exact cubeBumpAtom_coordinate_mem_realDyadicCell ψ x a ha i

theorem cubeBumpAtomPair_depth_le_of_hullShell
    {d n : ℕ} {x y : Fin d → ℝ} (ψ : AdmissibleBump) (u : Fin d → ℕ)
    (hu : (fun i => (x i, y i)) ∈ tensorOppositeHullShell u)
    (a : LayerIndex d n) (hxa : cubeBumpAtom ψ x a ≠ 0)
    (hya : cubeBumpAtom ψ y a ≠ 0) : ∀ i, layerIndexDepth a i ≤ u i := by
  have hboxx := cubeBumpAtom_mem_realDyadicBox ψ x a hxa
  have hboxy := cubeBumpAtom_mem_realDyadicBox ψ y a hya
  have hu' : ∀ i, (x i, y i) ∈
      BrownianSharp.AlignmentPaperContinuumHulls.oneDyadicOppositeHalfShell (u i) := by
    simpa [tensorOppositeHullShell, Set.mem_pi] using hu
  intro i
  by_contra h
  have hlt : u i < layerIndexDepth a i := by omega
  rcases Set.mem_iUnion.mp (hu' i) with ⟨c, hc⟩
  rcases Set.mem_iUnion.mp hc with ⟨hcRange, hpair⟩
  exact no_common_deeper_dyadic_cell_of_pair hlt hpair
    (hboxx i) (hboxy i)

theorem cubeBumpAtom_pair_abs_sum_le_of_hullShell
    {d n h : ℕ} (hd : 0 < d) (ψ : AdmissibleBump)
    (x y : Fin d → ℝ) (u : Fin d → ℕ)
    (hu : (fun i => (x i, y i)) ∈ tensorOppositeHullShell u)
    (hgrade : (∑ i : Fin d, u i) = n + h) :
    (∑ a : LayerIndex d n, |cubeBumpAtom ψ x a * cubeBumpAtom ψ y a|) ≤
      min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) := by
  classical
  let c : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm u
  have hci (i : Fin d) : c i = u i := by rfl
  have hc : c.sum (fun _ z => z) = n + h := by
    simpa [c, Finsupp.sum_fintype] using hgrade
  let f : LayerIndex d n → ℝ := fun a =>
    |cubeBumpAtom ψ x a * cubeBumpAtom ψ y a|
  have hnonneg : ∀ a, 0 ≤ f a := fun _ => abs_nonneg _
  have hbound : ∀ a, f a ≤ 1 := by
    intro a
    dsimp [f]
    rw [abs_mul]
    have hx := cubeBumpAtom_abs_le_one ψ x a
    have hy := cubeBumpAtom_abs_le_one ψ y a
    calc
      |cubeBumpAtom ψ x a| * |cubeBumpAtom ψ y a| ≤
          1 * |cubeBumpAtom ψ y a| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hy (by norm_num)
      _ = 1 := by norm_num
  have hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i := by
    intro a ha i
    have hfpos : |cubeBumpAtom ψ x a * cubeBumpAtom ψ y a| > 0 := by
      simpa [f] using ha
    have hprod : cubeBumpAtom ψ x a * cubeBumpAtom ψ y a ≠ 0 := abs_pos.mp hfpos
    have hxa : cubeBumpAtom ψ x a ≠ 0 := by
      intro hz
      exact hprod (by simp [hz])
    have hya : cubeBumpAtom ψ y a ≠ 0 := by
      intro hz
      exact hprod (by simp [hz])
    have hbnd := cubeBumpAtomPair_depth_le_of_hullShell ψ u hu a hxa hya i
    simpa [hci i] using hbnd
  have hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b := by
    intro a b ha hb hdepth
    have hprodA : cubeBumpAtom ψ x a * cubeBumpAtom ψ y a ≠ 0 :=
      abs_pos.mp (by simpa [f] using ha)
    have hprodB : cubeBumpAtom ψ x b * cubeBumpAtom ψ y b ≠ 0 :=
      abs_pos.mp (by simpa [f] using hb)
    have hxa : cubeBumpAtom ψ x a ≠ 0 := fun hz => hprodA (by simp [hz])
    have hxb : cubeBumpAtom ψ x b ≠ 0 := fun hz => hprodB (by simp [hz])
    exact cubeBumpAtom_unique_address ψ x a b hdepth hxa hxb
  have hsum := BrownianSharp.layerRowProduct_sum_le_of_support hd c hc f 1
    (by norm_num) hnonneg hbound hsupport hunique
  simpa [f] using hsum

theorem cubeBumpGoodSet_coordinates_Ioo {d n : ℕ} (ψ : AdmissibleBump)
    (hd : 0 < d) {x : Fin d → ℝ}
    (hx : x ∈ cubeBumpGoodSet (d := d) (n := n) ψ) (i : Fin d) :
    x i ∈ Set.Ioo (0 : ℝ) 1 := by
  have hmean : 0 < cubeBumpEnergyMean (d := d) (n := n) ψ := by
    rw [cubeBumpEnergyMean_eq_layerCount_mass_pow ψ hd]
    exact mul_pos (by
      rw [hyperbolicCount]
      exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1))
      (pow_pos ψ.squareIntegral_pos d)
  have hcube : x i ∈ Set.Icc (0 : ℝ) 1 := hx.1 i (Set.mem_univ i)
  have hboundary (hxi : x i = 0 ∨ x i = 1) :
      cubeBumpEnergy (d := d) (n := n) ψ x = 0 := by
    have hatom (a : LayerIndex d n) : cubeBumpAtom ψ x a = 0 := by
      unfold cubeBumpAtom
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rcases hxi with hzero | hone
      · rw [hzero]
        have ht : (2 : ℝ) ^ layerIndexDepth a i * 0 - layerIndexCell a i ≤ 0 := by
          have hp : 0 ≤ (2 : ℝ) ^ layerIndexDepth a i := by positivity
          have hc : 0 ≤ (layerIndexCell a i : ℝ) := by positivity
          nlinarith
        exact ψ.eq_zero_of_outside (Or.inl ht)
      · rw [hone]
        have hp : (2 : ℝ) ^ layerIndexDepth a i =
            (2 ^ layerIndexDepth a i : ℕ) := by norm_cast
        have hc : layerIndexCell a i + 1 ≤ 2 ^ layerIndexDepth a i :=
          Nat.succ_le_of_lt (layerIndexCell_lt a i)
        have hcreal : (layerIndexCell a i : ℝ) + 1 ≤
            (2 : ℝ) ^ layerIndexDepth a i := by exact_mod_cast hc
        have ht : 1 ≤ (2 : ℝ) ^ layerIndexDepth a i * 1 -
            (layerIndexCell a i : ℝ) := by nlinarith [hcreal]
        exact ψ.eq_zero_of_outside (Or.inr ht)
    unfold cubeBumpEnergy
    simp [hatom]
  have hnot : ¬(x i = 0 ∨ x i = 1) := by
    intro hb
    have hz := hboundary hb
    have hgood := hx.2
    rw [hz] at hgood
    linarith [hmean]
  constructor
  · by_contra h
    exact hnot (Or.inl (le_antisymm (le_of_not_gt h) hcube.1))
  · by_contra h
    exact hnot (Or.inr (le_antisymm hcube.2 (le_of_not_gt h)))

theorem cubeBumpGoodRow_measurable {d n : ℕ} (ψ : AdmissibleBump)
    (a : LayerIndex d n) :
    Measurable (fun x : Fin d → ℝ => cubeBumpGoodRow ψ x a) := by
  unfold cubeBumpGoodRow
  exact (cubeBumpAtom_continuous ψ a).measurable.div
    ((Real.continuous_sqrt.comp (cubeBumpEnergy_continuous ψ)).measurable)

theorem cubeBumpRowCorrelation_eq_zero_of_lowHullShell
    {d n : ℕ} (ψ : AdmissibleBump) (x y : Fin d → ℝ) (u : Fin d → ℕ)
    (hu : (fun i => (x i, y i)) ∈ tensorOppositeHullShell u)
    (hgrade : (∑ i : Fin d, u i) < n) :
    BrownianSharp.AlignmentPaperGenericContinuumVariance.rowCorrelation
      (κ := LayerIndex d n) (cubeBumpGoodRow (d := d) (n := n) ψ) x y = 0 := by
  classical
  have hprod0 (a : LayerIndex d n) : cubeBumpAtom ψ x a * cubeBumpAtom ψ y a = 0 := by
    by_contra hne
    have hxa : cubeBumpAtom ψ x a ≠ 0 := by
      intro hz
      exact hne (by simp [hz])
    have hya : cubeBumpAtom ψ y a ≠ 0 := by
      intro hz
      exact hne (by simp [hz])
    have hdepth := cubeBumpAtomPair_depth_le_of_hullShell ψ u hu a hxa hya
    have hshape := layerIndexDepth_grade a
    have hsum : (∑ i : Fin d, layerIndexDepth a i) = n := by
      simpa [Finsupp.sum_fintype, layerIndexDepth] using hshape
    have hle : (∑ i : Fin d, layerIndexDepth a i) ≤ ∑ i : Fin d, u i :=
      Finset.sum_le_sum (fun i hi => hdepth i)
    omega
  unfold BrownianSharp.AlignmentPaperGenericContinuumVariance.rowCorrelation
  apply Finset.sum_eq_zero
  intro a ha
  unfold cubeBumpGoodRow
  rw [div_mul_div_comm, hprod0 a]
  simp

theorem cubeBumpRowCorrelation_abs_le_of_hullShell
    {d n h : ℕ} (ψ : AdmissibleBump) (hd : 0 < d)
    (x y : Fin d → ℝ)
    (hx : x ∈ cubeBumpGoodSet (d := d) (n := n) ψ)
    (hy : y ∈ cubeBumpGoodSet (d := d) (n := n) ψ)
    (u : Fin d → ℕ)
    (hu : (fun i => (x i, y i)) ∈ tensorOppositeHullShell u)
    (hgrade : (∑ i : Fin d, u i) = n + h) :
  |BrownianSharp.AlignmentPaperGenericContinuumVariance.rowCorrelation
      (κ := LayerIndex d n) (cubeBumpGoodRow (d := d) (n := n) ψ) x y| ≤ shapeOverlapCap d n h
        (2 / ψ.squareIntegral ^ d) := by
  classical
  let I : ℝ := ψ.squareIntegral
  let Cn : ℝ := hyperbolicCount d n
  let Ex := cubeBumpEnergy (d := d) (n := n) ψ x
  let Ey := cubeBumpEnergy (d := d) (n := n) ψ y
  have hIpos : 0 < I := by dsimp [I]; exact ψ.squareIntegral_pos
  have hCnpos : 0 < Cn := by
    dsimp [Cn]
    exact hyperbolicCount_pos (by omega)
  have hEx : Ex ≥ Cn * I ^ d / 2 := by
    have hmean := cubeBumpEnergyMean_eq_layerCount_mass_pow (d := d) (n := n) ψ hd
    have hgood := hx.2
    dsimp [Ex, Cn, I] at hgood ⊢
    rw [hmean] at hgood
    linarith
  have hEy : Ey ≥ Cn * I ^ d / 2 := by
    have hmean := cubeBumpEnergyMean_eq_layerCount_mass_pow (d := d) (n := n) ψ hd
    have hgood := hy.2
    dsimp [Ey, Cn, I] at hgood ⊢
    rw [hmean] at hgood
    linarith
  have hdenpos : 0 < Real.sqrt Ex * Real.sqrt Ey := by
    apply mul_pos
    · exact Real.sqrt_pos.2 (by nlinarith [hIpos, hCnpos, pow_pos hIpos d])
    · exact Real.sqrt_pos.2 (by nlinarith [hIpos, hCnpos, pow_pos hIpos d])
  have hden : Cn * I ^ d / 2 ≤ Real.sqrt Ex * Real.sqrt Ey := by
    have hsx := Real.sqrt_le_sqrt hEx
    have hsy := Real.sqrt_le_sqrt hEy
    have hprod : Real.sqrt (Cn * I ^ d / 2) * Real.sqrt (Cn * I ^ d / 2) ≤
        Real.sqrt Ex * Real.sqrt Ey := by
      calc
        Real.sqrt (Cn * I ^ d / 2) * Real.sqrt (Cn * I ^ d / 2) ≤
            Real.sqrt Ex * Real.sqrt (Cn * I ^ d / 2) :=
          mul_le_mul_of_nonneg_right hsx (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt Ex * Real.sqrt Ey :=
          mul_le_mul_of_nonneg_left hsy (Real.sqrt_nonneg _)
    have hsq : Real.sqrt (Cn * I ^ d / 2) * Real.sqrt (Cn * I ^ d / 2) =
        Cn * I ^ d / 2 := by rw [Real.mul_self_sqrt (by positivity)]
    calc
      Cn * I ^ d / 2 =
          Real.sqrt (Cn * I ^ d / 2) * Real.sqrt (Cn * I ^ d / 2) := hsq.symm
      _ ≤ Real.sqrt Ex * Real.sqrt Ey := hprod
  have hnum := cubeBumpAtom_pair_abs_sum_le_of_hullShell hd ψ x y u hu hgrade
  have hcorrEq :
      BrownianSharp.AlignmentPaperGenericContinuumVariance.rowCorrelation
        (κ := LayerIndex d n) (cubeBumpGoodRow (d := d) (n := n) ψ) x y =
      (∑ a : LayerIndex d n, cubeBumpAtom ψ x a * cubeBumpAtom ψ y a) /
        (Real.sqrt Ex * Real.sqrt Ey) := by
    unfold BrownianSharp.AlignmentPaperGenericContinuumVariance.rowCorrelation
      cubeBumpGoodRow
    simp_rw [div_mul_div_comm]
    rw [Finset.sum_div]
  have hnumAbs : |∑ a : LayerIndex d n,
      cubeBumpAtom ψ x a * cubeBumpAtom ψ y a| ≤
      (min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) : ℕ) := by
    calc
      _ ≤ ∑ a : LayerIndex d n,
          |cubeBumpAtom ψ x a * cubeBumpAtom ψ y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by exact_mod_cast hnum
  rw [hcorrEq, abs_div, abs_of_pos hdenpos]
  have hMnonneg : 0 ≤
      min Cn (hyperbolicCount d h) :=
    le_min hCnpos.le (hyperbolicCount_pos (by omega)).le
  have hM : |∑ a : LayerIndex d n,
      cubeBumpAtom ψ x a * cubeBumpAtom ψ y a| ≤
      min Cn (hyperbolicCount d h) := by
    simpa [Cn, hyperbolicCount] using hnumAbs
  have hquot₁ := div_le_div_of_nonneg_right hM (le_of_lt hdenpos)
  have hfloorpos : 0 < Cn * I ^ d / 2 := by positivity
  have hquot₂ := div_le_div_of_nonneg_left hMnonneg hfloorpos hden
  calc
    |∑ a : LayerIndex d n, cubeBumpAtom ψ x a * cubeBumpAtom ψ y a| /
        (Real.sqrt Ex * Real.sqrt Ey) ≤
      min Cn (hyperbolicCount d h) /
          (Real.sqrt Ex * Real.sqrt Ey) := hquot₁
    _ ≤ (min Cn (hyperbolicCount d h)) / (Cn * I ^ d / 2) := hquot₂
    _ = _ := by
      rw [shapeOverlapCap]
      dsimp [Cn, I, hyperbolicCount]
      field_simp [ne_of_gt hIpos, ne_of_gt hCnpos] <;> ring

/-- The arbitrary admissible bump induces the exact region-row structure used
by the generic continuum variance and confinement theorems. -/
def cubeBumpRegionRows {d n : ℕ} (ψ : AdmissibleBump) (hd : 2 ≤ d) :
    BrownianSharp.AlignmentPaperGenericContinuumVariance.RegionRows d n
      (LayerIndex d n) (ψ.squareIntegral ^ d / 2) (2 / ψ.squareIntegral ^ d) := by
  classical
  refine ⟨cubeBumpGoodSet (d := d) (n := n) ψ,
    cubeBumpGoodSet_measurable (d := d) (n := n) ψ, ?_, ?_,
    cubeBumpGoodRow (d := d) (n := n) ψ, ?_, ?_, ?_, ?_⟩
  · simpa [cubeBumpGoodMeasure, Measure.restrict_apply,
      cubeBumpGoodSet_measurable ψ] using cubeBumpGoodMeasure_lower ψ (by omega : 0 < d)
  · intro x hx i
    exact ⟨(cubeBumpGoodSet_coordinates_Ioo ψ (by omega) hx i).1.le,
      (cubeBumpGoodSet_coordinates_Ioo ψ (by omega) hx i).2⟩
  · intro a
    exact cubeBumpGoodRow_measurable ψ a
  · intro x hx
    exact cubeBumpGoodRow_unit_on_goodSet ψ (by omega) x hx
  · intro x hx y hy u hu hgrade
    exact cubeBumpRowCorrelation_eq_zero_of_lowHullShell ψ x y u hu hgrade
  · intro x hx y hy u hu hge
    apply cubeBumpRowCorrelation_abs_le_of_hullShell ψ (by omega) x y hx hy u hu
    omega

end BrownianSharp.AlignmentPaperContinuumGenericBump
