import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentGeometricRanks

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPeriodicTail
open BrownianSharp.AlignmentPeriodicReconstruction
open BrownianSharp.SmoothResolution BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicEnergy

theorem geometric_tail_bound {d T : ℕ} (S : Finset (Fin d → ℕ))
    {q q' : ℝ} (hq : 0<q) (hqq' : q<q') (hq' : q'<1)
    (hgrade : ∀ s, s∉S → T≤∑ i,s i) :
    (∑' s : (Sᶜ : Set (Fin d → ℕ)), q^(∑ i,s.val i)) ≤
      (q/q')^T * ∑' s : Fin d → ℕ, q'^(∑ i,s i) := by
  classical
  have hq'pos : 0<q' := hq.trans hqq'
  have hq1 : q<1 := hqq'.trans hq'
  have hratio0 : 0≤q/q' := (div_pos hq hq'pos).le
  have hratio1 : q/q'≤1 := (div_le_one hq'pos).2 hqq'.le
  have hs := summable_shape_geometric d hq.le hq1
  have hs' := summable_shape_geometric d hq'pos.le hq'
  have hpoint : ∀ s : (Sᶜ : Set (Fin d → ℕ)),
      q^(∑ i,s.val i) ≤ (q/q')^T*q'^(∑ i,s.val i) := by
    intro s
    have hge := hgrade s.val s.property
    calc
      _ = (q/q')^(∑ i,s.val i)*q'^(∑ i,s.val i) := by
        rw [div_pow]
        exact (div_mul_cancel₀ _ (pow_ne_zero _ hq'pos.ne')).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hratio0 hratio1 hge) (pow_nonneg hq'pos.le _)
  calc
    _ ≤ ∑' s : (Sᶜ : Set (Fin d → ℕ)), (q/q')^T*q'^(∑ i,s.val i) :=
      (hs.subtype _).tsum_le_tsum hpoint ((hs'.subtype _).mul_left _)
    _ = (q/q')^T * ∑' s : (Sᶜ : Set (Fin d → ℕ)), q'^(∑ i,s.val i) := by
      rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.tsum_subtype_le (fun s : Fin d → ℕ => q'^(∑ i,s i))
        (Sᶜ : Set (Fin d → ℕ)) (fun _ => pow_nonneg hq'pos.le _) hs')
      (pow_nonneg hratio0 _)

theorem nikolsky_two_uniform_tail {d T : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) (hr : 1/2<r)
    (q' : ℝ) (hqq' : (2:ℝ)^(1/2-r)<q') (hq' : q'<1)
    (hgrade : ∀ s, s∉S → T≤∑ i,s i)
    (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f) :
    (∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.val f‖) ≤
      Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^T *
        ∑' s : Fin d → ℕ, q'^(∑ i,s i) := by
  have hq0 : 0<(2:ℝ)^(1/2-r) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r)<1 := hqq'.trans hq'
  have hs := summable_shape_geometric d hq0.le hq1
  have hb := hs.mul_left (Real.sqrt ((5:ℝ)^d))
  have hn := hb.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun s => nikolsky_two_block_sup_bound s f r hf)
  calc
    _ ≤ ∑' s : (Sᶜ : Set (Fin d → ℕ)),
        Real.sqrt ((5:ℝ)^d)*((2:ℝ)^(1/2-r))^(∑ i,s.val i) :=
      (hn.subtype _).tsum_le_tsum
        (fun s => nikolsky_two_block_sup_bound s.val f r hf) (hb.subtype _)
    _ = Real.sqrt ((5:ℝ)^d) *
        ∑' s : (Sᶜ : Set (Fin d → ℕ)), ((2:ℝ)^(1/2-r))^(∑ i,s.val i) := by rw [tsum_mul_left]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (geometric_tail_bound S hq0 hqq' hq' hgrade) (Real.sqrt_nonneg _)

theorem sobolev_two_uniform_tail {d T : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) (hr : 1/2<r)
    (q' : ℝ) (hqq' : (2:ℝ)^(1/2-r)<q') (hq' : q'<1)
    (hgrade : ∀ s, s∉S → T≤∑ i,s i)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    (∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.val f‖) ≤
      Real.sqrt ((5:ℝ)^d) * (((2:ℝ)^(1/2-r))/q')^T *
        ∑' s : Fin d → ℕ, q'^(∑ i,s i) :=
  nikolsky_two_uniform_tail S r hr q' hqq' hq' hgrade f
    (sobolev_two_subset_nikolsky_two r f hf)

end BrownianSharp.AlignmentPeriodicTail
