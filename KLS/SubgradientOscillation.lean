import KLS.ConvexSubgradient
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Elementary interior estimates on ordinary supporting slopes.  Bounded
oscillation on a ball bounds all slopes on the concentric half-ball. Combined
with a lower Alexandrov volume bound, it controls the density coefficient.
No differentiability or regularity of a Monge--Ampere solution is assumed. -/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem norm_subgradient_le_of_ball_oscillation {u : Space n → ℝ}
    {x p : Space n} (hp : p ∈ convexSubgradient u x)
    {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hupper : ∀ y ∈ closedBall x r, u y ≤ u x + h) : ‖p‖ ≤ h / r := by
  by_cases hpzero : p = 0
  · simp only [hpzero, norm_zero]
    exact div_nonneg hh hr.le
  · have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hpzero
    let y : Space n := x + (r / ‖p‖) • p
    have hydist : ‖y - x‖ = r := by
      simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hpn), div_mul_cancel₀ _ hpn.ne']
    have hy : y ∈ closedBall x r := by
      simpa only [mem_closedBall, dist_eq_norm, hydist] using (le_rfl : r ≤ r)
    have hs := hp y
    have hu := hupper y hy
    have hip : inner ℝ p (y - x) = r * ‖p‖ := by
      simp only [y, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hip] at hs
    apply (le_div_iff₀ hr).mpr
    nlinarith

theorem convexSubgradientImage_halfBall_subset {u : Space n → ℝ}
    {c : Space n} {r h a : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hosc : ∀ x ∈ closedBall c r, a ≤ u x ∧ u x ≤ a + h) :
    convexSubgradientImage u (closedBall c (r / 2)) ⊆ closedBall 0 (2 * h / r) := by
  rintro p ⟨x, hx, hp⟩
  have hxnorm : ‖x - c‖ ≤ r / 2 := hx
  have hxouter : x ∈ closedBall c r := by
    exact closedBall_subset_closedBall (by linarith) hx
  have hupper : ∀ y ∈ closedBall x (r / 2), u y ≤ u x + h := by
    intro y hy
    have hynorm : ‖y - x‖ ≤ r / 2 := hy
    have hyouter : y ∈ closedBall c r := by
      change ‖y - c‖ ≤ r
      calc
        _ ≤ ‖y - x‖ + ‖x - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ r := by linarith
    have h1 := (hosc x hxouter).1
    have h2 := (hosc y hyouter).2
    linarith
  have hnorm := norm_subgradient_le_of_ball_oscillation hp (by linarith : 0 < r / 2) hh hupper
  rw [mem_closedBall, dist_zero_right]
  convert hnorm using 1
  field_simp

/-- On a normalized ball, a lower Alexandrov density is controlled by the
oscillation. The numerical factor is explicit. -/
theorem alexandrov_density_le_of_unit_ball_oscillation {u : Space n → ℝ}
    {h : ℝ} (hh : 0 ≤ h)
    (hosc : ∀ x ∈ closedBall (0 : Space n) 1, -h ≤ u x ∧ u x ≤ 0)
    {a : ℝ≥0∞}
    (hmass : a * volume (closedBall (0 : Space n) (1 / 2)) ≤
      volume (convexSubgradientImage u (closedBall (0 : Space n) (1 / 2)))) :
    a ≤ ENNReal.ofReal ((4 * h) ^ n) := by
  have hsub : convexSubgradientImage u (closedBall (0 : Space n) (1 / 2)) ⊆
      closedBall 0 (2 * h) := by
    have hh' := convexSubgradientImage_halfBall_subset (by norm_num : (0 : ℝ) < 1) hh
      (a := -h) (fun x hx => by simpa only [neg_add_cancel] using hosc x hx)
    simpa only [div_one] using hh'
  have hle := hmass.trans (measure_mono hsub)
  have hscale : volume (closedBall (0 : Space n) (2 * h)) =
      ENNReal.ofReal ((4 * h) ^ n) * volume (closedBall (0 : Space n) (1 / 2)) := by
    have hs := Measure.addHaar_closedBall_mul (volume : Measure (Space n)) (0 : Space n)
      (by positivity : 0 ≤ 4 * h) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have heq : 4 * h * (1 / 2) = 2 * h := by ring
    simpa only [heq, Space, finrank_euclideanSpace_fin] using hs
  rw [hscale] at hle
  exact (ENNReal.mul_le_mul_iff_left
    (measure_closedBall_pos volume (0 : Space n) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
    measure_closedBall_lt_top.ne).mp hle

end KLS
end

#print axioms KLS.norm_subgradient_le_of_ball_oscillation
#print axioms KLS.alexandrov_density_le_of_unit_ball_oscillation
