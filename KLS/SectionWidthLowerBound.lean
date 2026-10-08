import KLS.SectionWidthControl

/-!
# Positive normalized width at a deep point

The supporting-width estimate has a positive lower bound independent of the
height of the section whenever the point has a fixed proportion of its depth.
All constants are the actual finite density and volume bounds.
-/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

lemma directional_width_lower_bound_real {n : ℕ} (hn : n ≠ 0)
    {A B θ s h m δ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hθ : 0 < θ) (hs : 0 < s)
    (hh : 0 < h) (hδ : 0 < δ) (hm : θ * h ≤ m)
    (hbound : A * (m / (2 * δ) * (m / s) ^ (n - 1)) ≤ B * (4 * h) ^ n) :
    A * θ ^ n / (2 * B * 4 ^ n * s ^ (n - 1)) ≤ δ := by
  have hp : (θ * h) ^ n ≤ m ^ n := pow_le_pow_left₀ (by positivity) hm n
  have hprod : m / (2 * δ) * (m / s) ^ (n - 1) =
      m ^ n / (2 * δ * s ^ (n - 1)) := by
    rw [div_pow, div_mul_div_comm, mul_comm m, pow_sub_one_mul hn]
  rw [hprod, ← mul_div_assoc] at hbound
  have hclear := (div_le_iff₀ (by positivity : 0 < 2 * δ * s ^ (n - 1))).mp hbound
  have hscaled : (A * θ ^ n) * h ^ n ≤
      (2 * B * 4 ^ n * s ^ (n - 1) * δ) * h ^ n := by
    calc
      _ = A * (θ * h) ^ n := by rw [mul_pow]; ring
      _ ≤ A * m ^ n := mul_le_mul_of_nonneg_left hp hA.le
      _ ≤ (B * (4 * h) ^ n) * (2 * δ * s ^ (n - 1)) := hclear
      _ = _ := by rw [mul_pow]; ring
  have hcancel := le_of_mul_le_mul_right hscaled (pow_pos hh n)
  apply (div_le_iff₀ (by positivity : 0 < 2 * B * 4 ^ n * s ^ (n - 1))).mpr
  nlinarith

theorem directional_width_lower_bound_ennreal {n : ℕ} (hn : n ≠ 0)
    {a b : ℝ≥0∞} (ha : 0 < a) (hatop : a < ∞)
    (hb : 0 < b) (hbtop : b < ∞)
    {θ s h m δ : ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hh : 0 < h) (hδ : 0 < δ) (hm : θ * h ≤ m)
    (hbound : a * (ENNReal.ofReal (m / (2 * δ)) *
      ENNReal.ofReal (m / s) ^ (n - 1)) ≤ b * ENNReal.ofReal ((4 * h) ^ n)) :
    0 < a.toReal * θ ^ n / (2 * b.toReal * 4 ^ n * s ^ (n - 1)) ∧
      a.toReal * θ ^ n / (2 * b.toReal * 4 ^ n * s ^ (n - 1)) ≤ δ := by
  have hA : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hatop.ne
  have hB : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop.ne
  have hmpos : 0 < m := lt_of_lt_of_le (mul_pos hθ hh) hm
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ m / (2 * δ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ m / s),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (4 * h) ^ n)] at hreal
  exact ⟨by positivity,
    directional_width_lower_bound_real hn hA hB hθ hs hh hδ hm hreal⟩

/-- The lower supporting width depends only on dimension, the density bounds,
and the proportion of section depth, independently of section height. -/
def normalizedSectionWidthConstant (n : ℕ) (a b : ℝ≥0∞) (θ : ℝ) : ℝ :=
  a.toReal * θ ^ n /
    (2 * (b * volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3))).toReal *
      4 ^ n * ((n : ℝ) * (4 * ((n : ℝ) + 1) ^ 3)) ^ (n - 1))

theorem normalizedSectionWidthConstant_pos {n : ℕ} (hn : 0 < n)
    {a b : ℝ≥0∞} (ha : 0 < a) (hatop : a < ∞)
    (hb : 0 < b) (hbtop : b < ∞) {θ : ℝ} (hθ : 0 < θ) :
    0 < normalizedSectionWidthConstant n a b θ := by
  have hA : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hatop.ne
  have hR : 0 < 2 * ((n : ℝ) + 1) ^ 3 := by positivity
  have hvol : 0 < volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3)) :=
    measure_closedBall_pos volume _ hR
  have hvoltop : volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3)) < ∞ :=
    measure_closedBall_lt_top
  have hB : 0 < (b * volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3))).toReal :=
    ENNReal.toReal_pos (by positivity) (by finiteness)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold normalizedSectionWidthConstant
  positivity

/-- A single affine normalization works for every sufficiently deep point.
The explicit positive constant is chosen before the section and its height. -/
theorem exists_normalization_with_positive_directional_width
    {n : ℕ} (hn : 0 < n) {a b : ℝ≥0∞}
    (ha : 0 < a) (hatop : a < ∞) (hb : 0 < b) (hbtop : b < ∞)
    {θ : ℝ} (hθ : 0 < θ) {u : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {h : ℝ} (hh : 0 < h) (hosc : ∀ z ∈ K, -h ≤ u z ∧ u z ≤ 0)
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ b * volume S) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      closedBall 0 1 ⊆ e '' K ∧
      e '' K ⊆ closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ∀ (x v : Space n) (δ : ℝ), x ∈ e '' K →
        θ * h ≤ -u (e.symm x) → ‖v‖ = 1 → 0 < δ →
        (∀ z ∈ e '' K, inner ℝ v (z - x) ≤ δ) →
        normalizedSectionWidthConstant n a b θ ≤ δ := by
  obtain ⟨e, heinner, heouter, hewidth⟩ :=
    exists_normalization_with_directional_width_control hK hc hne hucont huconvex
      hboundary hh.le hosc hlower hupper
  refine ⟨e, heinner, heouter, ?_⟩
  intro x v δ hx hdepth hv hδ hsupport
  have hnegative : u (e.symm x) < 0 := by nlinarith [mul_pos hθ hh]
  have hbound := hewidth ⟨0, hn⟩ x v δ hx hnegative hv hδ hsupport
  have hR : 0 < 2 * ((n : ℝ) + 1) ^ 3 := by positivity
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hvol : 0 < volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3)) :=
    measure_closedBall_pos volume _ hR
  have hvoltop : volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3)) < ∞ :=
    measure_closedBall_lt_top
  have hbound' : a * (ENNReal.ofReal (-u (e.symm x) / (2 * δ)) *
      ENNReal.ofReal (-u (e.symm x) / ((n : ℝ) * (4 * ((n : ℝ) + 1) ^ 3))) ^ (n - 1)) ≤
      (b * volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3))) *
        ENNReal.ofReal ((4 * h) ^ n) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound
  exact (directional_width_lower_bound_ennreal hn.ne' ha hatop
    (by positivity) (by finiteness) hθ (by positivity) hh hδ hdepth hbound').2

end KLS
end

#print axioms KLS.directional_width_lower_bound_real
#print axioms KLS.directional_width_lower_bound_ennreal
#print axioms KLS.normalizedSectionWidthConstant_pos
#print axioms KLS.exists_normalization_with_positive_directional_width
