import KLS.RadialTailProfile

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def radialAverageKernel (a : ℝ → ℝ) (c : Space n) (t : ℝ) (x : Space n) : ℝ :=
  a (radialSquaredCoordinate c t x) / t ^ n

def radialAverageKernelScaleDerivative (a : ℝ → ℝ) (c : Space n) (t : ℝ) (x : Space n) : ℝ :=
  (-((n : ℝ) * a (radialSquaredCoordinate c t x) +
    2 * radialSquaredCoordinate c t x * deriv a (radialSquaredCoordinate c t x))) / t ^ (n+1)

lemma hasDerivAt_radialSquaredCoordinate (c x : Space n) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun r => radialSquaredCoordinate c r x) (-2 * ‖x-c‖ ^ 2 / t ^ 3) t := by
  have hh := (hasDerivAt_const t (‖x-c‖ ^ 2)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht)
  convert hh using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_mul, zero_sub]
    field_simp [ht]

lemma hasDerivAt_radialAverageKernel {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (c x : Space n) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun r => radialAverageKernel a c r x)
      (radialAverageKernelScaleDerivative a c t x) t := by
  have hnum := ((ha.differentiable (by norm_num) _).hasDerivAt).comp t
    (hasDerivAt_radialSquaredCoordinate c x ht)
  have hh := hnum.div ((hasDerivAt_id t).pow n) (pow_ne_zero _ ht)
  convert hh using 1
  · rfl
  · dsimp only [radialAverageKernelScaleDerivative, radialSquaredCoordinate, Pi.pow_apply, id_eq, Function.comp_apply]
    cases n with
    | zero => simp; ring
    | succ k =>
      simp only [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
      ring

lemma radialAverageKernelScaleDerivative_eq_laplacian {a : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (c x : Space n) {t : ℝ} (ht : t ≠ 0) :
    radialAverageKernelScaleDerivative a c t x = t / (2 * t ^ n) *
      coordinateLaplacian (fun y => radialTailProfile a (radialSquaredCoordinate c t y)) x := by
  rw [coordinateLaplacian_radialTailProfile ha c x ht]
  dsimp only [radialAverageKernelScaleDerivative]
  rw [pow_succ]
  field_simp [ht]

lemma radialSquaredCoordinate_ge_one {c x : Space n} {t : ℝ} (ht : 0 < t)
    (hx : x ∉ closedBall c t) : 1 ≤ radialSquaredCoordinate c t x := by
  have hx' : t < ‖x-c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
  dsimp only [radialSquaredCoordinate]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith

lemma tsupport_radial_composition_subset_closedBall {b : ℝ → ℝ}
    (hb : ∀ s, 1 ≤ s → b s = 0) (c : Space n) {t : ℝ} (ht : 0 < t) :
    tsupport (fun x => b (radialSquaredCoordinate c t x)) ⊆ closedBall c t := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hnot
  exact hx (hb _ (radialSquaredCoordinate_ge_one ht hnot))

lemma tsupport_radialAverageKernel_subset_closedBall {a : ℝ → ℝ}
    (ha0 : ∀ s, 1 ≤ s → a s = 0) (c : Space n) {t : ℝ} (ht : 0 < t) :
    tsupport (radialAverageKernel a c t) ⊆ closedBall c t := by
  exact tsupport_mul_subset_left.trans
    (tsupport_radial_composition_subset_closedBall ha0 c ht)

lemma contDiff_radialAverageKernel {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (c : Space n) (t : ℝ) : ContDiff ℝ 1 (radialAverageKernel a c t) :=
  (ha.comp ((contDiff_radialSquaredCoordinate c t).of_le (by simp))).div_const _

lemma radialAverageKernel_nonneg {a : ℝ → ℝ} (ha : ∀ s, 0 ≤ a s)
    (c x : Space n) {t : ℝ} (ht : 0 < t) : 0 ≤ radialAverageKernel a c t x :=
  div_nonneg (ha _) (pow_nonneg ht.le _)

lemma contDiff_radialTailTest {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (c : Space n) (t : ℝ) :
    ContDiff ℝ 2 (fun x => radialTailProfile a (radialSquaredCoordinate c t x)) :=
  (contDiff_radialTailProfile ha).comp ((contDiff_radialSquaredCoordinate c t).of_le (by simp))

lemma tsupport_radialTailTest_subset_closedBall {a : ℝ → ℝ}
    (ha0 : ∀ s, 1 ≤ s → a s = 0) (c : Space n) {t : ℝ} (ht : 0 < t) :
    tsupport (fun x => radialTailProfile a (radialSquaredCoordinate c t x)) ⊆ closedBall c t :=
  tsupport_radial_composition_subset_closedBall (fun _ hs => radialTailProfile_eq_zero ha0 hs) c ht

end KLS
end
