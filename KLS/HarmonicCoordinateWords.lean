import KLS.HarmonicInteriorGradient

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Iterated actual coordinate Fréchet derivatives, in the displayed order. -/
def harmonicCoordinateWord : List (Fin n) → (Space n → ℝ) → Space n → ℝ
  | [], f => f
  | i :: w, f => coordinateDerivative (harmonicCoordinateWord w f) i

lemma contDiff_harmonicCoordinateWord {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : List (Fin n)) : ContDiff ℝ (⊤ : ℕ∞) (harmonicCoordinateWord w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact contDiff_coordinateDerivative ih (m := (⊤ : ℕ∞)) (by simp) i

lemma harmonicCoordinateWord_eventuallyEq {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[𝓝 x] g) (w : List (Fin n)) :
    harmonicCoordinateWord w f =ᶠ[𝓝 x] harmonicCoordinateWord w g := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy

lemma harmonicCoordinateWord_laplacian_eq_zero_on {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {U : Set (Space n)} (hU : IsOpen U)
    (hh : ∀ x ∈ U, coordinateLaplacian f x = 0) (w : List (Fin n)) :
    ∀ x ∈ U, coordinateLaplacian (harmonicCoordinateWord w f) x = 0 := by
  induction w with
  | nil => exact hh
  | cons i w ih =>
    intro x hx
    exact coordinateLaplacian_derivative_eq_zero_on
      ((contDiff_harmonicCoordinateWord hf w).of_le (by simp)) hU ih i hx

/-- Explicit successive Bernstein factors at halved radii. -/
def harmonicDerivativeFactor (n : ℕ) (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (120 + 8 * n) * harmonicDerivativeFactor n R k / (R / 2 ^ k) ^ 2

lemma harmonicDerivativeFactor_nonneg (n k : ℕ) (R : ℝ) :
    0 ≤ harmonicDerivativeFactor n R k := by
  induction k with
  | zero => simp [harmonicDerivativeFactor]
  | succ k ih => exact div_nonneg (mul_nonneg (by positivity) ih) (sq_nonneg _)

/-- Every finite word of actual derivatives has a quantitative interior bound,
obtained by repeated use of the proved Bernstein estimate. -/
theorem harmonicCoordinateWord_sq_le {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hh : ∀ x ∈ ball c R, coordinateLaplacian f x = 0)
    (hb : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B) (w : List (Fin n)) :
    ∀ x ∈ closedBall c (R / 2 ^ w.length),
      harmonicCoordinateWord w f x ^ 2 ≤ harmonicDerivativeFactor n R w.length * B := by
  induction w with
  | nil => simpa only [List.length_nil, pow_zero, div_one, harmonicCoordinateWord,
      harmonicDerivativeFactor, one_mul] using hb
  | cons i w ih =>
    intro x hx
    have hr : 0 < R / (2 : ℝ) ^ w.length := by positivity
    have hrle : R / (2 : ℝ) ^ w.length ≤ R :=
      div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hh' : ∀ y ∈ ball c (R / 2 ^ w.length),
        coordinateLaplacian (harmonicCoordinateWord w f) y = 0 := fun y hy =>
      harmonicCoordinateWord_laplacian_eq_zero_on hf isOpen_ball hh w y (ball_subset_ball hrle hy)
    have hx' : x ∈ closedBall c ((R / 2 ^ w.length) / 2) := by
      simpa only [List.length_cons, pow_succ, div_mul_eq_div_div] using hx
    have h := coordinateDerivative_sq_le_of_harmonic_on_ball
      ((contDiff_harmonicCoordinateWord hf w).of_le (by simp)) hr hh' ih i hx'
    simpa only [harmonicCoordinateWord, List.length_cons, harmonicDerivativeFactor,
      mul_div_assoc, mul_assoc, div_mul_eq_mul_div] using h

/-- The same bounds hold for an original function smooth only on its open
harmonic domain, by a proved extension near the outer closed ball. -/
theorem harmonicCoordinateWord_sq_le_of_harmonicOn {f : Space n → ℝ} {U : Set (Space n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hh : ∀ x ∈ U, coordinateLaplacian f x = 0)
    {c : Space n} {R B : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U)
    (hb : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B) (w : List (Fin n))
    {x : Space n} (hx : x ∈ closedBall c (R / 2 ^ w.length)) :
    harmonicCoordinateWord w f x ^ 2 ≤ harmonicDerivativeFactor n R w.length * B := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_eq_near_compact hU hf (isCompact_closedBall c R) hball
  have hglap : ∀ y ∈ ball c R, coordinateLaplacian g y = 0 := by
    intro y hy
    rw [coordinateLaplacian_eq_of_eventuallyEq (he.filter_mono
      (nhds_le_nhdsSet (ball_subset_closedBall hy)))]
    exact hh y (hball (ball_subset_closedBall hy))
  have hgbound : ∀ y ∈ closedBall c R, g y ^ 2 ≤ B := by
    intro y hy
    rw [he.self_of_nhdsSet hy]
    exact hb y hy
  have h := harmonicCoordinateWord_sq_le hg hR hglap hgbound w x hx
  have hrle : R / (2 : ℝ) ^ w.length ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hxR : x ∈ closedBall c R := closedBall_subset_closedBall hrle hx
  rwa [(harmonicCoordinateWord_eventuallyEq (he.filter_mono (nhds_le_nhdsSet hxR)) w).self_of_nhds] at h

lemma harmonicDerivativeFactor_two (R : ℝ) :
    harmonicDerivativeFactor n R 2 = 4 * (120 + 8 * n) ^ 2 / R ^ 4 := by
  simp only [harmonicDerivativeFactor, pow_zero, div_one, mul_one, pow_one]
  ring

lemma harmonicDerivativeFactor_three (R : ℝ) :
    harmonicDerivativeFactor n R 3 = 64 * (120 + 8 * n) ^ 3 / R ^ 6 := by
  rw [harmonicDerivativeFactor, harmonicDerivativeFactor_two]
  ring

/-- The actual viscosity-harmonic function inherits all finite-order interior
bounds; no differentiability is an input to this consumer. -/
theorem IsViscosityHarmonicOn.harmonicCoordinateWord_sq_le
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hb : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B)
    (w : List (Fin n)) {x : Space n} (hx : x ∈ closedBall c (R / 2 ^ w.length)) :
    harmonicCoordinateWord w f x ^ 2 ≤ harmonicDerivativeFactor n R w.length * B :=
  harmonicCoordinateWord_sq_le_of_harmonicOn hU (hf.contDiffOn hU)
    (fun _ hy => hf.coordinateLaplacian_eq_zero hU hy) hR hball hb w hx

end KLS
end
