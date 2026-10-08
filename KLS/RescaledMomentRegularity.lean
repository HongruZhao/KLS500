import KLS.QuadraticRescalingBounds

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma strictConvexOn_comp_continuousAffineEquiv {u : Space n → ℝ}
    (hu : StrictConvexOn ℝ univ u) (e : Space n ≃ᴬ[ℝ] Space n) :
    StrictConvexOn ℝ univ (u ∘ e) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  change u (e (a • x + b • y)) < _
  have he : e (a • x + b • y) = a • e x + b • e y :=
    Convex.combo_affine_apply (f := e.toAffineEquiv.toAffineMap) hab
  rw [he]
  exact hu.2 (mem_univ _) (mem_univ _) (fun he => hxy (e.injective he)) ha hb hab

lemma strictConvexOn_div_const {u : Space n → ℝ}
    (hu : StrictConvexOn ℝ univ u) {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ univ (fun x => u x / c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hh := hu.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  calc
    _ < (a * u x + b * u y) / c := div_lt_div_of_pos_right hh hc
    _ = a * (u x / c) + b * (u y / c) := by ring

/-- Strict convexity is preserved by the actual affine subtraction and
positive quadratic normalization. -/
theorem strictConvexOn_quadraticallyRescaledPotential {u : Space n → ℝ}
    (hu : StrictConvexOn ℝ univ u) (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    StrictConvexOn ℝ univ (quadraticallyRescaledPotential u x₀ p a r) := by
  have hcomp : StrictConvexOn ℝ univ (fun y => u (x₀ + r • y)) := by
    apply (strictConvexOn_comp_continuousAffineEquiv hu (scalarNormalizationEquiv x₀ r hr).symm).congr
    intro y _
    change u ((scalarNormalizationEquiv x₀ r hr).symm y) = _
    rw [scalarNormalizationEquiv_symm_apply]
  have hlin : ConcaveOn ℝ univ (fun y : Space n => r * inner ℝ p y + a) := by
    exact ((r • innerSL ℝ p).toLinearMap.concaveOn convex_univ).add_const a
  have hnum := hcomp.sub_concaveOn hlin
  have hdiv := strictConvexOn_div_const hnum (sq_pos_of_ne_zero hr)
  apply hdiv.congr
  intro y _
  dsimp [quadraticallyRescaledPotential]
  congr 1
  ring

lemma continuous_scalarNormalizedPotential {u : Space n → ℝ} (hu : Continuous u)
    (x₀ : Space n) (r : ℝ) : Continuous (scalarNormalizedPotential u x₀ r) := by
  unfold scalarNormalizedPotential
  fun_prop

lemma isFiniteMeasure_scalarNormalizedPotential {u : Space n → ℝ} (hu : Measurable u)
    [IsFiniteMeasure (potentialMeasure u)] (x₀ : Space n) {r : ℝ} (hr : r ≠ 0) :
    IsFiniteMeasure (potentialMeasure (scalarNormalizedPotential u x₀ r)) := by
  rw [← map_potentialMeasure_scalarNormalization hu x₀ hr]
  infer_instance

lemma isClosed_scalarNormalization_image {K : Set (Space n)} (hK : IsClosed K)
    (p : Space n) {r : ℝ} (hr : r ≠ 0) :
    IsClosed ((scalarNormalizationEquiv p r hr) '' K) :=
  (scalarNormalizationEquiv p r hr).toHomeomorph.isClosedMap _ hK

lemma convex_scalarNormalization_image {K : Set (Space n)} (hK : Convex ℝ K)
    (p : Space n) {r : ℝ} (hr : r ≠ 0) :
    Convex ℝ ((scalarNormalizationEquiv p r hr) '' K) :=
  Convex.affine_image (scalarNormalizationEquiv p r hr).toAffineEquiv.toAffineMap hK

end KLS
end
