import KLS.MomentCenteredSections

/-! Contact-set geometry for the actual coercive source potential.
A small strictly convex quadratic perturbation of an affine functional
constructs a strictly exposed contact point inside a compact sublevel.
This avoids assuming a separate exposed-point approximation theorem. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def supportContactSet (u : Space n → ℝ) (x p : Space n) : Set (Space n) :=
  {y | u y = u x + inner ℝ p (y - x)}

theorem self_mem_supportContactSet (u : Space n → ℝ) (x p : Space n) :
    x ∈ supportContactSet u x p := by
  simp [supportContactSet]

theorem isClosed_supportContactSet {u : Space n → ℝ} (hu : Continuous u) (x p : Space n) :
    IsClosed (supportContactSet u x p) :=
  isClosed_eq hu (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))

theorem supportContactSet_eq_tilted_sublevel {u : Space n → ℝ} {x p : Space n}
    (hp : p ∈ convexSubgradient u x) :
    supportContactSet u x p = {y | tiltedPotential u p y ≤ tiltedPotential u p x} := by
  ext y
  have hs := hp y
  simp only [supportContactSet, tiltedPotential, mem_ofPred_eq, inner_sub_right] at *
  constructor <;> intro h <;> linarith

theorem convex_supportContactSet {u : Space n → ℝ} (hc : ConvexOn ℝ univ u)
    {x p : Space n} (hp : p ∈ convexSubgradient u x) : Convex ℝ (supportContactSet u x p) := by
  rw [supportContactSet_eq_tilted_sublevel hp]
  convert (convexOn_tiltedPotential hc p).convex_le (tiltedPotential u p x) using 1
  ext y
  simp only [mem_ofPred_eq, mem_univ, true_and]

theorem isCompact_contact_sublevel {u : Space n → ℝ} (hu : Continuous u)
    (hc : ConvexOn ℝ univ u) [IsFiniteMeasure (potentialMeasure u)]
    (x p : Space n) (R : ℝ) :
    IsCompact (supportContactSet u x p ∩ {y | u y ≤ R}) :=
  (isCompact_sublevel_of_finite_potentialMeasure hu hc R).inter_left
    (isClosed_supportContactSet hu x p)

/-- A compact portion of the contact set has a strictly exposed point that
lies below the chosen sublevel boundary. The exposed point is constructed by
maximizing a small quadratic perturbation of the supporting affine slope. -/
theorem exists_strict_exposed_contact_in_sublevel {u : Space n → ℝ} (hu : Continuous u)
    (hc : ConvexOn ℝ univ u) [IsFiniteMeasure (potentialMeasure u)]
    {x p : Space n} (hp : p ∈ convexSubgradient u x) {R : ℝ} (hR : u x < R) :
    ∃ z v : Space n, z ∈ supportContactSet u x p ∧ u z < R ∧
      ∀ y ∈ supportContactSet u x p, u y ≤ R → y ≠ z → inner ℝ v (y - z) < 0 := by
  let K := supportContactSet u x p ∩ {y | u y ≤ R}
  have hK : IsCompact K := isCompact_contact_sublevel hu hc x p R
  have hx : x ∈ K := ⟨self_mem_supportContactSet u x p, hR.le⟩
  obtain ⟨M, hMpos, hM⟩ := hK.isBounded.exists_pos_norm_le
  let ε : ℝ := (R - u x) / (2 * (M ^ 2 + 1))
  have hε : 0 < ε := div_pos (sub_pos.mpr hR) (by positivity)
  have hεeq : ε * (2 * (M ^ 2 + 1)) = R - u x :=
    div_mul_cancel₀ _ (by positivity)
  have hεM : ε * M ^ 2 < R - u x := by nlinarith [sq_nonneg M]
  let F : Space n → ℝ := fun y => ε * ‖y‖ ^ 2 - inner ℝ p y
  have hFcont : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hFcont.continuousOn
  have hzx : F x ≤ F z := hmax hx
  have hzcontact : u z = u x + inner ℝ p (z - x) := hz.1
  have hzM : ‖z‖ ^ 2 ≤ M ^ 2 := by
    have hm := hM z hz
    nlinarith [norm_nonneg z]
  have hzu : u z < R := by
    dsimp [F] at hzx
    rw [inner_sub_right] at hzcontact
    nlinarith [mul_le_mul_of_nonneg_left hzM hε.le, mul_nonneg hε.le (sq_nonneg ‖x‖)]
  let v : Space n := (2 * ε) • z - p
  refine ⟨z, v, hz.1, hzu, ?_⟩
  intro y hy hyR hyz
  have hymax : F y ≤ F z := hmax ⟨hy, hyR⟩
  have hn : 0 < ‖y - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz))
  have hquad := norm_sub_sq_real y z
  have hip : inner ℝ v (y - z) =
      2 * ε * (inner ℝ z y - ‖z‖ ^ 2) - (inner ℝ p y - inner ℝ p z) := by
    simp only [v, inner_sub_left, real_inner_smul_left, inner_sub_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [hip]
  dsimp [F] at hymax
  rw [real_inner_comm] at hquad
  nlinarith [mul_pos hε hn]

end KLS
end

#print axioms KLS.convex_supportContactSet
#print axioms KLS.exists_strict_exposed_contact_in_sublevel
