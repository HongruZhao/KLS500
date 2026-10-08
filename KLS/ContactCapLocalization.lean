import KLS.CoerciveContactGeometry

/-!
# Compact gaps for tilted contact sections

Small affine tilts of a nonnegative continuous function on a compact set
cannot create a nonpositive value away from its zero set. These explicit
compactness lemmas supply cap localization and keep the tilted section
away from the boundary. They do not assume strict convexity or a PDE
regularity theorem.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- A compact gap keeps small tilted sublevels in any strict cap containing
the zero set. The perturbing function need not be affine for this lemma. -/
theorem exists_pos_tilt_sublevel_in_cap
    {K : Set (Space n)} (hK : IsCompact K) {f q g : Space n → ℝ}
    (hf : Continuous f) (hq : Continuous q) (hg : Continuous g)
    (hfnn : ∀ x ∈ K, 0 ≤ f x) {δ : ℝ}
    (hzero : ∀ x ∈ K, f x = 0 → g x < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      ∀ x ∈ K, f x - t * q x ≤ 0 → g x < δ := by
  let B : Set (Space n) := K ∩ {x | δ ≤ g x}
  have hB : IsCompact B := hK.inter_right (isClosed_le continuous_const hg)
  by_cases hne : B.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hB.exists_isMinOn hne hf.continuousOn
    have hfy : 0 < f y := by
      refine lt_of_le_of_ne (hfnn y hy.1) ?_
      intro heq
      exact (not_lt_of_ge hy.2) (hzero y hy.1 heq.symm)
    obtain ⟨M, hM, hbound⟩ := (hK.image hq).isBounded.exists_pos_norm_le
    let ε : ℝ := f y / (2 * M)
    have hε : 0 < ε := div_pos hfy (mul_pos zero_lt_two hM)
    have hεeq : ε * (2 * M) = f y := div_mul_cancel₀ _ (by positivity)
    refine ⟨ε, hε, ?_⟩
    intro t ht htε x hx htilt
    by_contra hbad
    have hxB : x ∈ B := ⟨hx, le_of_not_gt hbad⟩
    have hfx : f y ≤ f x := hmin hxB
    have hqM : q x ≤ M := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hbound (q x) ⟨x, hx, rfl⟩)
    have htq : t * q x ≤ t * M := mul_le_mul_of_nonneg_left hqM ht
    have htm : t * M ≤ ε * M := mul_le_mul_of_nonneg_right htε hM.le
    nlinarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht htε x hx htilt
    by_contra hbad
    exact hne ⟨x, hx, le_of_not_gt hbad⟩

/-- If a perturbation points strictly below zero on all boundary contact
points, sufficiently small positive tilts have no boundary points. -/
theorem exists_pos_tilt_sublevel_subset_interior
    {K : Set (Space n)} (hK : IsCompact K) {f q : Space n → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hfnn : ∀ x ∈ K, 0 ≤ f x)
    (hzero : ∀ x ∈ frontier K, f x = 0 → q x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t ≤ ε →
      {x ∈ K | f x - t * q x ≤ 0} ⊆ interior K := by
  have hfront : frontier K ⊆ K := by
    simpa only [hK.isClosed.closure_eq] using (frontier_subset_closure (s := K))
  have hfrontCompact : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier hfront
  obtain ⟨ε, hε, hcap⟩ := exists_pos_tilt_sublevel_in_cap hfrontCompact hf hq hq
    (fun x hx => hfnn x (hfront hx)) hzero
  refine ⟨ε, hε, ?_⟩
  intro t ht htε x hx
  apply (mem_interior_iff_notMem_frontier hx.1).mpr
  intro hxf
  have hqneg := hcap t ht.le htε x hxf hx.2
  have hprod := mul_neg_of_pos_of_neg ht hqneg
  have hnonneg := hfnn x hx.1
  linarith [hx.2]

/-- A continuous function strictly negative on a compact set remains
strictly negative after adding one fixed positive constant. -/
theorem exists_pos_add_lt_zero_on_compact
    {K : Set (Space n)} (hK : IsCompact K) {g : Space n → ℝ}
    (hg : Continuous g) (hneg : ∀ x ∈ K, g x < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, g x + c < 0 := by
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hg.continuousOn
    refine ⟨-g y / 2, by linarith [hneg y hy], ?_⟩
    intro x hx
    have hxy : g x ≤ g y := hmax hx
    linarith [hxy, hneg y hy]
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

def supportGap (u : Space n → ℝ) (x p y : Space n) : ℝ :=
  u y - u x - inner ℝ p (y - x)

def contactTilt (u : Space n → ℝ) (x p z v : Space n) (c t : ℝ)
    (y : Space n) : ℝ :=
  supportGap u x p y - t * (inner ℝ v (y - z) + c)

def contactTiltSection (u : Space n → ℝ) (x p z v : Space n) (R c t : ℝ) :
    Set (Space n) :=
  {y | u y ≤ R ∧ contactTilt u x p z v c t y ≤ 0}

theorem continuous_supportGap {u : Space n → ℝ} (hu : Continuous u) (x p : Space n) :
    Continuous (supportGap u x p) := by
  unfold supportGap
  fun_prop

theorem supportGap_nonneg {u : Space n → ℝ} {x p : Space n}
    (hp : p ∈ convexSubgradient u x) (y : Space n) : 0 ≤ supportGap u x p y := by
  have h := hp y
  dsimp [supportGap]
  linarith

theorem supportGap_eq_zero_iff {u : Space n → ℝ} {x p y : Space n} :
    supportGap u x p y = 0 ↔ y ∈ supportContactSet u x p := by
  change u y - u x - inner ℝ p (y - x) = 0 ↔ u y = u x + inner ℝ p (y - x)
  constructor <;> intro h <;> linarith

theorem continuous_contactTilt {u : Space n → ℝ} (hu : Continuous u)
    (x p z v : Space n) (c t : ℝ) : Continuous (contactTilt u x p z v c t) := by
  unfold contactTilt
  exact (continuous_supportGap hu x p).sub
    (continuous_const.mul ((continuous_const.inner (continuous_id.sub continuous_const)).add
      continuous_const))

theorem convexOn_contactTilt {u : Space n → ℝ} (hc : ConvexOn ℝ univ u)
    (x p z v : Space n) (c t : ℝ) : ConvexOn ℝ univ (contactTilt u x p z v c t) := by
  have heq : contactTilt u x p z v c t = fun y =>
      tiltedPotential u (p + t • v) y + (-u x + inner ℝ p x + t * inner ℝ v z - t * c) := by
    funext y
    simp only [contactTilt, supportGap, tiltedPotential, inner_sub_right, inner_add_left,
      real_inner_smul_left]
    ring
  rw [heq]
  exact (convexOn_tiltedPotential hc (p + t • v)).add_const _

theorem contactTilt_at_contact {u : Space n → ℝ} {x p z : Space n}
    (hz : z ∈ supportContactSet u x p) (v : Space n) (c t : ℝ) :
    contactTilt u x p z v c t z = -t * c := by
  rw [contactTilt, supportGap_eq_zero_iff.mpr hz]
  simp

/-- The strictly exposed point produced from the coercive potential admits
an actual positive affine tilt whose small sublevels avoid the old boundary. -/
theorem exists_exposed_contact_tilt_inside
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    [IsFiniteMeasure (potentialMeasure u)] {x p : Space n}
    (hp : p ∈ convexSubgradient u x) {R : ℝ} (hR : u x < R) :
    ∃ z v : Space n, ∃ c ε : ℝ,
      z ∈ supportContactSet u x p ∧ u z < R ∧ 0 < c ∧ 0 < ε ∧
      (∀ y ∈ supportContactSet u x p, u y ≤ R → y ≠ z → inner ℝ v (y - z) < 0) ∧
      ∀ t : ℝ, 0 < t → t ≤ ε →
        contactTiltSection u x p z v R c t ⊆ interior {y | u y ≤ R} := by
  obtain ⟨z, v, hz, hzu, hexposed⟩ := exists_strict_exposed_contact_in_sublevel hu hc hp hR
  let K : Set (Space n) := {y | u y ≤ R}
  have hK : IsCompact K := isCompact_sublevel_of_finite_potentialMeasure hu hc R
  have hzint : z ∈ interior K := lt_subset_interior_le hu continuous_const hzu
  have hfront : frontier K ⊆ K := by
    simpa only [hK.isClosed.closure_eq] using (frontier_subset_closure (s := K))
  let C : Set (Space n) := frontier K ∩ supportContactSet u x p
  have hC : IsCompact C := hK.of_isClosed_subset
    (isClosed_frontier.inter (isClosed_supportContactSet hu x p))
    (inter_subset_left.trans hfront)
  have hg : Continuous (fun y : Space n => inner ℝ v (y - z)) := by fun_prop
  have hneg : ∀ y ∈ C, inner ℝ v (y - z) < 0 := by
    intro y hy
    apply hexposed y hy.2 (hfront hy.1)
    intro hyz
    subst y
    exact (mem_interior_iff_notMem_frontier (interior_subset hzint)).mp hzint hy.1
  obtain ⟨c, hcpos, hcneg⟩ := exists_pos_add_lt_zero_on_compact hC hg hneg
  have hq : Continuous (fun y : Space n => inner ℝ v (y - z) + c) := hg.add continuous_const
  have hboundary : ∀ y ∈ frontier K, supportGap u x p y = 0 →
      inner ℝ v (y - z) + c < 0 := by
    intro y hy hyzero
    exact hcneg y ⟨hy, supportGap_eq_zero_iff.mp hyzero⟩
  obtain ⟨ε, hε, hinside⟩ := exists_pos_tilt_sublevel_subset_interior hK
    (continuous_supportGap hu x p) hq (fun y _ => supportGap_nonneg hp y) hboundary
  exact ⟨z, v, c, ε, hz, hzu, hcpos, hε, hexposed, hinside⟩

/-- The actual tilted sections lie in arbitrarily thin upper caps of the
supporting functional as the positive tilt parameter tends to zero. -/
theorem contactTiltSection_cap_localization
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    [IsFiniteMeasure (potentialMeasure u)] {x p z v : Space n}
    (hp : p ∈ convexSubgradient u x) {R c : ℝ}
    (hexposed : ∀ y ∈ supportContactSet u x p, u y ≤ R → y ≠ z →
      inner ℝ v (y - z) < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      ∀ y ∈ contactTiltSection u x p z v R c t, inner ℝ v (y - z) < δ := by
  have hg : Continuous (fun y : Space n => inner ℝ v (y - z)) := by fun_prop
  obtain ⟨ε, hε, hcap⟩ := exists_pos_tilt_sublevel_in_cap
    (isCompact_sublevel_of_finite_potentialMeasure hu hc R)
    (continuous_supportGap hu x p) (hg.add continuous_const) hg
    (fun y _ => supportGap_nonneg hp y) (δ := δ) (by
      intro y hy hzero
      by_cases hyz : y = z
      · subst y
        simpa using hδ
      · exact (hexposed y (supportGap_eq_zero_iff.mp hzero) hy hyz).trans hδ)
  exact ⟨ε, hε, fun t ht htε y hy => hcap t ht htε y hy.1 hy.2⟩

/-- The confined tilted section is a genuine compact convex section with
nonempty interior and zero boundary values for its actual tilted potential. -/
theorem contactTiltSection_geometry
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    [IsFiniteMeasure (potentialMeasure u)] {x p z v : Space n} {R c t : ℝ}
    (hz : z ∈ supportContactSet u x p) (hzu : u z < R)
    (hcpos : 0 < c) (ht : 0 < t)
    (hinside : contactTiltSection u x p z v R c t ⊆ interior {y | u y ≤ R}) :
    IsCompact (contactTiltSection u x p z v R c t) ∧
      Convex ℝ (contactTiltSection u x p z v R c t) ∧
      z ∈ interior (contactTiltSection u x p z v R c t) ∧
      ∀ y ∈ frontier (contactTiltSection u x p z v R c t),
        contactTilt u x p z v c t y = 0 := by
  let K : Set (Space n) := {y | u y ≤ R}
  let S : Set (Space n) := contactTiltSection u x p z v R c t
  let f : Space n → ℝ := contactTilt u x p z v c t
  have hK : IsCompact K := isCompact_sublevel_of_finite_potentialMeasure hu hc R
  have hf : Continuous f := continuous_contactTilt hu x p z v c t
  have hS : IsCompact S := hK.inter_right (isClosed_le hf continuous_const)
  have hcK : Convex ℝ K := by
    simpa only [mem_univ, true_and] using hc.convex_le R
  have hcf : Convex ℝ {y | f y ≤ 0} := by
    simpa only [mem_univ, true_and] using (convexOn_contactTilt hc x p z v c t).convex_le 0
  have hzK : z ∈ interior K := lt_subset_interior_le hu continuous_const hzu
  have hfz : f z < 0 := by
    rw [show f z = -t * c from contactTilt_at_contact hz v c t]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hcpos
  have hzS : z ∈ interior S := by
    change z ∈ interior (K ∩ {y | f y ≤ 0})
    rw [interior_inter]
    exact ⟨hzK, lt_subset_interior_le hf continuous_const hfz⟩
  refine ⟨hS, hcK.inter hcf, hzS, ?_⟩
  intro y hy
  have hyS : y ∈ S := by
    exact hS.isClosed.closure_subset (frontier_subset_closure hy)
  have hyint : y ∈ interior K := hinside hyS
  have hynotfront : y ∉ frontier K :=
    (mem_interior_iff_notMem_frontier (interior_subset hyint)).mp hyint
  have hfr := frontier_inter_subset K {y | f y ≤ 0} hy
  rcases hfr with hleft | hright
  · exact False.elim (hynotfront hleft.1)
  · exact frontier_le_subset_eq hf continuous_const hright.2

/-- The cap estimate gives a matching oscillation bound; at the exposed
contact point the depth is exactly `t*c`, so the depth ratio stays positive. -/
theorem contactTiltSection_oscillation
    {u : Space n → ℝ} {x p z v : Space n} {R c t δ : ℝ}
    (hp : p ∈ convexSubgradient u x) (ht : 0 ≤ t)
    (hcap : ∀ y ∈ contactTiltSection u x p z v R c t, inner ℝ v (y - z) ≤ δ) :
    ∀ y ∈ contactTiltSection u x p z v R c t,
      -(t * (c + δ)) ≤ contactTilt u x p z v c t y ∧
        contactTilt u x p z v c t y ≤ 0 := by
  intro y hy
  refine ⟨?_, hy.2⟩
  have hf := supportGap_nonneg hp y
  have hmul := mul_le_mul_of_nonneg_left (hcap y hy) ht
  dsimp [contactTilt]
  nlinarith

end KLS
end

#print axioms KLS.exists_pos_tilt_sublevel_in_cap
#print axioms KLS.exists_pos_tilt_sublevel_subset_interior
#print axioms KLS.exists_pos_add_lt_zero_on_compact
#print axioms KLS.exists_exposed_contact_tilt_inside
#print axioms KLS.contactTiltSection_cap_localization
#print axioms KLS.contactTiltSection_geometry
#print axioms KLS.contactTiltSection_oscillation
