import KLS.SubgradientComparison

/-!
# Polar and anisotropic Alexandrov estimates

Every slope strictly below the boundary support threshold occurs at an
interior contact point. Rectangular subsets of this polar region yield
explicit volume bounds, including a narrow supporting-direction parameter.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

noncomputable section
namespace KLS

/-- A support plane with a strict boundary gap touches the convex function
at an interior point after lowering. -/
theorem exists_interior_subgradient_of_boundary_gap
    {n : ℕ} {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    {x p : Space n} (hx : x ∈ K)
    (hgap : ∀ z ∈ frontier K, u x + inner ℝ p (z - x) < u z) :
    ∃ z ∈ interior K, p ∈ convexSubgradient u z := by
  let F : Space n → ℝ := fun z => u z - inner ℝ p z
  obtain ⟨z, hzK, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩
    ((hucont.sub (continuous_const.inner continuous_id)).continuousOn)
  have hzint : z ∈ interior K := by
    by_contra hznot
    have hzgap := hgap z ((mem_frontier_iff_notMem_interior hzK).mpr hznot)
    have hzle := hmin hx
    rw [inner_sub_right] at hzgap
    change u z - inner ℝ p z ≤ u x - inner ℝ p x at hzle
    linarith
  have hFconvex : ConvexOn ℝ Set.univ F :=
    huconvex.sub ((innerSL ℝ p).toLinearMap.concaveOn convex_univ)
  have hglobal := IsMinOn.of_isLocalMin_of_convex_univ
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hzint)) hFconvex
  refine ⟨z, hzint, ?_⟩
  intro y
  have hh := hglobal y
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at hh
  rw [inner_sub_right]
  linarith

/-- The actual strict polar body at a negative point is contained in the
subgradient image, without smoothness of the function or domain. -/
theorem strictPolar_subset_convexSubgradientImage
    {n : ℕ} {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : Space n} (hx : x ∈ K) :
    {p : Space n | ∀ z ∈ frontier K, inner ℝ p (z - x) < -u x} ⊆
      convexSubgradientImage u (interior K) := by
  intro p hp
  obtain ⟨z, hz, hzp⟩ := exists_interior_subgradient_of_boundary_gap hK hucont huconvex hx
    (fun z hz => by linarith [hp z hz, hboundary z hz])
  exact ⟨z, hz, hzp⟩

/-- Coordinate rectangles have their actual product Lebesgue volume in the
Euclidean-space model used throughout this development. -/
theorem volume_euclidean_coordinate_box {n : ℕ} (a b : Fin n → ℝ) :
    volume {p : Space n | ∀ i, p i ∈ Set.Ioo (a i) (b i)} =
      ∏ i : Fin n, ENNReal.ofReal (b i - a i) := by
  have hmeas : MeasurableSet {p : Space n | ∀ i, p i ∈ Set.Ioo (a i) (b i)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).measurable measurableSet_Ioo
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hmeas.nullMeasurableSet]
  change volume {p : Fin n → ℝ | ∀ i, p i ∈ Set.Ioo (a i) (b i)} = _
  have hset : {p : Fin n → ℝ | ∀ i, p i ∈ Set.Ioo (a i) (b i)} =
      Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  rw [hset]
  exact Real.volume_pi_Ioo

/-- A rectangular family of slopes below every boundary threshold yields an
explicit Alexandrov lower bound by the product of its side lengths. -/
theorem coordinate_box_volume_le_convexSubgradientImage
    {n : ℕ} {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : Space n} (hx : x ∈ K)
    (a b : Fin n → ℝ)
    (hpolar : ∀ p : Space n, (∀ i, p i ∈ Set.Ioo (a i) (b i)) →
      ∀ z ∈ frontier K, inner ℝ p (z - x) < -u x) :
    (∏ i : Fin n, ENNReal.ofReal (b i - a i)) ≤
      volume (convexSubgradientImage u (interior K)) := by
  rw [← volume_euclidean_coordinate_box]
  apply measure_mono
  exact fun p hp => strictPolar_subset_convexSubgradientImage hK hucont huconvex hboundary hx (hpolar p hp)

/-- An anisotropic rectangle of slopes fits below the polar threshold when
one supporting direction has width δ and the transverse directions have width R. -/
theorem inner_lt_of_anisotropic_coordinate_box
    {n : ℕ} (i : Fin n) {m δ R : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hR : 0 < R)
    {p z : Space n} (hp0 : 0 ≤ p i) (hpi : p i < m / (2 * δ))
    (hp : ∀ j, j ≠ i → |p j| < m / (2 * n * R))
    (hzi : z i ≤ δ) (hz : ∀ j, j ≠ i → |z j| ≤ R) : inner ℝ p z < m := by
  have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hfirst : p i * z i < m / 2 := by
    have hmul := (lt_div_iff₀ (show 0 < 2 * δ by positivity)).mp hpi
    have hle := mul_le_mul_of_nonneg_left hzi hp0
    nlinarith
  have hcancel : m / (2 * (n : ℝ) * R) * R = m / (2 * n) := by field_simp
  have hterm (j : Fin n) : (if j = i then 0 else p j * z j) ≤ m / (2 * n) := by
    by_cases hji : j = i
    · simp only [ite_eq_left hji]
      positivity
    · simp only [ite_eq_right hji]
      have hmul := mul_lt_mul_of_pos_right (hp j hji) hR
      rw [hcancel] at hmul
      exact ((le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hz j hji) (abs_nonneg _))).trans hmul.le
  have hsum : (∑ j : Fin n, if j = i then 0 else p j * z j) ≤ m / 2 := by
    calc
      _ ≤ ∑ _j : Fin n, m / (2 * n) := Finset.sum_le_sum fun j _ => hterm j
      _ = (n : ℝ) * (m / (2 * n)) := by simp
      _ = m / 2 := by field_simp
  have hinner : inner ℝ p z = ∑ j : Fin n, p j * z j := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hsplit : (∑ j : Fin n, p j * z j) =
      p i * z i + ∑ j : Fin n, if j = i then 0 else p j * z j := by
    calc
      _ = ∑ j : Fin n, ((if j = i then p i * z i else 0) +
          (if j = i then 0 else p j * z j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i <;> simp [hji]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hinner, hsplit]
  linarith

/-- An explicit anisotropic Alexandrov lower bound. Its side-length product
contains one factor proportional to 1/δ and n−1 transverse factors proportional
to 1/R. The narrow-direction and transverse hypotheses are proved geometric
bounds on K, not a regularity certificate. -/
theorem anisotropic_box_volume_le_convexSubgradientImage
    {n : ℕ} (i : Fin n) {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : Space n} (hx : x ∈ K)
    (hux : u x < 0) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hwidth : ∀ z ∈ K, z i - x i ≤ δ)
    (htransverse : ∀ z ∈ K, ∀ j, j ≠ i → |z j - x j| ≤ R) :
    (∏ j : Fin n, ENNReal.ofReal
      ((if j = i then -u x / (2 * δ) else -u x / (2 * n * R)) -
       (if j = i then 0 else -(-u x / (2 * n * R))))) ≤
      volume (convexSubgradientImage u (interior K)) := by
  apply coordinate_box_volume_le_convexSubgradientImage hK hucont huconvex hboundary hx
  intro p hp z hz
  have hzK : z ∈ K := hK.isClosed.closure_eq ▸ frontier_subset_closure hz
  have hpi := hp i
  simp only [Set.mem_Ioo] at hpi
  apply inner_lt_of_anisotropic_coordinate_box i (neg_pos.mpr hux) hδ hR hpi.1.le hpi.2
  · intro j hji
    have hpj := hp j
    simpa only [ite_eq_right hji, Set.mem_Ioo, ← abs_lt] using hpj
  · exact hwidth z hzK
  · exact htransverse z hzK

/-- Closed-form anisotropic maximum estimate. The small distance δ appears in
the denominator, which is the boundary sensitivity absent from the ball bound. -/
theorem anisotropic_alexandrov_maximum_estimate
    {n : ℕ} (i : Fin n) {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z) {x : Space n} (hx : x ∈ K)
    (hux : u x < 0) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hwidth : ∀ z ∈ K, z i - x i ≤ δ)
    (htransverse : ∀ z ∈ K, ∀ j, j ≠ i → |z j - x j| ≤ R) :
    ENNReal.ofReal (-u x / (2 * δ)) *
      ENNReal.ofReal (-u x / (n * R)) ^ (n - 1) ≤
        volume (convexSubgradientImage u (interior K)) := by
  have hbound := anisotropic_box_volume_le_convexSubgradientImage i hK hucont huconvex
    hboundary hx hux hδ hR hwidth htransverse
  let F : Fin n → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((if j = i then -u x / (2 * δ) else -u x / (2 * n * R)) -
     (if j = i then 0 else -(-u x / (2 * n * R))))
  have hprod : (∏ j : Fin n, F j) = ENNReal.ofReal (-u x / (2 * δ)) *
      ENNReal.ofReal (-u x / (n * R)) ^ (n - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i)]
    have hrest : (∏ j ∈ Finset.univ.erase i, F j) =
        ENNReal.ofReal (-u x / (n * R)) ^ (n - 1) := by
      calc
        _ = ∏ _j ∈ Finset.univ.erase i, ENNReal.ofReal (-u x / (n * R)) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hji := (Finset.mem_erase.mp hj).1
          simp only [F, ite_eq_right hji]
          congr 1
          ring
        _ = _ := by simp
    rw [hrest]
    simp [F]
  change (∏ j : Fin n, F j) ≤ _ at hbound
  rwa [hprod] at hbound

end KLS
end

#print axioms KLS.strictPolar_subset_convexSubgradientImage
#print axioms KLS.volume_euclidean_coordinate_box
#print axioms KLS.coordinate_box_volume_le_convexSubgradientImage

#print axioms KLS.anisotropic_box_volume_le_convexSubgradientImage

#print axioms KLS.anisotropic_alexandrov_maximum_estimate
