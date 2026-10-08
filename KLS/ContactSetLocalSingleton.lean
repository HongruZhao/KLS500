import KLS.ContactSetSingleton

/-!
# Local singleton contacts on one controlled sublevel

The exposed-section argument needs Alexandrov bounds on only one sublevel.
This local interface is intended for truncated conjugates, whose controlled
region agrees with the actual relative conjugate. No bounds outside that
sublevel and no contact uniqueness are assumed.
-/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Actual positive finite density bounds on one closed sublevel rule out
multiple support contacts inside that sublevel. -/
theorem supportContactSet_sublevel_subsingleton_of_subgradient_bounds
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    [IsFiniteMeasure (potentialMeasure u)]
    {R : ℝ} {a b : ℝ≥0∞} (ha : 0 < a) (hatop : a < ∞)
    (hb : 0 < b) (hbtop : b < ∞)
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ {y | u y ≤ R} →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ {y | u y ≤ R} →
      volume (convexSubgradientImage u S) ≤ b * volume S)
    {x p : Space n} (hp : p ∈ convexSubgradient u x) (hxR : u x < R) :
    (supportContactSet u x p ∩ {y | u y ≤ R}).Subsingleton := by
  intro x₁ hx₁ x₂ hx₂
  rcases hx₁ with ⟨hx₁, hx₁R⟩
  rcases hx₂ with ⟨hx₂, hx₂R⟩
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.elim _ _
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  by_contra hneq
  obtain ⟨z, v, c, ε₀, hz, hzu, hcpos, hε₀, hexposed, hinside⟩ :=
    exists_exposed_contact_tilt_inside hu hc hp hxR
  obtain ⟨w, hw, hwu, hwz⟩ : ∃ w : Space n,
      w ∈ supportContactSet u x p ∧ u w ≤ R ∧ w ≠ z := by
    by_cases h₁ : x₁ = z
    · refine ⟨x₂, hx₂, hx₂R, ?_⟩
      intro h₂
      exact hneq (h₁.trans h₂.symm)
    · exact ⟨x₁, hx₁, hx₁R, h₁⟩
  obtain ⟨y, d, hd, hdc, hsep, hretained⟩ :=
    exists_retained_contact_segment hc hp hz hzu.le hw hwu (hexposed w hw hwu hwz) hcpos
  let η : ℝ := normalizedSectionWidthConstant n a b (1 / 2)
  have hη : 0 < η := normalizedSectionWidthConstant_pos hnpos ha hatop hb hbtop (by norm_num)
  let Rn : ℝ := 2 * ((n : ℝ) + 1) ^ 3
  have hRn : 0 < Rn := by dsimp [Rn]; positivity
  let δ : ℝ := min (c / 2) (η * d / (4 * Rn))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδc : δ ≤ c := (min_le_left _ _).trans (by linarith)
  have hδsmall : (2 * Rn / d) * δ < η := by
    have hh : δ * (4 * Rn) ≤ η * d :=
      (le_div_iff₀ (by positivity : 0 < 4 * Rn)).mp (min_le_right _ _)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos hη hd]
  obtain ⟨ε₁, hε₁, hcap⟩ := contactTiltSection_cap_localization hu hc hp hexposed hδ
  let t : ℝ := min ε₀ ε₁ / 2
  have ht : 0 < t := div_pos (lt_min hε₀ hε₁) zero_lt_two
  have ht₀ : t ≤ ε₀ := by
    have hmin := min_le_left ε₀ ε₁
    dsimp [t]
    linarith [lt_min hε₀ hε₁]
  have ht₁ : t ≤ ε₁ := by
    have hmin := min_le_right ε₀ ε₁
    dsimp [t]
    linarith [lt_min hε₀ hε₁]
  let S : Set (Space n) := contactTiltSection u x p z v R c t
  let f : Space n → ℝ := contactTilt u x p z v c t
  have hScap : ∀ w ∈ S, inner ℝ v (w - z) ≤ δ :=
    fun w hw => (hcap t ht.le ht₁ w hw).le
  obtain ⟨hScompact, hSconvex, hzint, hboundary⟩ :=
    contactTiltSection_geometry hu hc hz hzu hcpos ht (hinside t ht ht₀)
  have hosc : ∀ w ∈ S, -(t * (c + δ)) ≤ f w ∧ f w ≤ 0 :=
    contactTiltSection_oscillation hp ht.le hScap
  obtain ⟨hlowerS, hupperS⟩ :=
    contactTiltSection_subgradient_volume_bounds (x := x) (p := p) (z := z) (v := v)
      (c := c) (t := t) hlower hupper
  obtain ⟨e, heinner, heouter, hewidth⟩ :=
    exists_normalization_with_positive_directional_width hnpos ha hatop hb hbtop
      (θ := (1 / 2 : ℝ)) (by norm_num) hScompact hSconvex ⟨z, hzint⟩
      (continuous_contactTilt hu x p z v c t) (convexOn_contactTilt hc x p z v c t)
      (fun w hw => (hboundary w hw).ge) (mul_pos ht (add_pos hcpos hδ))
      hosc hlowerS hupperS
  have hzS : z ∈ S := interior_subset hzint
  obtain ⟨v', hv', hcap'⟩ := exists_normalized_cap_from_retained_width e
    (hretained t ht.le) hzS hd hδ hsep heouter hScap
  have hdepth : (1 / 2 : ℝ) * (t * (c + δ)) ≤ -f (e.symm (e z)) := by
    rw [e.symm_apply_apply, show f z = -t * c from contactTilt_at_contact hz v c t]
    nlinarith [mul_le_mul_of_nonneg_left hδc ht.le]
  have hwidth := hewidth (e z) v' ((2 * Rn / d) * δ) ⟨z, hzS, rfl⟩ hdepth hv'
    (by positivity) hcap'
  exact (not_le_of_gt hδsmall) hwidth

/-- The sigma-compact mass-equation interface supplies the compact lower
and open upper hypotheses of the preceding local geometric theorem. -/
theorem supportContactSet_sublevel_subsingleton_of_sigmaCompact_bounds
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    [IsFiniteMeasure (potentialMeasure u)]
    {R : ℝ} {a b : ℝ≥0∞} (ha : 0 < a) (hatop : a < ∞)
    (hb : 0 < b) (hbtop : b < ∞)
    (hbounds : ∀ S : Set (Space n), IsSigmaCompact S → S ⊆ {y | u y ≤ R} →
      a * volume S ≤ volume (convexSubgradientImage u S) ∧
      volume (convexSubgradientImage u S) ≤ b * volume S)
    {x p : Space n} (hp : p ∈ convexSubgradient u x) (hxR : u x < R) :
    (supportContactSet u x p ∩ {y | u y ≤ R}).Subsingleton :=
  supportContactSet_sublevel_subsingleton_of_subgradient_bounds hu hc ha hatop hb hbtop
    (fun S hS hSR => (hbounds S hS.isSigmaCompact hSR).1)
    (fun S hS hSR => (hbounds S (isSigmaCompact_of_isOpen_space hS) hSR).2) hp hxR

end KLS
end

#print axioms KLS.supportContactSet_sublevel_subsingleton_of_subgradient_bounds
#print axioms KLS.supportContactSet_sublevel_subsingleton_of_sigmaCompact_bounds
