import KLS.ContactSetSingleton

/-! Strict convexity of the actual weak moment potential, obtained from
singleton support contacts and the already constructed support planes. -/

open MeasureTheory InnerProductSpace Set
open scoped NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- A continuous convex function with singleton support contacts is strictly
convex. Support planes at convex combinations are constructed by separation. -/
theorem strictConvexOn_of_supportContactSet_subsingleton
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    (hcontact : ∀ x p : Space n, p ∈ convexSubgradient u x →
      (supportContactSet u x p).Subsingleton) :
    StrictConvexOn ℝ univ u := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let z : Space n := a • x + b • y
  have hconv : u z ≤ a * u x + b * u y := hc.2 hx hy ha.le hb.le hab
  apply lt_of_le_of_ne hconv
  intro heq
  obtain ⟨p, hp⟩ := convexSubgradient_nonempty hu hc z
  have hpx := hp x
  have hpy := hp y
  have hpz : inner ℝ p z = a * inner ℝ p x + b * inner ℝ p y := by
    simp only [z, inner_add_right, real_inner_smul_right]
  have hip : a * inner ℝ p (x - z) + b * inner ℝ p (y - z) = 0 := by
    simp only [inner_sub_right]
    nlinarith [congrArg (fun r : ℝ => r * inner ℝ p z) hab]
  have hsum : a * (u x - u z - inner ℝ p (x - z)) +
      b * (u y - u z - inner ℝ p (y - z)) = 0 := by
    nlinarith [congrArg (fun r : ℝ => r * u z) hab]
  have hnonnegx : 0 ≤ u x - u z - inner ℝ p (x - z) := by linarith
  have hnonnegy : 0 ≤ u y - u z - inner ℝ p (y - z) := by linarith
  have hxcontact : x ∈ supportContactSet u z p := by
    change u x = u z + inner ℝ p (x - z)
    nlinarith [mul_nonneg hb.le hnonnegy]
  have hycontact : y ∈ supportContactSet u z p := by
    change u y = u z + inner ℝ p (y - z)
    nlinarith [mul_nonneg ha.le hnonnegx]
  exact hxy (hcontact z p hp hxcontact hycontact)

/-- The weak moment identity, local density bounds, and actual tilted-section
geometry imply strict convexity of the source potential. -/
theorem moment_strictConvexOn
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure φ)]
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K) :
    StrictConvexOn ℝ univ φ :=
  strictConvexOn_of_supportContactSet_subsingleton hLip.continuous hc
    (fun _ _ hp => moment_supportContactSet_subsingleton hLip hc hV hK hKc hpush hp)

end KLS
end

#print axioms KLS.strictConvexOn_of_supportContactSet_subsingleton
#print axioms KLS.moment_strictConvexOn
