import KLS.WeightedEnergyGraph

/-!
# The actual smooth centered gradient core is linear

Every sum and scalar multiple of genuine smooth centered-gradient pairs is
again the pair of an explicit compact C³ function. Compact-support weighted
integrability justifies linearity of the mean. Thus the span used in the
closed graph definition is exactly the original smooth core.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

lemma zero_mem_smoothCenteredGradientGraphSet (φ : Space n → ℝ) :
    (0 : WeightedEnergyAmbient φ) ∈ smoothCenteredGradientGraphSet φ := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
    change (0 : Lp ℝ 2 (potentialMeasure φ)) x = _
    rw [hx]
    simp
  · intro i
    filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
    change (0 : Lp ℝ 2 (potentialMeasure φ)) x = coordinateDerivative (0 : Space n → ℝ) i x
    rw [hx]
    simp [coordinateDerivative]

lemma add_mem_smoothCenteredGradientGraphSet {φ : Space n → ℝ} (hφ : Continuous φ)
    {U V : WeightedEnergyAmbient φ}
    (hU : U ∈ smoothCenteredGradientGraphSet φ) (hV : V ∈ smoothCenteredGradientGraphSet φ) :
    U + V ∈ smoothCenteredGradientGraphSet φ := by
  obtain ⟨f, hf, hfc, hu, hud⟩ := hU
  obtain ⟨g, hg, hgc, hv, hvd⟩ := hV
  have hfI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hf.continuous hfc
  have hgI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hg.continuous hgc
  refine ⟨f + g, hf.add hg, hfc.add hgc, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (U 0) (V 0), hu, hv] with x hx hux hvx
    change (U 0 + V 0) x = _
    rw [hx]
    simp only [Pi.add_apply]
    rw [hux, hvx, integral_add hfI hgI]
    ring
  · intro i
    filter_upwards [Lp.coeFn_add (U i.succ) (V i.succ), hud i, hvd i] with x hx hux hvx
    change (U i.succ + V i.succ) x = _
    rw [hx]
    simp only [Pi.add_apply]
    rw [hux, hvx, coordinateDerivative_add
      (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]

lemma smul_mem_smoothCenteredGradientGraphSet {φ : Space n → ℝ}
    {U : WeightedEnergyAmbient φ} (c : ℝ) (hU : U ∈ smoothCenteredGradientGraphSet φ) :
    c • U ∈ smoothCenteredGradientGraphSet φ := by
  obtain ⟨f, hf, hfc, hu, hud⟩ := hU
  refine ⟨c • f, hf.const_smul c, hfc.smul_left, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c (U 0), hu] with x hx hux
    change (c • U 0) x = _
    rw [hx]
    simp only [Pi.smul_apply]
    rw [hux, integral_smul]
    simp only [smul_eq_mul]
    ring
  · intro i
    filter_upwards [Lp.coeFn_smul c (U i.succ), hud i] with x hx hux
    change (c • U i.succ) x = _
    rw [hx]
    simp only [Pi.smul_apply]
    rw [hux, coordinateDerivative_smul (hf.differentiable (by norm_num) x)]
    rfl

/-- The genuine compact C³ centered-gradient pairs form a linear submodule. -/
def smoothCenteredGradientCore {φ : Space n → ℝ} (hφ : Continuous φ) :
    Submodule ℝ (WeightedEnergyAmbient φ) where
  carrier := smoothCenteredGradientGraphSet φ
  zero_mem' := zero_mem_smoothCenteredGradientGraphSet φ
  add_mem' := add_mem_smoothCenteredGradientGraphSet hφ
  smul_mem' := fun c _ hU => smul_mem_smoothCenteredGradientGraphSet c hU

@[simp] theorem mem_smoothCenteredGradientCore {φ : Space n → ℝ} (hφ : Continuous φ)
    (U : WeightedEnergyAmbient φ) :
    U ∈ smoothCenteredGradientCore hφ ↔ U ∈ smoothCenteredGradientGraphSet φ := Iff.rfl

/-- Taking the span adds no elements: every element is itself an actual smooth gradient pair. -/
theorem span_smoothCenteredGradientGraphSet {φ : Space n → ℝ} (hφ : Continuous φ) :
    Submodule.span ℝ (smoothCenteredGradientGraphSet φ) = smoothCenteredGradientCore hφ := by
  change Submodule.span ℝ (smoothCenteredGradientCore hφ : Set (WeightedEnergyAmbient φ)) = _
  exact Submodule.span_eq _

/-- The complete energy graph is the closure of the genuine smooth core. -/
theorem weightedCenteredGradientGraph_eq_core_closure {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    weightedCenteredGradientGraph φ = (smoothCenteredGradientCore hφ).topologicalClosure := by
  rw [weightedCenteredGradientGraph, span_smoothCenteredGradientGraphSet hφ]

/-- In particular, a function-pair inequality need only be extended from this actual set's closure. -/
theorem weightedCenteredGradientGraph_coe_eq_closure {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    (weightedCenteredGradientGraph φ : Set (WeightedEnergyAmbient φ)) =
      closure (smoothCenteredGradientGraphSet φ) := by
  rw [weightedCenteredGradientGraph_eq_core_closure hφ]
  rfl

end KLS
end

#print axioms KLS.smoothCenteredGradientCore
#print axioms KLS.span_smoothCenteredGradientGraphSet
#print axioms KLS.weightedCenteredGradientGraph_coe_eq_closure
