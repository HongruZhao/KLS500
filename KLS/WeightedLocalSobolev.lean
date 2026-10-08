import KLS.LocalizedGradientBound
import KLS.WeakGradientExtraction

/-!
# Actual weak derivatives of compact localizations of weighted annihilators

The mollified equation, uniform local gradient bounds, and genuine weak-limit
extraction produce L² weak derivatives. A proved weak product rule transfers
these derivatives from u exp(-φ) back to the original function u. No Sobolev
membership or weak regularity is assumed of the weighted L² annihilator.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

/-- An actual L² coordinate derivative, defined by integration against all compact C¹ tests. -/
def HasWeakCoordinateDerivative (f : Space n → ℝ) (i : Fin n)
    (g : Lp ℝ 2 (volume : Measure (Space n))) : Prop :=
  ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    (∫ x, f x * coordinateDerivative ψ i x) = -(∫ x, g x * ψ x)

/-- The density-transformed annihilator has actual weak derivatives after every compact cutoff. -/
theorem weighted_annihilator_cutoff_density_hasWeakDerivative {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * densityWeightedFunction φ u x) i g := by
  have hv : ∀ K : Set (Space n), IsCompact K →
      MemLp (densityWeightedFunction φ u) 2 (volume.restrict K) :=
    fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK
  have hloc := locallyIntegrable_of_memLp_two_on_compacts hv
  have hU := memLp_compact_mul_of_local hχ.continuous hc hv
  have hconv := eLpNorm_compact_mul_mollify_sub_tendsto_zero hχ.continuous hc hv
  obtain ⟨M, hM, hb⟩ := weighted_annihilator_localized_derivative_bound hφ u hu hχ hc
  obtain ⟨g, -, hg⟩ := exists_weak_coordinateDerivative_of_approximation
    (f := fun k x => χ x * mollify k (densityWeightedFunction φ u) x)
    (fun k => hχ.mul ((mollify_contDiff hloc k).of_le (by simp)))
    (fun _ => hc.mul_right) hU hconv i hM (fun k => hb k i)
  exact ⟨g, hg⟩

/-- Weak differentiation obeys the actual product rule for a compact C¹ multiplier. -/
theorem HasWeakCoordinateDerivative.compact_mul {f b : Space n → ℝ} {i : Fin n}
    {g : Lp ℝ 2 (volume : Measure (Space n))} (hf : MemLp f 2 volume)
    (hg : HasWeakCoordinateDerivative f i g) (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b) :
    ∃ h : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => b x * f x) i h := by
  have hdb := (contDiff_coordinateDerivative hb (m := 0) (by norm_num) i).continuous
  have hbc := hb.continuous.memLp_top_of_hasCompactSupport hc volume
  have hdbc := hdb.memLp_top_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i) volume
  have hbf : MemLp (fun x => b x * f x) 2 volume := hbc.mul hf
  have hbg : MemLp (fun x => b x * g x) 2 volume := hbc.mul (Lp.memLp g)
  have hdf : MemLp (fun x => coordinateDerivative b i x * f x) 2 volume := hdbc.mul hf
  have hW : MemLp (fun x => b x * g x + coordinateDerivative b i x * f x) 2 volume := hbg.add hdf
  let w : Lp ℝ 2 volume := hW.toLp (fun x => b x * g x + coordinateDerivative b i x * f x)
  refine ⟨w, ?_⟩
  intro ψ hψ hψc
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψ2 : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  have hA : Integrable (fun x => (b x * g x) * ψ x) volume := hbg.integrable_mul hψ2
  have hB : Integrable (fun x => (coordinateDerivative b i x * f x) * ψ x) volume := hdf.integrable_mul hψ2
  have hC : Integrable (fun x => (b x * f x) * coordinateDerivative ψ i x) volume :=
    hbf.integrable_mul hdψ2
  have he := hg (fun x => b x * ψ x) (hb.mul hψ) hc.mul_right
  have hleft : (∫ x, f x * coordinateDerivative (fun y => b y * ψ y) i x) =
      (∫ x, (coordinateDerivative b i x * f x) * ψ x) +
        ∫ x, (b x * f x) * coordinateDerivative ψ i x := by
    rw [← integral_add hB hC]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_mul (hb.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x)]
      ring
  have hright : (∫ x, g x * (b x * ψ x)) = ∫ x, (b x * g x) * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hw : (∫ x, w x * ψ x) = (∫ x, (b x * g x) * ψ x) +
      ∫ x, (coordinateDerivative b i x * f x) * ψ x := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with x hx
    rw [show w x = b x * g x + coordinateDerivative b i x * f x from hx]
    ring
  rw [hleft, hright] at he
  rw [hw]
  linarith

/-- The original weighted L² annihilator has actual weak derivatives after squaring a cutoff.
A cutoff equal to one on a ball therefore supplies local H¹ membership there. -/
theorem weighted_annihilator_compact_square_hasWeakDerivative {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x ^ 2 * u x) i g := by
  obtain ⟨g, hg⟩ := weighted_annihilator_cutoff_density_hasWeakDerivative hφ u hu hχ hc i
  have hloc : ∀ K : Set (Space n), IsCompact K →
      MemLp (densityWeightedFunction φ u) 2 (volume.restrict K) :=
    fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK
  have hf := memLp_compact_mul_of_local hχ.continuous hc hloc
  have hb : ContDiff ℝ 1 (fun x => χ x * Real.exp (φ x)) :=
    hχ.mul (hφ.of_le (by norm_num)).exp
  obtain ⟨G, hG⟩ := hg.compact_mul hf hb hc.mul_right
  have heq : (fun x => (χ x * Real.exp (φ x)) * (χ x * densityWeightedFunction φ u x)) =
      fun x => χ x ^ 2 * u x := by
    funext x
    dsimp [densityWeightedFunction]
    calc
      χ x * Real.exp (φ x) * (χ x * (u x * Real.exp (-φ x))) =
          χ x ^ 2 * u x * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
      _ = χ x ^ 2 * u x := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [heq] at hG
  exact ⟨G, hG⟩

end KLS
end

#print axioms KLS.weighted_annihilator_cutoff_density_hasWeakDerivative
#print axioms KLS.HasWeakCoordinateDerivative.compact_mul
#print axioms KLS.weighted_annihilator_compact_square_hasWeakDerivative
