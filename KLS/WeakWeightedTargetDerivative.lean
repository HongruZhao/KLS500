import KLS.WeakWeightedInverseDerivative

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Differentiating the actual target-gradient drift uses only target C2
 and the actual almost-everywhere derivative of the Lipschitz source gradient. -/
theorem actual_weighted_targetGradient_hasLocalWeakDerivative
    {u V : Space n → ℝ} {G : ℝ≥0}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (k j : Fin n) :
    HasLocalWeakCoordinateDerivative
      (fun x => Real.exp (-u x) * coordinateDerivative V j (gradient u x))
      (fun x => Real.exp (-u x) *
        ((coordinateHessian u x * coordinateHessian V (gradient u x)) k j -
          coordinateDerivative u k x * coordinateDerivative V j (gradient u x))) k ∧
    ∀ S, IsCompact S → MemLp
      (fun x => Real.exp (-u x) *
        ((coordinateHessian u x * coordinateHessian V (gradient u x)) k j -
          coordinateDerivative u k x * coordinateDerivative V j (gradient u x)))
      ∞ (volume.restrict S) := by
  have hVj : ContDiff ℝ 1 (coordinateDerivative V j) :=
    contDiff_coordinateDerivative hV (by norm_num) j
  have hq : LocallyLipschitz (fun x => coordinateDerivative V j (gradient u x)) :=
    hVj.locallyLipschitz.comp hG.locallyLipschitz
  have he : coordinateDerivative (fun x => coordinateDerivative V j (gradient u x)) k =ᵐ[volume]
      (fun x => (coordinateHessian u x * coordinateHessian V (gradient u x)) k j) := by
    filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
    rw [coordinateDerivative_comp (hVj.differentiable (by norm_num) _) hx]
    have hg (a : Fin n) : (fun y => gradient u y a) = coordinateDerivative u a :=
      funext fun y => (coordinateDerivative_eq_gradient u a y).symm
    simp_rw [hg]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  have hqW := (hasLocalWeakCoordinateDerivative_of_locallyLipschitz hq k).congr_ae
    Filter.EventuallyEq.rfl he
  have hqb : ∀ S, IsCompact S →
      MemLp (fun x => coordinateDerivative V j (gradient u x)) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_restrict_compact_of_continuous hq.continuous hS
  have hqDb : ∀ S, IsCompact S →
      MemLp (fun x => (coordinateHessian u x * coordinateHessian V (gradient u x)) k j)
        ∞ (volume.restrict S) := by
    intro S hS
    exact (memLp_congr_ae (ae_restrict_of_ae he)).mp
      (memLp_top_coordinateDerivative_of_locallyLipschitz hq k hS)
  have hρ : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have hρd : Continuous (fun x => -Real.exp (-u x) * coordinateDerivative u k x) :=
    hρ.neg.mul (contDiff_coordinateDerivative hu (m := 0) (by norm_num) k).continuous
  have hρb : ∀ S, IsCompact S → MemLp (fun x => Real.exp (-u x)) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_restrict_compact_of_continuous hρ hS
  have hρdb : ∀ S, IsCompact S →
      MemLp (fun x => -Real.exp (-u x) * coordinateDerivative u k x) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_restrict_compact_of_continuous hρd hS
  have hw := (actual_density_hasLocalWeakDerivative hu k).mul hqW
    (memLp_two_on_compacts_of_top hρb) (memLp_two_on_compacts_of_top hqb)
    (memLp_two_on_compacts_of_top hρdb) (memLp_two_on_compacts_of_top hqDb)
  have hid : (fun x => (-Real.exp (-u x) * coordinateDerivative u k x) *
      coordinateDerivative V j (gradient u x) +
      Real.exp (-u x) * (coordinateHessian u x * coordinateHessian V (gradient u x)) k j) =
      (fun x => Real.exp (-u x) *
        ((coordinateHessian u x * coordinateHessian V (gradient u x)) k j -
          coordinateDerivative u k x * coordinateDerivative V j (gradient u x))) := by
    funext x
    ring
  refine ⟨?_, ?_⟩
  · rwa [hid] at hw
  · intro S hS
    rw [← hid]
    have ha : MemLp (fun x => (-Real.exp (-u x) * coordinateDerivative u k x) *
        coordinateDerivative V j (gradient u x)) ∞ (volume.restrict S) := (hρdb S hS).mul (hqb S hS)
    have hb : MemLp (fun x => Real.exp (-u x) *
        (coordinateHessian u x * coordinateHessian V (gradient u x)) k j) ∞ (volume.restrict S) :=
      (hρb S hS).mul (hqDb S hS)
    exact ha.add hb

end KLS
end
