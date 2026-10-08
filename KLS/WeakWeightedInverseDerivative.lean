import KLS.WeakHessianInverseDerivative

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem actual_density_hasLocalWeakDerivative
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (k : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => Real.exp (-u x))
      (fun x => -Real.exp (-u x) * coordinateDerivative u k x) k := by
  have he : coordinateDerivative (fun x => Real.exp (-u x)) k =
      fun x => -Real.exp (-u x) * coordinateDerivative u k x := by
    funext x
    unfold coordinateDerivative
    rw [fderiv_exp_neg_apply (hu.differentiable (by norm_num) x)]
    ring
  rw [← he]
  exact hasLocalWeakCoordinateDerivative_of_contDiff hu.neg.exp k

/-- The density-weighted actual inverse has its constructed local L2 weak
 derivative. The Hessian derivative remains the raw tensor T. -/
theorem actual_weighted_inverse_hasLocalWeakDerivative
    {u : Space n → ℝ} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ i j S, IsCompact S →
      MemLp (fun x => (coordinateHessian u x)⁻¹ i j) ∞ (volume.restrict S))
    (hDJ : ∀ k i j S, IsCompact S →
      MemLp (fun x => (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j)
        2 (volume.restrict S))
    (hJw : ∀ k i j, HasLocalWeakCoordinateDerivative (fun x => (coordinateHessian u x)⁻¹ i j)
      (fun x => (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j) k)
    (k i j : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j)
      (fun x => -(coordinateDerivative u k x * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j)) -
        Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) i j) k ∧
    ∀ S, IsCompact S →
      MemLp (fun x => -(coordinateDerivative u k x * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j)) -
        Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) i j)
        2 (volume.restrict S) := by
  have hρ : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have hρd : Continuous (fun x => -Real.exp (-u x) * coordinateDerivative u k x) :=
    hρ.neg.mul (contDiff_coordinateDerivative hu (m := 0) (by norm_num) k).continuous
  have hρb : ∀ S, IsCompact S → MemLp (fun x => Real.exp (-u x)) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_restrict_compact_of_continuous hρ hS
  have hρdb : ∀ S, IsCompact S →
      MemLp (fun x => -Real.exp (-u x) * coordinateDerivative u k x) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_restrict_compact_of_continuous hρd hS
  have hw := (actual_density_hasLocalWeakDerivative hu k).mul (hJw k i j)
    (memLp_two_on_compacts_of_top hρb) (memLp_two_on_compacts_of_top (hJ i j))
    (memLp_two_on_compacts_of_top hρdb) (hDJ k i j)
  have he : (fun x => (-Real.exp (-u x) * coordinateDerivative u k x) * (coordinateHessian u x)⁻¹ i j +
      Real.exp (-u x) * (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j) =
      (fun x => -(coordinateDerivative u k x * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ i j)) -
        Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) i j) := by
    funext x
    simp only [Matrix.neg_apply]
    ring
  refine ⟨?_, ?_⟩
  · rwa [he] at hw
  · intro S hS
    rw [← he]
    have ha : MemLp (fun x => (-Real.exp (-u x) * coordinateDerivative u k x) *
        (coordinateHessian u x)⁻¹ i j) 2 (volume.restrict S) :=
      (hρdb S hS).mul (memLp_two_on_compacts_of_top (hJ i j) S hS)
    have hb : MemLp (fun x => Real.exp (-u x) *
        (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j) 2 (volume.restrict S) :=
      (hρb S hS).mul (hDJ k i j S hS)
    exact ha.add hb

end KLS
end
