import KLS.WeakHessianInverseDerivative

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma actual_hessian_global_entry_bound
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (x : Space n) (i j : Fin n) : ‖coordinateHessian u x i j‖ ≤ G := by
  have hcoord : LipschitzWith G (coordinateDerivative u j) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hb := (PiLp.norm_apply_le (gradient u y - gradient u z) j).trans (hG.norm_sub_le y z)
    simpa only [dist_eq_norm, PiLp.sub_apply, coordinateDerivative_eq_gradient] using hb
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hcoord
  have hh := ((fderiv ℝ (coordinateDerivative u j) x).le_opNorm (EuclideanSpace.single i 1)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  simpa only [coordinateHessian, coordinateDerivative, PiLp.norm_single, norm_one, mul_one] using hh

/-- An actual compact Hessian test has a global bound and the explicit raw
H1 derivative needed by the divergence extension theorem. -/
theorem actual_hessian_compact_H1_test
    {u χ : Space n → ℝ} {G : ℝ≥0} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hG : LipschitzWith G (gradient u))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i j : Fin n) :
    HasCompactSupport (fun x => χ x * coordinateHessian u x i j) ∧
    (∃ C : ℝ, ∀ x, ‖χ x * coordinateHessian u x i j‖ ≤ C) ∧
    (∀ S, IsCompact S → MemLp (fun x => χ x * coordinateHessian u x i j) 2 (volume.restrict S)) ∧
    (∀ k S, IsCompact S → MemLp
      (fun x => χ x * T x k i j + coordinateDerivative χ k x * coordinateHessian u x i j)
      2 (volume.restrict S)) ∧
    ∀ k, HasLocalWeakCoordinateDerivative (fun x => χ x * coordinateHessian u x i j)
      (fun x => χ x * T x k i j + coordinateDerivative χ k x * coordinateHessian u x i j) k := by
  have hHb : ∀ S, IsCompact S → MemLp (fun x => coordinateHessian u x i j) ∞ (volume.restrict S) :=
    fun S hS => memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz i j hS
  have hH2 := memLp_two_on_compacts_of_top hHb
  have hχb (S : Set (Space n)) := (hχ.continuous.memLp_top_of_hasCompactSupport hc volume).restrict S
  have hdχ (k : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) k).continuous
  have hdχb (k : Fin n) (S : Set (Space n)) :=
    ((hdχ k).memLp_top_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc k) volume).restrict S
  refine ⟨hc.mul_right, ?_, fun S hS => (hχb S).mul (hH2 S hS), ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
    refine ⟨C * G, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC x) (actual_hessian_global_entry_bound hG x i j)
      (norm_nonneg _) (le_trans (norm_nonneg (χ x)) (hC x))
  · intro k S hS
    have ha : MemLp (fun x => χ x * T x k i j) 2 (volume.restrict S) := (hχb S).mul (hTl k i j S hS)
    have hb : MemLp (fun x => coordinateDerivative χ k x * coordinateHessian u x i j)
        2 (volume.restrict S) := (hdχb k S).mul (hH2 S hS)
    exact ha.add hb
  · intro k
    have hw := (hasLocalWeakCoordinateDerivative_of_contDiff hχ k).mul (hTw k i j)
      (fun S _ => (hχ.continuous.memLp_of_hasCompactSupport hc).restrict S) hH2
      (fun S _ => ((hdχ k).memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc k)).restrict S) (hTl k i j)
    have he : (fun x => coordinateDerivative χ k x * coordinateHessian u x i j + χ x * T x k i j) =
        (fun x => χ x * T x k i j + coordinateDerivative χ k x * coordinateHessian u x i j) := by
      funext x
      exact add_comm _ _
    rwa [he] at hw

end KLS
end
