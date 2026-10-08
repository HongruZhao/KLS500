import KLS.WeakHessianEvolution

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma locallyIntegrable_matrix_trace_product_of_localL2
    {A B : Space n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j S, IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hB : ∀ i j S, IsCompact S → MemLp (fun x => B x i j) 2 (volume.restrict S)) :
    LocallyIntegrable (fun x => (A x * B x).trace) volume := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hA i j S hS).integrable_mul (hB j i S hS)

/-- The actual weak Hessian evolution has locally L2 flux and locally L1
right side, so it can be tested through the genuine compact H1 extension. -/
theorem actual_hessian_evolution_local_integrability
    {u V : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k) (k l : Fin n) :
    (∀ a S, IsCompact S → MemLp
      (fun x => Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l) 2 (volume.restrict S)) ∧
    LocallyIntegrable (fun x => Real.exp (-u x) *
      (-coordinateHessian u x k l +
        (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace)) volume := by
  obtain ⟨hJ, hDJ, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    hu (hV.of_le (by norm_num)) hG hMA hTl hTw
  have hρ : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have hρb (S : Set (Space n)) (hS : IsCompact S) := memLp_top_restrict_compact_of_continuous hρ hS
  have hHb (i j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => coordinateHessian u x i j) ∞ (volume.restrict S) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz i j hS
  have hWb (i j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => coordinateHessian V (gradient u x) i j) ∞ (volume.restrict S) :=
    memLp_top_restrict_compact_of_continuous
      ((contDiff_coordinateHessian hV (m := 0) (by norm_num) i j).continuous.comp hG.continuous) hS
  have hEl (a i : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => (Real.exp (-u x) •
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) a i) 2 (volume.restrict S) := by
    have he : MemLp (fun x => -(-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) a i)
        2 (volume.restrict S) := (hDJ k a i S hS).neg
    have ht : MemLp (fun x => ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i)
        2 (volume.restrict S) := by simpa only [Matrix.neg_apply, neg_neg] using he
    exact (hρb S hS).mul ht
  have hquad := locallyIntegrable_matrix_trace_product_of_localL2 hEl (hTl l)
  have hquad' : LocallyIntegrable (fun x => Real.exp (-u x) *
      ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) volume := by
    simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using hquad
  have hlinear : LocallyIntegrable (fun x => Real.exp (-u x) *
      (-coordinateHessian u x k l +
        (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l)) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    apply memLp_two_on_compacts_of_top
    intro S hS
    have hM (a i : Fin n) := memLp_top_matrixMul (fun p q => hHb p q S hS) (fun p q => hWb p q S hS) a i
    have hM' := memLp_top_matrixMul hM (fun p q => hHb p q S hS) k l
    exact (hρb S hS).mul ((hHb k l S hS).neg.add hM')
  refine ⟨?_, ?_⟩
  · intro a S hS
    exact (hρb S hS).mul (memLp_two_matrixMul_left (fun i j => hJ i j S hS) (fun i j => hTl k i j S hS) a l)
  · have h := hlinear.add hquad'
    convert h using 1
    funext x
    dsimp only [Pi.add_apply]
    ring

/-- The genuine weak Hessian evolution extends to any bounded compact H1
scalar test with its actual supplied weak derivative. All pairings are
proved integrable; the extension uses actual mollifications. -/
theorem actual_weak_hessian_evolution_bounded_H1
    {u V f : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ} {F : Fin n → Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ i,
      (∑ a, ∫ x, Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i * coordinateDerivative ψ a x) =
        ∫ x, Real.exp (-u x) * coordinateDerivative V i (gradient u x) * ψ x)
    (hf : ∀ S, IsCompact S → MemLp f 2 (volume.restrict S)) (hc : HasCompactSupport f)
    {C : ℝ} (hbound : ∀ᵐ x, ‖f x‖ ≤ C)
    (hFl : ∀ a S, IsCompact S → MemLp (F a) 2 (volume.restrict S))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) (k l : Fin n) :
    (∀ a, Integrable (fun x => Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l * F a x)) ∧
    Integrable (fun x => Real.exp (-u x) *
      (-coordinateHessian u x k l +
        (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) * f x) ∧
    -(∑ a, ∫ x, Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l * F a x) =
      ∫ x, Real.exp (-u x) *
        (-coordinateHessian u x k l +
          (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
          ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) * f x := by
  let R (x : Space n) := Real.exp (-u x) *
    (-coordinateHessian u x k l +
      (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
      ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace)
  have hlocal := actual_hessian_evolution_local_integrability hu hV hG hMA hTl hTw k l
  have hR : LocallyIntegrable (fun x => -R x) volume := hlocal.2.neg
  have htest (ψ : Space n → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
      (∑ a, ∫ x, Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l * coordinateDerivative ψ a x) =
        ∫ x, (-R x) * ψ x := by
    have he := actual_weak_hessian_evolution_matrix_flux hu hV hG hMA hTl hTw hdiv hψ hψc k l
    have hr : (∫ x, (-R x) * ψ x) = -(∫ x, ψ x * Real.exp (-u x) *
        (-coordinateHessian u x k l +
          (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
          ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [R]; ring
    rw [hr]
    linarith
  have hh := integral_divergence_of_bounded_compact_H1_test hlocal.1 hR htest hf hc hbound hFl hFw
  have hr : (∫ x, (-R x) * f x) = -(∫ x, R x * f x) := by
    simp only [neg_mul, integral_neg]
  have hi : Integrable (fun x => R x * f x) := by
    have hn : Integrable (fun x => -((-R x) * f x)) := hh.2.1.neg
    simpa only [neg_mul, neg_neg] using hn
  refine ⟨hh.1, hi, ?_⟩
  have he := hh.2.2
  rw [hr] at he
  change -(∑ a, ∫ x, Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l * F a x) = ∫ x, R x * f x
  linarith

end KLS
end
