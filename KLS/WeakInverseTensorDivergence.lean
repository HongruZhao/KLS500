import KLS.WeakWeightedTargetDerivative
import KLS.WeakDivergenceMultiplier

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Differentiating the actual inverse-column divergence yields the
 divergence of J*T_k*J. The density-gradient terms cancel by a genuine
 local H1 product rule and the actual inverse-Hessian identity. -/
theorem actual_inverse_tensor_integral_column
    {u V : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ i,
      (∑ a, ∫ x, Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i * coordinateDerivative ψ a x) =
        ∫ x, Real.exp (-u x) * coordinateDerivative V i (gradient u x) * ψ x)
    (k i : Fin n) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ a, ∫ x, Real.exp (-u x) *
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i * coordinateDerivative ψ a x) =
      ∫ x, Real.exp (-u x) *
        ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
          (coordinateHessian u x * coordinateHessian V (gradient u x)) k i) * ψ x := by
  obtain ⟨hJ, hDJ, hJw⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    hu (hV.of_le (by norm_num)) hG hMA hTl hTw
  have hρ : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have huk : Continuous (coordinateDerivative u k) :=
    (contDiff_coordinateDerivative hu (m := 0) (by norm_num) k).continuous
  have hVi : Continuous (fun x => coordinateDerivative V i (gradient u x)) :=
    (contDiff_coordinateDerivative hV (m := 1) (by norm_num) i).continuous.comp hG.continuous
  have hρb (S : Set (Space n)) (hS : IsCompact S) := memLp_top_restrict_compact_of_continuous hρ hS
  have hukb (S : Set (Space n)) (hS : IsCompact S) := memLp_top_restrict_compact_of_continuous huk hS
  have hAl (a : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i) 2 (volume.restrict S) :=
    (hρb S hS).mul (memLp_two_on_compacts_of_top (hJ a i) S hS)
  have hEl (a : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => Real.exp (-u x) *
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i) 2 (volume.restrict S) := by
    have ht : MemLp (fun x => ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i)
        2 (volume.restrict S) := by
      have hh : MemLp (fun x => -(-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) a i)
          2 (volume.restrict S) := (hDJ k a i S hS).neg
      simpa only [Matrix.neg_apply, neg_neg] using hh
    exact (hρb S hS).mul ht
  have hBl (a : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => coordinateDerivative u k x *
        (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i)) 2 (volume.restrict S) :=
    (hukb S hS).mul (hAl a S hS)
  have hweighted (a : Fin n) := actual_weighted_inverse_hasLocalWeakDerivative hu hJ hDJ hJw k a i
  have htarget := actual_weighted_targetGradient_hasLocalWeakDerivative hu hV hG k i
  have htargetloc := locallyIntegrable_of_memLp_two_on_compacts
    (memLp_two_on_compacts_of_top htarget.2)
  have hD := integral_divergence_coordinateDerivative (fun a => (hweighted a).1) htarget.1
    (fun a => (hweighted a).2) htargetloc (fun φ hφ hφc => hdiv φ hφ hφc i) hψ hc
  have hHloc (a : Fin n) : ∀ S, IsCompact S →
      MemLp (fun x => coordinateHessian u x a k) 2 (volume.restrict S) :=
    memLp_two_on_compacts_of_top (fun S hS =>
      memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz a k hS)
  have hbcont : LocallyIntegrable (fun x => Real.exp (-u x) * coordinateDerivative V i (gradient u x)) volume :=
    (hρ.mul hVi).locallyIntegrable
  have hM := integral_divergence_mul_localH1 hAl hbcont
    (fun φ hφ hφc => hdiv φ hφ hφc i) huk (memLp_two_on_compacts_of_top hukb) hHloc
    (fun a => actual_hessian_hasLocalWeakCoordinateDerivative hG.locallyLipschitz a k) hψ hc
  have hsym := actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hu.locallyLipschitz hG.locallyLipschitz
  have hcontract : ∀ᵐ x, (∑ a, (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i) *
      coordinateHessian u x a k) = Real.exp (-u x) * (1 : Matrix (Fin n) (Fin n) ℝ) k i := by
    filter_upwards [hMA, hsym] with x hx hs
    have hdet : (coordinateHessian u x).det ≠ 0 := by rw [hx]; exact (Real.exp_pos _).ne'
    calc
      _ = Real.exp (-u x) * (coordinateHessian u x * (coordinateHessian u x)⁻¹) k i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [hs.apply a k]
        ring
      _ = _ := by rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
  have hMright : (∫ x, (coordinateDerivative u k x *
        (Real.exp (-u x) * coordinateDerivative V i (gradient u x)) -
        ∑ a, (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i) * coordinateHessian u x a k) * ψ x) =
      ∫ x, Real.exp (-u x) *
        (coordinateDerivative u k x * coordinateDerivative V i (gradient u x) -
          (1 : Matrix (Fin n) (Fin n) ℝ) k i) * ψ x := by
    apply integral_congr_ae
    filter_upwards [hcontract] with x hx
    rw [hx]
    ring
  rw [hMright] at hM
  have hda := fun a => (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous
  have hBi (a : Fin n) := integrable_mul_compact_of_locallyIntegrable
    (locallyIntegrable_of_memLp_two_on_compacts (hBl a)) (hda a) (hasCompactSupport_coordinateDerivative hc a)
  have hEi (a : Fin n) := integrable_mul_compact_of_locallyIntegrable
    (locallyIntegrable_of_memLp_two_on_compacts (hEl a)) (hda a) (hasCompactSupport_coordinateDerivative hc a)
  have hsplit (a : Fin n) : (∫ x,
      (-(coordinateDerivative u k x * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i)) -
        Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i) *
          coordinateDerivative ψ a x) =
      -(∫ x, (coordinateDerivative u k x * (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i)) *
          coordinateDerivative ψ a x) -
        ∫ x, (Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹) a i) *
          coordinateDerivative ψ a x := by
    simp only [sub_mul, neg_mul]
    have hn : Integrable (fun x => -((coordinateDerivative u k x *
        (Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i)) * coordinateDerivative ψ a x)) := (hBi a).neg
    rw [integral_sub hn (hEi a), integral_neg]
  simp_rw [hsplit] at hD
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hM] at hD
  have hDb := integrable_mul_compact_of_locallyIntegrable htargetloc hψ.continuous hc
  have hMb : Integrable (fun x => Real.exp (-u x) *
      (coordinateDerivative u k x * coordinateDerivative V i (gradient u x) -
        (1 : Matrix (Fin n) (Fin n) ℝ) k i) * ψ x) :=
    ((hρ.mul ((huk.mul hVi).sub continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hr : (∫ x, Real.exp (-u x) *
        ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
          (coordinateHessian u x * coordinateHessian V (gradient u x)) k i) * ψ x) =
      -(∫ x, Real.exp (-u x) *
        (coordinateDerivative u k x * coordinateDerivative V i (gradient u x) -
          (1 : Matrix (Fin n) (Fin n) ℝ) k i) * ψ x) -
      ∫ x, Real.exp (-u x) *
        ((coordinateHessian u x * coordinateHessian V (gradient u x)) k i -
          coordinateDerivative u k x * coordinateDerivative V i (gradient u x)) * ψ x := by
    have hn : Integrable (fun x => -(Real.exp (-u x) *
        (coordinateDerivative u k x * coordinateDerivative V i (gradient u x) -
          (1 : Matrix (Fin n) (Fin n) ℝ) k i) * ψ x)) := hMb.neg
    rw [← integral_neg, ← integral_sub hn hDb]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  rw [hr]
  linarith

end KLS
end
