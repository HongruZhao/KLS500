import KLS.WeakInverseTensorDivergence
import KLS.WeakHessianCompactTest
import KLS.RawInverseHessianContractions

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma matrix_identity_sub_row_contraction
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (M : Matrix (Fin n) (Fin n) ℝ) (k l : Fin n) :
    (∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) k i - M k i) * H l i) = H k l - (M * H) k l := by
  calc
    _ = ((1 - M) * H) k l := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [hH.apply i l]
      rfl
    _ = _ := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]

/-- Actual weak Hessian evolution follows by testing the differentiated
inverse columns with bounded compact H1 Hessian entries. The raw tensor
has genuine weak derivatives and both adjacent symmetries proved from them. -/
theorem actual_weak_hessian_evolution_matrix_flux
    {u V χ : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ i,
      (∑ a, ∫ x, Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i * coordinateDerivative ψ a x) =
        ∫ x, Real.exp (-u x) * coordinateDerivative V i (gradient u x) * ψ x)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (k l : Fin n) :
    -(∑ a, ∫ x, Real.exp (-u x) * ((coordinateHessian u x)⁻¹ * T x k) a l * coordinateDerivative χ a x) =
      ∫ x, χ x * Real.exp (-u x) *
        (-coordinateHessian u x k l +
          (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
          ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) := by
  let H (x : Space n) := coordinateHessian u x
  let J (x : Space n) := (H x)⁻¹
  let W (x : Space n) := coordinateHessian V (gradient u x)
  let ρ (x : Space n) := Real.exp (-u x)
  let E (x : Space n) := J x * T x k * J x
  let b (i : Fin n) (x : Space n) := ρ x * ((1 : Matrix (Fin n) (Fin n) ℝ) k i - (H x * W x) k i)
  obtain ⟨hJ, hDJ, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    hu (hV.of_le (by norm_num)) hG hMA hTl hTw
  have hρ : Continuous ρ := Real.continuous_exp.comp hu.continuous.neg
  have hρb (S : Set (Space n)) (hS : IsCompact S) := memLp_top_restrict_compact_of_continuous hρ hS
  have hHb (i j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => H x i j) ∞ (volume.restrict S) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz i j hS
  have hWb (i j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => W x i j) ∞ (volume.restrict S) :=
    memLp_top_restrict_compact_of_continuous
      ((contDiff_coordinateHessian hV (m := 0) (by norm_num) i j).continuous.comp hG.continuous) hS
  have hbl (i : Fin n) : LocallyIntegrable (b i) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    apply memLp_two_on_compacts_of_top
    intro S hS
    have hM := memLp_top_matrixMul (fun a c => hHb a c S hS) (fun a c => hWb a c S hS) k i
    exact (hρb S hS).mul ((memLp_top_const ((1 : Matrix (Fin n) (Fin n) ℝ) k i)).sub hM)
  have hEl (a i : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => ρ x * E x a i) 2 (volume.restrict S) := by
    have he : MemLp (fun x => -(-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) a i)
        2 (volume.restrict S) := (hDJ k a i S hS).neg
    have he' : MemLp (fun x => E x a i) 2 (volume.restrict S) := by
      simpa only [Matrix.neg_apply, neg_neg] using he
    exact (hρb S hS).mul he'
  have hcolumn (i : Fin n) (ψ : Space n → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
      (∑ a, ∫ x, (ρ x * E x a i) * coordinateDerivative ψ a x) = ∫ x, b i x * ψ x :=
    actual_inverse_tensor_integral_column hu hV hG hMA hTl hTw hdiv k i hψ hψc
  have htest (i : Fin n) := actual_hessian_compact_H1_test hG hTl hTw hχ hc l i
  have htested (i : Fin n) :
      (∀ a, Integrable (fun x => (ρ x * E x a i) *
        (χ x * T x a l i + coordinateDerivative χ a x * H x l i))) ∧
      Integrable (fun x => b i x * (χ x * H x l i)) ∧
      (∑ a, ∫ x, (ρ x * E x a i) *
        (χ x * T x a l i + coordinateDerivative χ a x * H x l i)) =
        ∫ x, b i x * (χ x * H x l i) := by
    obtain ⟨C, hC⟩ := (htest i).2.1
    exact integral_divergence_of_bounded_compact_H1_test (fun a => hEl a i) (hbl i) (hcolumn i)
      (htest i).2.2.1 (htest i).1 (Eventually.of_forall hC) (htest i).2.2.2.1 (htest i).2.2.2.2
  let Q (i a : Fin n) (x : Space n) := (ρ x * E x a i * T x a l i) * χ x
  let L (i a : Fin n) (x : Space n) := (ρ x * E x a i * H x l i) * coordinateDerivative χ a x
  have hQi (i a : Fin n) : Integrable (Q i a) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_product_of_localL2 (hEl a i) (hTl a l i)) hχ.continuous hc
  have hLi (i a : Fin n) : Integrable (L i a) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_product_of_localL2 (hEl a i) (memLp_two_on_compacts_of_top (hHb l i)))
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) a).continuous
      (hasCompactSupport_coordinateDerivative hc a)
  have hsplit (i a : Fin n) : (∫ x, (ρ x * E x a i) *
      (χ x * T x a l i + coordinateDerivative χ a x * H x l i)) =
      (∫ x, Q i a x) + ∫ x, L i a x := by
    rw [← integral_add (hQi i a) (hLi i a)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [Q, L]; ring
  have hsum : (∑ i, ∑ a, ∫ x, Q i a x) + (∑ i, ∑ a, ∫ x, L i a x) =
      ∑ i, ∫ x, b i x * (χ x * H x l i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have he := (htested i).2.2
    simp_rw [hsplit] at he
    rwa [Finset.sum_add_distrib] at he
  have hsym := actual_hessian_ae_symmetric_of_locallyLipschitz_gradient hu.locallyLipschitz hG.locallyLipschitz
  have hTsym := actual_weak_third_tensor_ae_symmetric hu.locallyLipschitz hG.locallyLipschitz hTl hTw
  have hQpoint : (fun x => ∑ i, ∑ a, Q i a x) =ᵐ[volume]
      (fun x => χ x * ρ x * (J x * T x k * J x * T x l).trace) := by
    filter_upwards [hTsym] with x hx
    have ht := raw_inverse_hessian_column_times_third (H x) (T x)
      (fun a i j => (hx a i j).1) (fun a i j => (hx a i j).2) k l
    calc
      _ = (χ x * ρ x) * (∑ a, ∑ i, E x a i * T x a l i) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [Q]
        ring
      _ = _ := by rw [ht]
  have hQsum : (∑ i, ∑ a, ∫ x, Q i a x) =
      ∫ x, χ x * ρ x * (J x * T x k * J x * T x l).trace := by
    calc
      _ = ∑ i, ∫ x, ∑ a, Q i a x := by
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum _ (fun a _ => hQi i a)).symm
      _ = ∫ x, ∑ i, ∑ a, Q i a x :=
        (integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hQi i a))).symm
      _ = _ := integral_congr_ae hQpoint
  have hQint : Integrable (fun x => χ x * ρ x * (J x * T x k * J x * T x l).trace) :=
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hQi i a))).congr hQpoint
  have hLpoint (a : Fin n) : (fun x => ∑ i, L i a x) =ᵐ[volume]
      (fun x => ρ x * (J x * T x k) a l * coordinateDerivative χ a x) := by
    filter_upwards [hMA, hsym] with x hx hs
    have huH : IsUnit (H x).det := isUnit_iff_ne_zero.mpr (by rw [hx]; exact (Real.exp_pos _).ne')
    have he := raw_inverse_hessian_column_times_hessian hs huH (T x) a k l
    calc
      _ = (ρ x * coordinateDerivative χ a x) * (∑ i, E x a i * H x l i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [L]
        ring
      _ = _ := by rw [he]; ring
  have hLsum : (∑ i, ∑ a, ∫ x, L i a x) =
      ∑ a, ∫ x, ρ x * (J x * T x k) a l * coordinateDerivative χ a x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_finsetSum _ (fun i _ => hLi i a)]
    exact integral_congr_ae (hLpoint a)
  have hRpoint : (fun x => ∑ i, b i x * (χ x * H x l i)) =ᵐ[volume]
      (fun x => χ x * ρ x * (H x k l - (H x * W x * H x) k l)) := by
    filter_upwards [hsym] with x hx
    have he := matrix_identity_sub_row_contraction hx (H x * W x) k l
    calc
      _ = (χ x * ρ x) * (∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) k i - (H x * W x) k i) * H x l i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [b]
        ring
      _ = _ := by rw [he]
  have hRsum : (∑ i, ∫ x, b i x * (χ x * H x l i)) =
      ∫ x, χ x * ρ x * (H x k l - (H x * W x * H x) k l) := by
    rw [← integral_finsetSum _ (fun i _ => (htested i).2.1)]
    exact integral_congr_ae hRpoint
  have hRint : Integrable (fun x => χ x * ρ x * (H x k l - (H x * W x * H x) k l)) :=
    (integrable_finsetSum _ (fun i _ => (htested i).2.1)).congr hRpoint
  rw [hQsum, hLsum, hRsum] at hsum
  change -(∑ a, ∫ x, ρ x * (J x * T x k) a l * coordinateDerivative χ a x) =
    ∫ x, χ x * ρ x * (-H x k l + (H x * W x * H x) k l + (J x * T x k * J x * T x l).trace)
  have he : (∫ x, χ x * ρ x *
      (-H x k l + (H x * W x * H x) k l + (J x * T x k * J x * T x l).trace)) =
      (∫ x, χ x * ρ x * (J x * T x k * J x * T x l).trace) -
        ∫ x, χ x * ρ x * (H x k l - (H x * W x * H x) k l) := by
    rw [← integral_sub hQint hRint]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  rw [he]
  linarith

end KLS
end
