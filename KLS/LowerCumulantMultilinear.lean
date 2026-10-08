import KLS.MaskedSubsetEnumeration

/-! Every labeled lower-cumulant contraction is genuinely multilinear.
Consequently the actual tensor-matrix whitening is exactly evaluation on
inverse covariance directions, including for the lower drift tensor. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n m : ℕ} {ν : Measure (Space n)} [IsProbabilityMeasure ν]

theorem listCumulant_cons_ofFn (hν : IsCompact ν.support)
    (v : Space n) (h : Fin m → Space n) :
    listCumulant ν (v :: List.ofFn h) = cumulantTensor ν (m+1) (Fin.cons v h) := by
  rw [listCumulant_eq_word hν, ← List.ofFn_cons,
    directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hν)]
  rfl

def subsetCumulantMultilinear (ν : Measure (Space n)) (w : Fin n → Space n)
    (S : Finset (Fin m)) : ContinuousMultilinearMap ℝ (fun _ : Fin m => Space n) ℝ :=
  ∑ k, (ContinuousMultilinearMap.curryFinFinset ℝ (Space n) ℝ (s := S) rfl rfl).symm
    (((cumulantTensor ν (S.card+1)).curryLeft (w k)).smulRight
      ((cumulantTensor ν (Sᶜ.card+1)).curryLeft (w k)))

theorem subsetCumulantMultilinear_apply (hν : IsCompact ν.support)
    (w : Fin n → Space n) (S : Finset (Fin m)) (h : Fin m → Space n) :
    subsetCumulantMultilinear ν w S h =
      ∑ k, listCumulant ν (w k :: maskedDirections h (fun i => decide (i ∈ S))) *
        listCumulant ν (w k :: maskedDirections h (fun i => decide (i ∈ Sᶜ))) := by
  simp only [subsetCumulantMultilinear, _root_.sum_apply,
    ContinuousMultilinearMap.curryFinFinset_symm_apply,
    ContinuousMultilinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.curryLeft_apply, finSumEquivOfFinset_inl, finSumEquivOfFinset_inr]
  apply Finset.sum_congr rfl
  intro k _
  rw [listCumulant_perm hν ((maskedDirections_perm_orderEmb h S).cons (w k)),
    listCumulant_perm hν ((maskedDirections_perm_orderEmb h Sᶜ).cons (w k)),
    listCumulant_cons_ofFn hν, listCumulant_cons_ofFn hν]

end KLS
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def lowerCumulantMultilinear (μ : Measure (Space n)) (m : ℕ)
    (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => Space n) ℝ :=
  ∑ S : Finset (Fin m), if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then
    subsetCumulantMultilinear (law μ (decodeState z).1 (decodeState z).2)
      (inverseSqrtDirection μ z) S else 0

theorem lowerCumulantMultilinear_apply (hμ : IsCompact μ.support)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) :
    lowerCumulantMultilinear μ m z i₀ h = lowerCumulantDrift μ h z i₀ := by
  let := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hν : IsCompact (law μ (decodeState z).1 (decodeState z).2).support := by
    rwa [support_law hμ]
  simp only [lowerCumulantMultilinear, _root_.sum_apply, lowerCumulantDrift]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs
  · exact subsetCumulantMultilinear_apply hν _ _ _
  · rfl

theorem whitenedLowerCumulantTensor_eq_evaluation (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (a : Fin r → Fin n) :
    whitenedLowerCumulantTensor μ r u z a =
      lowerCumulantDrift μ (Fin.cons u (fun s => inverseSqrtDirection μ z (a s))) z 0 := by
  let M := (lowerCumulantMultilinear μ (r+1) z 0).curryLeft u
  have he := tensorCoordinates_transform M (inverseSqrtCovariance μ (decodeState z)) a
  have hc : tensorCoordinates M = lowerCumulantTensor μ r u z := by
    funext b
    exact lowerCumulantMultilinear_apply hμ _ _ _
  rw [hc] at he
  simp_rw [rowVector_inverseSqrt] at he
  exact he.trans (lowerCumulantMultilinear_apply hμ _ _ _)

end KLS.AdaptiveLocalization
end
