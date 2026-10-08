import KLS.BoundedLocalH1CompactFlux

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual coefficient-gradient flux of a scalar function. -/
def weakEllipticFlux (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  ∑ j, A x i j * coordinateDerivative f j x

theorem weakEllipticFlux_localL2
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {f : Space n → ℝ}
    (hA : ∀ i j S, IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hDf : ∀ j, LocallyLipschitz (coordinateDerivative f j))
    (i : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
    MemLp (weakEllipticFlux A f i) 2 (volume.restrict S) := by
  apply memLp_finsetSum
  intro j _
  simpa only [mul_comm] using memLp_continuous_mul_on_compact hS (hA i j S hS) (hDf j).continuous

/-- The actual expression is locally L1 with locally L2 coefficients and
 locally Lipschitz first derivatives. No derivative of the coefficients is used. -/
theorem weakEllipticExpression_locallyIntegrable_of_localC11
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ} {f : Space n → ℝ}
    (hA : ∀ i j S, IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j S, IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hDf : ∀ j, LocallyLipschitz (coordinateDerivative f j)) :
    LocallyIntegrable (weakEllipticExpression A b f) volume := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  have hsecond (i j : Fin n) : Integrable (fun x => A x i j * coordinateHessian f x i j)
      (volume.restrict S) := by
    have hh := memLp_top_coordinateDerivative_of_locallyLipschitz (hDf j) i hS
    have hi : MemLp (fun x => A x i j * coordinateHessian f x i j) 2 (volume.restrict S) :=
      (hA i j S hS).mul hh
    exact hi.integrable (by norm_num)
  have hfirst (j : Fin n) : Integrable (fun x => b j x * coordinateDerivative f j x)
      (volume.restrict S) := by
    have hi := memLp_continuous_mul_on_compact hS (hb j S hS) (hDf j).continuous
    simpa only [mul_comm] using hi.integrable (by norm_num)
  exact (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hsecond i j))).sub
    (integrable_finsetSum _ (fun j _ => hfirst j))

/-- Genuine weak column divergence induces the actual divergence equation
 for the coefficient-gradient flux of a local C1,1 function. -/
theorem integral_weakEllipticFlux_coordinateDerivative
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Fin n → Space n → ℝ} {f : Space n → ℝ}
    (hA : ∀ i j S, IsCompact S → MemLp (fun x => A x i j) 2 (volume.restrict S))
    (hb : ∀ j S, IsCompact S → MemLp (b j) 2 (volume.restrict S))
    (hdiv : ∀ j ψ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A x i j * coordinateDerivative ψ i x) = ∫ x, b j x * ψ x)
    (hDf : ∀ j, LocallyLipschitz (coordinateDerivative f j))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    (∑ i, ∫ x, weakEllipticFlux A f i x * coordinateDerivative ψ i x) =
      ∫ x, (-weakEllipticExpression A b f x) * ψ x := by
  obtain ⟨_,_,he⟩ := integral_weakEllipticExpression_localC11_compact_first_factor
    hA hb hdiv hDf hψ hψc
  have hi (i : Fin n) : Integrable (fun x => weakEllipticFlux A f i x * coordinateDerivative ψ i x) :=
    integrable_mul_continuous_compact_of_localL2
      ((contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous)
      (hasCompactSupport_coordinateDerivative hψc i) (weakEllipticFlux_localL2 hA hDf i)
  have hp (x : Space n) : (∑ i, weakEllipticFlux A f i x * coordinateDerivative ψ i x) =
      ∑ i, ∑ j, A x i j * coordinateDerivative ψ i x * coordinateDerivative f j x := by
    simp only [weakEllipticFlux,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hp]
  have hr : (∫ x, (-weakEllipticExpression A b f x) * ψ x) =
      -(∫ x, ψ x * weakEllipticExpression A b f x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  rw [hr,he,neg_neg]

end KLS
end
