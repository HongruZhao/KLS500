import KLS.AdaptiveCumulantEnergy

/-! The tensor-coordinate action is exactly multilinear evaluation on
transformed coordinate directions. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def tensorCoordinates (M : ContinuousMultilinearMap ℝ (fun _ : Fin r => Space n) ℝ) :
    (Fin r → Fin n) → ℝ := fun a => M (fun s => EuclideanSpace.single (a s) 1)

def rowVector (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Space n :=
  ∑ j, P i j • EuclideanSpace.single j 1

theorem rowVector_apply (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    rowVector P i j = P i j := by
  change (EuclideanSpace.proj j) (∑ k, P i k • EuclideanSpace.single k 1) = _
  rw [map_sum]
  simp

theorem tensorCoordinates_transform
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin r => Space n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (a : Fin r → Fin n) :
    (tensorMatrix P *ᵥ tensorCoordinates M) a = M (fun s => rowVector P (a s)) := by
  change (∑ b : Fin r → Fin n, (∏ s, P (a s) (b s)) * M (fun s => EuclideanSpace.single (b s) 1)) = _
  unfold rowVector
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [M.map_smul_univ]
  rfl

end KLS.TensorEnergy
namespace KLS
variable {n r : ℕ} {ν : Measure (Space n)} [IsProbabilityMeasure ν]

theorem cumulantTensor_swap_front (hν : IsCompact ν.support)
    (u v : Space n) (h : Fin r → Space n) :
    cumulantTensor ν (r+2) (Fin.cons u (Fin.cons v h)) =
      cumulantTensor ν (r+2) (Fin.cons v (Fin.cons u h)) := by
  unfold cumulantTensor
  rw [← directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hν),
    ← directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hν)]
  simp only [List.ofFn_cons]
  exact congrFun (directionalWordDerivative_swap (contDiff_tiltLogLaplace hν) u v (List.ofFn h)) 0

end KLS
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem rowVector_inverseSqrt (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    rowVector (inverseSqrtCovariance μ (decodeState z)) k = inverseSqrtDirection μ z k := by
  apply PiLp.ext
  intro j
  rw [rowVector_apply]
  exact congrFun (congrFun (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq j) k

theorem whitenedCumulantTensor_eq_evaluation (u : Space n)
    (z : Fin (n+n*n) → ℝ) (a : Fin r → Fin n) :
    whitenedCumulantTensor μ r u z a =
      cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (r+1)
        (Fin.cons u (fun s => inverseSqrtDirection μ z (a s))) := by
  let M := (cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (r+1)).curryLeft u
  have h := tensorCoordinates_transform M (inverseSqrtCovariance μ (decodeState z)) a
  simp_rw [rowVector_inverseSqrt] at h
  exact h

theorem whitenedNextCumulantTensor_eq_evaluation (u : Space n)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) (a : Fin r → Fin n) :
    whitenedNextCumulantTensor μ r u k z a =
      cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (r+2)
        (Fin.cons (inverseSqrtDirection μ z k) (Fin.cons u (fun s => inverseSqrtDirection μ z (a s)))) := by
  let M := ((cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (r+2)).curryLeft
    (inverseSqrtDirection μ z k)).curryLeft u
  have h := tensorCoordinates_transform M (inverseSqrtCovariance μ (decodeState z)) a
  simp_rw [rowVector_inverseSqrt] at h
  exact h

theorem whitenedNextCumulantTensor_eq_next_slice (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) (a : Fin r → Fin n) :
    whitenedNextCumulantTensor μ r u k z a = whitenedCumulantTensor μ (r+1) u z (Fin.cons k a) := by
  rw [whitenedNextCumulantTensor_eq_evaluation, whitenedCumulantTensor_eq_evaluation]
  letI := law_isProbability hμ (decodeState z).1 (decodeState z).2
  rw [cumulantTensor_swap_front (by rwa [support_law hμ])]
  congr 2
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- Paper (90): the squared Brownian-noise tensors sum to the next genuine
inverse-covariance cumulant energy. -/
theorem sum_whitenedNextCumulantTensor_square (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (z : Fin (n+n*n) → ℝ) :
    (∑ k, whitenedNextCumulantTensor μ r u k z ⬝ᵥ whitenedNextCumulantTensor μ r u k z) =
      cumulantEnergy μ (r+1) u z := by
  rw [cumulantEnergy_eq_whitened hμ hfull]
  unfold dotProduct
  simp_rw [whitenedNextCumulantTensor_eq_next_slice hμ]
  have h := (Fin.consEquiv (fun _ : Fin (r+1) => Fin n)).sum_comp
    (fun a => whitenedCumulantTensor μ (r+1) u z a * whitenedCumulantTensor μ (r+1) u z a)
  have he (k : Fin n) (a : Fin r → Fin n) :
      (Fin.consEquiv (fun _ : Fin (r+1) => Fin n)) (k,a) = Fin.cons k a := rfl
  simpa only [Fintype.sum_prod_type, he] using h

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.sum_whitenedNextCumulantTensor_square
