import SpectralReductionLongPrefix

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

theorem norm_sq_le_of_projection_recovery_coefficient {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) {C : ℝ} (hc : 1<C)
    {ε : ℝ} (hε : 0<ε)
    (hy : ‖y‖^2 ≤ C*‖finiteIsometryAverage ρ y‖^2)
    (horth : inner ℝ x y=‖y‖^2) :
    ‖x‖^2 ≤ (1+ε)*C*‖finiteIsometryAverage ρ x‖^2 +
      (C+(C-1)/ε)*‖x-y‖^2 := by
  let p := finiteIsometryAverage ρ x
  let q := finiteIsometryAverage ρ y
  let α := (1+ε)*C
  let A := α-1
  let H := (1+ε)*(C-1)
  have hC : 0<C-1 := by linarith
  have hA : 0<A := by dsimp [A, α]; nlinarith
  have hH : 0<H := by dsimp [H]; positivity
  have hgap : 0≤C*‖q‖^2-‖y‖^2 := by dsimp [q]; linarith
  have hpq : inner ℝ p q=inner ℝ x q := inner_finiteIsometryAverage_pair ρ x y
  have hpy : inner ℝ p y=inner ℝ p q := by
    calc
      _ = inner ℝ y p := real_inner_comm _ _
      _ = inner ℝ q p := (inner_finiteIsometryAverage_pair ρ y x).symm
      _ = _ := real_inner_comm _ _
  have hux : ‖x-p‖^2=‖x‖^2-‖p‖^2 := by
    rw [norm_sub_sq_real, inner_finiteIsometryAverage_self]
    ring
  have huy : ‖y-q‖^2=‖y‖^2-‖q‖^2 := by
    rw [norm_sub_sq_real, inner_finiteIsometryAverage_self]
    ring
  have huv : inner ℝ (x-p) (y-q)=‖y‖^2-inner ℝ p q := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, horth, ←hpq, hpy]
    ring
  have h1 : 0≤H^2*(‖x‖^2-‖p‖^2)+A^2*(‖y‖^2-‖q‖^2)-
      2*H*A*(‖y‖^2-inner ℝ p q) := by
    have hh := sq_nonneg ‖H • (x-p)-A • (y-q)‖
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right] at hh
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial, hux, huy, huv] at hh
    nlinarith [hh]
  have h2 : 0≤(1+ε)^2*‖p‖^2+‖q‖^2-2*(1+ε)*inner ℝ p q := by
    have hh := sq_nonneg ‖(1+ε) • p-q‖
    rw [norm_sub_sq_real, norm_smul, inner_smul_left] at hh
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial] at hh
    nlinarith [hh]
  have hid : H*(ε*α*‖p‖^2+A*(‖x‖^2-‖y‖^2)-ε*‖x‖^2) =
      (H^2*(‖x‖^2-‖p‖^2)+A^2*(‖y‖^2-‖q‖^2)-2*H*A*(‖y‖^2-inner ℝ p q)) +
      A*(C-1)*((1+ε)^2*‖p‖^2+‖q‖^2-2*(1+ε)*inner ℝ p q) +
      ε*A*(C*‖q‖^2-‖y‖^2) := by
    dsimp [H, A, α]
    ring
  have hnon : 0≤H*(ε*α*‖p‖^2+A*(‖x‖^2-‖y‖^2)-ε*‖x‖^2) := by
    rw [hid]
    exact add_nonneg (add_nonneg h1 (mul_nonneg (mul_nonneg hA.le hC.le) h2))
      (mul_nonneg (mul_nonneg hε.le hA.le) hgap)
  have hpoly := (mul_nonneg_iff_of_pos_left hH).mp hnon
  have hz : ‖x-y‖^2=‖x‖^2-‖y‖^2 := by rw [norm_sub_sq_real, horth]; ring
  have hAid : A=ε*(C+(C-1)/ε) := by
    dsimp [A, α]
    field_simp
    ring
  rw [←hz, hAid] at hpoly
  have hf : ε*‖x‖^2 ≤ ε*((1+ε)*C*‖p‖^2+(C+(C-1)/ε)*‖x-y‖^2) := by
    dsimp [α] at hpoly
    nlinarith
  exact (mul_le_mul_iff_right₀ hε).mp hf

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_tripleYoung
    {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    {ε : ℝ} (hε : 0 < ε)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 3 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      (1 + ε) * ((3 * d).choose d : ℝ) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      (((3*d).choose d : ℝ) + (((3*d).choose d : ℝ) - 1)/ε) * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have htwo : (2 : ℝ) ≤ ((3*d).choose d : ℝ) := by
    exact_mod_cast (Nat.two_le_centralBinom d (by omega)).trans
      (Nat.choose_le_choose d (by omega : 2*d≤3*d))
  have hc : (1 : ℝ) < ((3*d).choose d : ℝ) := by linarith
  have hcsub : 0 ≤ ((3*d).choose d : ℝ)-1 := by nlinarith
  have hy := norm_sq_weightedL2BlockTaylor_symmetrized_triple_choose_le hφ hκ hlower r d q hq g
  have horth : inner ℝ (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) =
      ‖weightedL2BlockTaylor φ r d q S‖^2 := by
    change inner ℝ (weightedL2BlockTaylor φ r d q g)
      (weightedL2BlockTaylor φ r d q (finiteIsometryAverage _ g)) = _
    rw [weightedL2BlockTaylor_suffix_average hφ hκ hlower]
    exact inner_finiteIsometryAverage_self _ _
  have hrec := norm_sq_le_of_projection_recovery_coefficient ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hε hy horth
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le_coefficient hφ hκ hlower hβ r d q hd g S
  calc
    _ ≤ (1 + ε) * ((3 * d).choose d : ℝ) * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (((3*d).choose d : ℝ) + (((3*d).choose d : ℝ) - 1)/ε) * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ (1 + ε) * ((3 * d).choose d : ℝ) * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (((3*d).choose d : ℝ) + (((3*d).choose d : ℝ) - 1)/ε) * (β d * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring


end KLS.ConstantReduction
end
