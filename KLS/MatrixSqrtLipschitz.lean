import KLS.MatrixWhitening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.PosDef

/-! Local Lipschitz control of the actual CFC square root on positive definite
real matrices, in the elementwise norm used by the adaptive parameter space. -/
open Matrix Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace KLS

open scoped Matrix.Norms.L2Operator in
lemma matrix_sqrt_continuousOn_posDef {n : ℕ} :
    ContinuousOn (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → _) {A | A.PosDef} :=
  CFC.continuousOn_sqrt.mono (fun _ hA => hA.posSemidef.nonneg)

/-- The Sylvester operator at a positive definite real matrix is injective. -/
lemma posDef_sylvester_injective {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) : Function.Injective (fun D => S * D + D * S) := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hS.isHermitian.eigenvectorUnitary
  have hSdiag : e.symm S = Matrix.diagonal hS.isHermitian.eigenvalues := by
    apply e.symm_apply_eq.mpr
    simpa only [e, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hS.isHermitian.spectral_theorem
  suffices hzero : ∀ D : Matrix (Fin n) (Fin n) ℝ, S * D + D * S = 0 → D = 0 by
    intro X Y hXY
    have h := hzero (X - Y) (by
      calc
        S * (X - Y) + (X - Y) * S = (S * X + X * S) - (S * Y + Y * S) := by noncomm_ring
        _ = 0 := sub_eq_zero.mpr hXY)
    exact sub_eq_zero.mp h
  intro D hD
  apply e.symm.injective
  rw [map_zero]
  have he := congrArg e.symm hD
  simp only [map_add, map_mul, map_zero, hSdiag] at he
  ext i j
  have hij := congrFun (congrFun he i) j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.zero_apply] at hij
  have hpos : 0 < hS.isHermitian.eigenvalues i + hS.isHermitian.eigenvalues j :=
    add_pos (hS.eigenvalues_pos i) (hS.eigenvalues_pos j)
  have hz : (hS.isHermitian.eigenvalues i + hS.isHermitian.eigenvalues j) *
      e.symm D i j = 0 := by nlinarith [hij]
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)

/-- Elementwise matrix multiplication has the dimension-dependent bound needed
for local regularity; no dimension-independent constant is claimed here. -/
lemma matrix_elementwise_norm_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    ‖A * B‖ ≤ ((n : ℝ) + 1) * ‖A‖ * ‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  calc
    ‖(A * B) i j‖ ≤ ∑ k : Fin n, ‖A i k * B k j‖ := by simpa only [Matrix.mul_apply] using norm_sum_le (Finset.univ) (fun k => A i k * B k j)
    _ ≤ ∑ _k : Fin n, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖A‖ * ‖B‖ := by simp [mul_assoc]
    _ ≤ ((n : ℝ) + 1) * ‖A‖ * ‖B‖ := by nlinarith [mul_nonneg (norm_nonneg A) (norm_nonneg B)]

lemma posDef_sylvester_norm_lower {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) : ∃ K : ℝ, 0 < K ∧
      ∀ D : Matrix (Fin n) (Fin n) ℝ, ‖D‖ ≤ K * ‖S * D + D * S‖ := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun D => S * D + D * S
      map_add' := by intros; noncomm_ring
      map_smul' := by intros; simp [smul_add] }
  obtain ⟨K, hK, hL⟩ := L.injective_iff_antilipschitz.mp (posDef_sylvester_injective hS)
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro D
  simpa only [dist_eq_norm, map_zero, sub_zero, L, LinearMap.coe_mk,
    AddHom.coe_mk] using hL.le_mul_dist D 0

/-- The positive square root is locally Lipschitz on the actual positive
 definite cone, with no assumed eigenvalue regularity of a parameterization. -/
theorem locallyLipschitzOn_matrix_sqrt_posDef {n : ℕ} :
    LocallyLipschitzOn {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef} CFC.sqrt := by
  intro A hA
  let S := CFC.sqrt A
  have hS : S.PosDef := (CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)
  obtain ⟨K, hK, hlower⟩ := posDef_sylvester_norm_lower hS
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  let ε : ℝ := 1 / (4 * K * m)
  have hε : 0 < ε := by positivity
  have hnear : {B : Matrix (Fin n) (Fin n) ℝ | ‖CFC.sqrt B - S‖ < ε} ∈
      𝓝[{B | B.PosDef}] A := by
    have hc : ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ =>
        ‖CFC.sqrt B - S‖) {B | B.PosDef} A :=
      (matrix_sqrt_continuousOn_posDef A hA).sub_const S |>.norm
    have hz : ‖CFC.sqrt A - S‖ = 0 := by simp [S]
    exact hc (Iio_mem_nhds (by simpa only [hz] using hε))
  refine ⟨Real.toNNReal (2 * K),
    {B | B.PosDef} ∩ {B | ‖CFC.sqrt B - S‖ < ε},
    inter_mem self_mem_nhdsWithin hnear, LipschitzOnWith.of_dist_le' ?_⟩
  intro B hB C hC
  let T := CFC.sqrt B
  let U := CFC.sqrt C
  let D := T - U
  have hT : T * T = B := CFC.sqrt_mul_sqrt_self B (show B.PosDef from hB.1).posSemidef.nonneg
  have hU : U * U = C := CFC.sqrt_mul_sqrt_self C (show C.PosDef from hC.1).posSemidef.nonneg
  have hid : S * D + D * S = (B - C) + (S - T) * D + D * (S - U) := by
    rw [← hT, ← hU]
    dsimp [D]
    noncomm_ring
  have hST : ‖S - T‖ ≤ ε := by rw [norm_sub_rev]; exact hB.2.le
  have hSU : ‖S - U‖ ≤ ε := by rw [norm_sub_rev]; exact hC.2.le
  have hb : ‖D‖ ≤ K * (‖B - C‖ + m * ε * ‖D‖ + m * ‖D‖ * ε) := by
    calc
      ‖D‖ ≤ K * ‖S * D + D * S‖ := hlower D
      _ = K * ‖(B - C) + (S - T) * D + D * (S - U)‖ := by rw [hid]
      _ ≤ K * (‖B - C‖ + ‖(S - T) * D‖ + ‖D * (S - U)‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K * (‖B - C‖ + m * ε * ‖D‖ + m * ‖D‖ * ε) := by
        gcongr
        · exact (matrix_elementwise_norm_mul_le _ _).trans (by gcongr)
        · exact (matrix_elementwise_norm_mul_le _ _).trans (by gcongr)
  have hcoef : K * m * ε = 1 / 4 := by
    dsimp [ε]
    field_simp
  have herr : K * (‖B - C‖ + m * ε * ‖D‖ + m * ‖D‖ * ε) =
      K * ‖B - C‖ + ‖D‖ / 2 := by
    calc
      _ = K * ‖B - C‖ + 2 * (K * m * ε) * ‖D‖ := by ring
      _ = _ := by rw [hcoef]; ring
  rw [herr] at hb
  simp only [dist_eq_norm]
  change ‖D‖ ≤ 2 * K * ‖B - C‖
  linarith

end KLS
end
