import KLS.AffinePotentialCutoff
import KLS.MomentMapIntegration
import KLS.AffineMomentMapStein
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Elementary affine normalization by a maximal determinant simplex.
The constants need only depend on dimension, so no John ellipsoid theorem
is imported or assumed. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped Topology NNReal ENNReal BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

def sectionColumnMatrix (a : Space n) (q : Fin n → Space n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (q j - a) i

theorem continuous_sectionColumnMatrix (a : Space n) :
    Continuous (sectionColumnMatrix a) := by
  unfold sectionColumnMatrix
  fun_prop

theorem sectionColumnMatrix_update (a : Space n) (q : Fin n → Space n)
    (j : Fin n) (x : Space n) :
    sectionColumnMatrix a (Function.update q j x) =
      (sectionColumnMatrix a q).updateCol j (fun i => (x - a) i) := by
  ext i k
  by_cases hk : k = j
  · subst k
    simp [sectionColumnMatrix]
  · simp [sectionColumnMatrix, Function.update_of_ne hk, Matrix.updateCol_ne hk]

theorem sectionColumnMatrix_coordinate_simplex (a : Space n) (r : ℝ) :
    sectionColumnMatrix a (fun j => a + r • MomentMap.coordinateVector j) = r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp [sectionColumnMatrix, MomentMap.coordinateVector, PiLp.single_apply, Matrix.one_apply]

/-- A maximal determinant tuple exists, is invertible, and controls every
coordinate of every point of the compact set in its resulting basis. -/
theorem exists_maximal_simplex_coordinates {K : Set (Space n)} (hK : IsCompact K)
    {a : Space n} (ha : a ∈ interior K) :
    ∃ q : Fin n → Space n, (∀ j, q j ∈ K) ∧
      (sectionColumnMatrix a q).det ≠ 0 ∧
      ∀ x ∈ K, ∀ i : Fin n,
        |matrixAction (sectionColumnMatrix a q)⁻¹ (x - a) i| ≤ 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let q₀ : Fin n → Space n := fun j => a + r • MomentMap.coordinateVector j
  have hq₀ : ∀ j, q₀ j ∈ K := by
    intro j
    apply hball
    have he : ‖MomentMap.coordinateVector j‖ = 1 := by simp [MomentMap.coordinateVector]
    simpa only [q₀, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, he, mul_one] using (by dsimp [r]; linarith : r < ε)
  let Q : Set (Fin n → Space n) := Set.pi univ (fun _ => K)
  have hQc : IsCompact Q := isCompact_univ_pi (fun _ => hK)
  have hq₀Q : q₀ ∈ Q := by simpa only [Q, Set.mem_pi, mem_univ, forall_const] using hq₀
  have hdetcont : Continuous (fun q : Fin n → Space n => |(sectionColumnMatrix a q).det|) :=
    (continuous_sectionColumnMatrix a).matrix_det.abs
  obtain ⟨q, hqQ, hmax⟩ := hQc.exists_isMaxOn ⟨q₀, hq₀Q⟩ hdetcont.continuousOn
  have hq : ∀ j, q j ∈ K := by simpa only [Q, Set.mem_pi, mem_univ, forall_const] using hqQ
  have hdet₀ : (sectionColumnMatrix a q₀).det = r ^ n := by
    dsimp [q₀]
    rw [sectionColumnMatrix_coordinate_simplex, Matrix.det_smul]
    simp
  have hA : (sectionColumnMatrix a q).det ≠ 0 := by
    have hm : |(sectionColumnMatrix a q₀).det| ≤ |(sectionColumnMatrix a q).det| := hmax hq₀Q
    rw [hdet₀, abs_of_pos (pow_pos hr _)] at hm
    exact (abs_pos.mp ((pow_pos hr n).trans_le hm))
  refine ⟨q, hq, hA, ?_⟩
  intro x hx i
  have hqi : Function.update q i x ∈ Q := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using hx
    · simpa [Function.update_of_ne hji] using hq j
  have hm : |(sectionColumnMatrix a (Function.update q i x)).det| ≤ |(sectionColumnMatrix a q).det| := hmax hqi
  rw [sectionColumnMatrix_update] at hm
  have hcr := congrFun ((sectionColumnMatrix a q).det_smul_inv_mulVec_eq_cramer
    (fun j => (x - a) j) (isUnit_iff_ne_zero.mpr hA)) i
  have hcr' : (sectionColumnMatrix a q).det *
      matrixAction (sectionColumnMatrix a q)⁻¹ (x - a) i =
      ((sectionColumnMatrix a q).updateCol i (fun j => (x - a) j)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
      matrixAction_apply, Matrix.mulVec, dotProduct] using hcr
  rw [← hcr', abs_mul] at hm
  exact (mul_le_mul_iff_right₀ (abs_pos.mpr hA)).mp (by simpa using hm)

def coordinateSimplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

theorem sum_smul_coordinateVector (x : Space n) :
    (∑ j : Fin n, x j • MomentMap.coordinateVector j) = x := by
  ext i
  simp [MomentMap.coordinateVector, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

theorem coordinateSimplex_subset_convex {S : Set (Space n)} (hS : Convex ℝ S)
    (hzero : (0 : Space n) ∈ S) (hbasis : ∀ i, MomentMap.coordinateVector i ∈ S) :
    coordinateSimplex n ⊆ S := by
  intro x hx
  let w : Option (Fin n) → ℝ := fun i => match i with
    | none => 1 - ∑ j, x j
    | some j => x j
  let z : Option (Fin n) → Space n := fun i => match i with
    | none => 0
    | some j => MomentMap.coordinateVector j
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hx.2
    | some j => exact hx.1 j
  have hsum : ∑ i : Option (Fin n), w i = 1 := by
    simp only [Fintype.sum_option, w]
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), z i ∈ S := by
    intro i _
    cases i with
    | none => exact hzero
    | some j => exact hbasis j
  have hh := hS.sum_mem hw hsum hz
  simpa only [Fintype.sum_option, z, w, smul_zero, zero_add,
    sum_smul_coordinateVector] using hh

theorem sectionColumnMatrix_apply_coordinateVector (a : Space n) (q : Fin n → Space n)
    (j : Fin n) : matrixAction (sectionColumnMatrix a q) (MomentMap.coordinateVector j) =
      q j - a := by
  ext i
  simp [matrixAction_apply, sectionColumnMatrix, MomentMap.coordinateVector, PiLp.single_apply]

theorem section_inverse_matrixAction_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.det ≠ 0)
    (x : Space n) : matrixAction A⁻¹ (matrixAction A x) = x := by
  rw [← MomentMap.matrixAction_mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
  ext i
  simp [matrixAction_apply, Matrix.one_apply]

/-- An actual affine equivalence places a simplex inside the convex body and
the whole body inside the coordinate cube. -/
theorem exists_simplex_box_affine_normalization {K : Set (Space n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      coordinateSimplex n ⊆ e '' K ∧ e '' K ⊆ {x | ∀ i, |x i| ≤ 1} := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨q, hq, hA, hcoords⟩ := exists_maximal_simplex_coordinates hK ha
  let A := sectionColumnMatrix a q
  have hAi : A⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero hA
  let e := affineMatrixEquiv A⁻¹ (-matrixAction A⁻¹ a) hAi
  have he (x : Space n) : e x = matrixAction A⁻¹ (x - a) := by
    change matrixAction A⁻¹ x - matrixAction A⁻¹ a = matrixAction A⁻¹ (x - a)
    exact ((matrixAction A⁻¹).map_sub x a).symm
  have hzero : (0 : Space n) ∈ e '' K := by
    refine ⟨a, interior_subset ha, ?_⟩
    rw [he, sub_self, map_zero]
  have hbasis : ∀ j, MomentMap.coordinateVector j ∈ e '' K := by
    intro j
    refine ⟨q j, hq j, ?_⟩
    rw [he, ← sectionColumnMatrix_apply_coordinateVector]
    exact section_inverse_matrixAction_apply hA _
  refine ⟨e, coordinateSimplex_subset_convex
    (Convex.affine_image e.toAffineEquiv.toAffineMap hc) hzero hbasis, ?_⟩
  rintro x ⟨y, hy, rfl⟩ i
  rw [he]
  exact hcoords y hy i

theorem norm_le_sum_abs_coordinates (x : Space n) : ‖x‖ ≤ ∑ i : Fin n, |x i| := by
  calc
    ‖x‖ = ‖∑ i : Fin n, x i • MomentMap.coordinateVector i‖ := by
      rw [sum_smul_coordinateVector]
    _ ≤ ∑ i : Fin n, ‖x i • MomentMap.coordinateVector i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |x i| := by
      simp [norm_smul, MomentMap.coordinateVector]

def coordinateSimplexCenter (n : ℕ) : Space n :=
  WithLp.toLp 2 (fun _ => ((n : ℝ) + 1)⁻¹)

def coordinateSimplexRadius (n : ℕ) : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹

theorem coordinateSimplexRadius_pos (n : ℕ) : 0 < coordinateSimplexRadius n := by
  unfold coordinateSimplexRadius
  positivity

theorem closedBall_subset_coordinateSimplex (n : ℕ) :
    closedBall (coordinateSimplexCenter n) (coordinateSimplexRadius n) ⊆ coordinateSimplex n := by
  intro y hy
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hmone : 1 ≤ m := by dsimp [m]; linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hrc : (m ^ 2)⁻¹ ≤ m⁻¹ := by
    apply inv_anti₀ hm
    nlinarith
  have hdist : ‖y - coordinateSimplexCenter n‖ ≤ (m ^ 2)⁻¹ := hy
  have hcoord (i : Fin n) : |y i - m⁻¹| ≤ (m ^ 2)⁻¹ := by
    have hh := (PiLp.norm_apply_le (y - coordinateSimplexCenter n) i).trans hdist
    change ‖y i - m⁻¹‖ ≤ (m ^ 2)⁻¹ at hh
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨?_, ?_⟩
  · intro i
    have hlow := (abs_le.mp (hcoord i)).1
    linarith
  · have hs : (∑ i : Fin n, y i) ≤ (n : ℝ) * (m⁻¹ + (m ^ 2)⁻¹) := by
      calc
        _ ≤ ∑ _i : Fin n, (m⁻¹ + (m ^ 2)⁻¹) := Finset.sum_le_sum (fun i _ => by
          have hu := (abs_le.mp (hcoord i)).2
          linarith)
        _ = _ := by simp; ring
    have heq : (n : ℝ) * (m⁻¹ + (m ^ 2)⁻¹) = 1 - (m ^ 2)⁻¹ := by
      have hnm : (n : ℝ) = m - 1 := by dsimp [m]; ring
      rw [hnm]
      field_simp
      ring
    rw [heq] at hs
    exact hs.trans (sub_le_self _ (by positivity))

/-- A dimension-only bound for the norm relative to the simplex center. -/
theorem norm_sub_coordinateSimplexCenter_le {x : Space n}
    (hx : ∀ i, |x i| ≤ 1) : ‖x - coordinateSimplexCenter n‖ ≤ 2 * (n : ℝ) := by
  have hcpos : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hcle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  calc
    _ ≤ ∑ i : Fin n, |(x - coordinateSimplexCenter n) i| := norm_le_sum_abs_coordinates _
    _ ≤ ∑ _i : Fin n, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      change |x i - ((n : ℝ) + 1)⁻¹| ≤ 2
      calc
        _ ≤ |x i| + |((n : ℝ) + 1)⁻¹| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (hx i) (by rwa [abs_of_nonneg hcpos])
        _ = 2 := by norm_num
    _ = _ := by simp [mul_comm]

theorem section_matrixAction_smul_one (r : ℝ) (x : Space n) :
    matrixAction (r • (1 : Matrix (Fin n) (Fin n) ℝ)) x = r • x := by
  ext i
  simp [matrixAction_apply, Matrix.smul_apply, Matrix.one_apply]

/-- Actual affine normalization of every compact convex body with nonempty
interior. The deliberately nonsharp outer radius is explicit and depends only
on the dimension. -/
theorem exists_ball_affine_normalization {K : Set (Space n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      closedBall 0 1 ⊆ e '' K ∧
      e '' K ⊆ closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) := by
  obtain ⟨e, hinner, houter⟩ := exists_simplex_box_affine_normalization hK hc hne
  let r := coordinateSimplexRadius n
  let c := coordinateSimplexCenter n
  have hr : 0 < r := coordinateSimplexRadius_pos n
  have hA : (r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hr.ne']
  let f := affineMatrixEquiv (r⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) (-r⁻¹ • c) hA
  have hf (x : Space n) : f x = r⁻¹ • (x - c) := by
    simp only [f, affineMatrixEquiv_apply, affineMatrixMap_apply,
      section_matrixAction_smul_one]
    module
  refine ⟨e.trans f, ?_, ?_⟩
  · intro x hx
    have hxnorm : ‖x‖ ≤ 1 := by simpa using hx
    have hyball : c + r • x ∈ closedBall c r := by
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    obtain ⟨y, hy, heq⟩ := hinner (closedBall_subset_coordinateSimplex n hyball)
    refine ⟨y, hy, ?_⟩
    change f (e y) = x
    rw [heq, hf, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rintro x ⟨y, hy, rfl⟩
    change f (e y) ∈ closedBall 0 _
    have hnorm := norm_sub_coordinateSimplexCenter_le (houter (mem_image_of_mem e hy))
    rw [mem_closedBall, dist_zero_right, hf, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    have hrinv : r⁻¹ = ((n : ℝ) + 1) ^ 2 := by simp [r, coordinateSimplexRadius]
    rw [hrinv]
    have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [c] at *
    nlinarith [sq_nonneg ((n : ℝ) + 1)]

end KLS
end

#print axioms KLS.exists_maximal_simplex_coordinates
#print axioms KLS.exists_simplex_box_affine_normalization
#print axioms KLS.exists_ball_affine_normalization
