import KLS.WeakMatrixInverseIdentity

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A genuine reciprocal determinant and the polynomial adjugate construct
the inverse weak derivative. The ordered inverse derivative is proved from
the matrix product identity; it is never supplied as a premise. -/
theorem hasLocalWeakCoordinateDerivative_matrixInv_of_reciprocalDet
    {A DA : Space n → Matrix (Fin n) (Fin n) ℝ} {r dr : Space n → ℝ} {k : Fin n}
    (hDA : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => A x i j) (fun x => DA x i j) k)
    (hr : HasLocalWeakCoordinateDerivative r dr k)
    (hA : ∀ i j K, IsCompact K → MemLp (fun x => A x i j) ∞ (volume.restrict K))
    (hDAloc : ∀ i j K, IsCompact K → MemLp (fun x => DA x i j) 2 (volume.restrict K))
    (hrb : ∀ K : Set (Space n), IsCompact K → MemLp r ∞ (volume.restrict K))
    (hdrloc : ∀ K : Set (Space n), IsCompact K → MemLp dr 2 (volume.restrict K))
    (hrecip : ∀ᵐ x, r x * (A x).det = 1) :
    (∀ i j K, IsCompact K → MemLp (fun x => (A x)⁻¹ i j) ∞ (volume.restrict K)) ∧
    (∀ i j K, IsCompact K →
      MemLp (fun x => (-((A x)⁻¹ * DA x * (A x)⁻¹)) i j) 2 (volume.restrict K)) ∧
    ∀ i j, HasLocalWeakCoordinateDerivative (fun x => (A x)⁻¹ i j)
      (fun x => (-((A x)⁻¹ * DA x * (A x)⁻¹)) i j) k := by
  have hdet : ∀ᵐ x, (A x).det ≠ 0 := by
    filter_upwards [hrecip] with x hx hz
    rw [hz, mul_zero] at hx
    exact zero_ne_one hx
  have hInv : ∀ᵐ x, (A x)⁻¹ = r x • (A x).adjugate := by
    filter_upwards [hrecip, hdet] with x hx hdx
    have hadj : (A x).det • (A x)⁻¹ = (A x).adjugate := by
      rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hdx, one_smul]
    rw [← hadj, smul_smul, hx, one_smul]
  have hsource (i j : Fin n) : (fun x => r x * (A x).adjugate i j) =ᵐ[volume]
      (fun x => (A x)⁻¹ i j) := by
    filter_upwards [hInv] with x hx
    rw [hx]
    rfl
  have hAdjb (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (A x).adjugate i j) ∞ (volume.restrict K) :=
    memLp_top_matrixAdjugate (fun a b => hA a b K hK) i j
  have hAdjD (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => adjugateDirectionalPolynomial (A x) (DA x) i j) 2 (volume.restrict K) :=
    memLp_two_adjugateDirectionalPolynomial (fun a b => hA a b K hK)
      (fun a b => hDAloc a b K hK) i j
  have hJ (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (A x)⁻¹ i j) ∞ (volume.restrict K) :=
    (memLp_congr_ae (ae_restrict_of_ae (hsource i j))).mp ((hrb K hK).mul (hAdjb i j K hK))
  let DJ (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
    dr x • (A x).adjugate + r x • adjugateDirectionalPolynomial (A x) (DA x)
  have hDJ (i j : Fin n) :
      HasLocalWeakCoordinateDerivative (fun x => (A x)⁻¹ i j) (fun x => DJ x i j) k := by
    have hp := hr.mul (hasLocalWeakCoordinateDerivative_matrixAdjugate hDA hA hDAloc i j)
      (memLp_two_on_compacts_of_top hrb) (memLp_two_on_compacts_of_top (hAdjb i j)) hdrloc (hAdjD i j)
    have hp' : HasLocalWeakCoordinateDerivative (fun x => r x * (A x).adjugate i j)
        (fun x => DJ x i j) k := by
      simpa only [DJ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hp
    exact hp'.congr_ae (hsource i j) Filter.EventuallyEq.rfl
  have hDJloc (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => DJ x i j) 2 (volume.restrict K) := by
    have ha : MemLp (fun x => dr x * (A x).adjugate i j) 2 (volume.restrict K) := by
      have hb : MemLp (fun x => (A x).adjugate i j * dr x) 2 (volume.restrict K) :=
        (hAdjb i j K hK).mul (hdrloc K hK)
      simpa only [mul_comm] using hb
    have hb : MemLp (fun x => r x * adjugateDirectionalPolynomial (A x) (DA x) i j)
        2 (volume.restrict K) := (hrb K hK).mul (hAdjD i j K hK)
    exact ha.add hb
  have he := weak_matrixInverse_derivative_eq hDA hDJ hA hJ hDAloc hDJloc hdet
  have heij (i j : Fin n) : (fun x => DJ x i j) =ᵐ[volume]
      (fun x => (-((A x)⁻¹ * DA x * (A x)⁻¹)) i j) :=
    he.mono fun _ hx => congrArg (fun M => M i j) hx
  refine ⟨hJ, ?_, ?_⟩
  · intro i j K hK
    exact (memLp_congr_ae (ae_restrict_of_ae (heij i j))).mp (hDJloc i j K hK)
  · intro i j
    exact (hDJ i j).congr_ae Filter.EventuallyEq.rfl (heij i j)

end KLS
end
