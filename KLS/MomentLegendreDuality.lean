import KLS.MomentVariationalAttainment
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Genuine Legendre biconjugation for normalized convex potentials

The supporting affine functions are obtained from mathlib's geometric
Hahn--Banach theorem. They prove an actual biconjugation statement for the
extended transform used by the variational energy.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

/-- The actual finite domain of the extended Legendre transform. -/
def momentLegendreDomain {n : ℕ} (φ : Space n → ℝ) : Set (Space n) :=
  {y | normalizedLegendreTransform φ y ≠ ∞}

theorem normalizedLegendreTransform_zero_of_nonneg {n : ℕ} {φ : Space n → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) : normalizedLegendreTransform φ 0 = 0 := by
  apply le_antisymm _ bot_le
  change normalizedLegendreTransform φ 0 ≤ (0 : ℝ≥0∞)
  rw [← ENNReal.ofReal_zero]
  apply (normalizedLegendreTransform_le_ofReal_iff φ 0 (le_refl 0)).mpr
  intro x
  simpa only [inner_zero_left, zero_sub, neg_nonpos] using hφ x

theorem momentLegendreDomain_nonempty {n : ℕ} {φ : Space n → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) : (momentLegendreDomain φ).Nonempty := by
  refine ⟨0, ?_⟩
  change normalizedLegendreTransform φ 0 ≠ ∞
  rw [normalizedLegendreTransform_zero_of_nonneg hφ]
  exact ENNReal.zero_ne_top

/-- The finite Legendre affine minorants have exactly the original potential
as their least upper bound at every point. -/
theorem normalizedLegendre_biconjugate_isLUB {n : ℕ} {φ : Space n → ℝ}
    (hcont : Continuous φ) (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0)
    (x : Space n) :
    IsLUB (Set.range (fun y : momentLegendreDomain φ =>
      inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal)) (φ x) := by
  constructor
  · rintro a ⟨y, rfl⟩
    have h := normalizedLegendreTransform_young φ y.2 x
    linarith
  · intro a ha
    by_contra h
    have hax : a < φ x := lt_of_not_ge h
    let b : ℝ := (a + φ x) / 2
    have hab : a < b := by dsimp [b]; linarith
    have hbx : b < φ x := by dsimp [b]; linarith
    obtain ⟨l, c, hminor, htouch⟩ := ConvexOn.exists_affine_le_of_lt
      (𝕜 := ℝ) (s := Set.univ) (x := x) (a := b) (mem_univ x) hbx isClosed_univ
      hcont.continuousOn.lowerSemicontinuousOn hconvex
    have hminor' (z : Space n) : l z + c ≤ φ z := by
      simpa using hminor ⟨z, mem_univ z⟩
    have htouch' : l x + c = b := by simpa using htouch
    have hc : 0 ≤ -c := by
      have h₀ := hminor' 0
      simp only [map_zero, zero_add, hzero] at h₀
      linarith
    let y : Space n := (InnerProductSpace.toDual ℝ (Space n)).symm l
    have hyinner (z : Space n) : inner ℝ y z = l z :=
      InnerProductSpace.toDual_symm_apply
    have hdual : normalizedLegendreTransform φ y ≤ ENNReal.ofReal (-c) := by
      apply (normalizedLegendreTransform_le_ofReal_iff φ y hc).mpr
      intro z
      rw [hyinner]
      have h := hminor' z
      linarith
    have hyfinite : normalizedLegendreTransform φ y ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdual
    have hreal : (normalizedLegendreTransform φ y).toReal ≤ -c :=
      ENNReal.toReal_le_of_le_ofReal hc hdual
    have hay := ha (Set.mem_range_self (⟨y, hyfinite⟩ : momentLegendreDomain φ))
    change inner ℝ y x - (normalizedLegendreTransform φ y).toReal ≤ a at hay
    rw [hyinner] at hay
    linarith

theorem normalizedLegendre_biconjugate_eq {n : ℕ} {φ : Space n → ℝ}
    (hcont : Continuous φ) (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0)
    (hnonneg : ∀ x, 0 ≤ φ x) (x : Space n) :
    sSup (Set.range (fun y : momentLegendreDomain φ =>
      inner ℝ y.1 x - (normalizedLegendreTransform φ y.1).toReal)) = φ x := by
  apply (normalizedLegendre_biconjugate_isLUB hcont hconvex hzero x).csSup_eq
  obtain ⟨y, hy⟩ := momentLegendreDomain_nonempty hnonneg
  exact ⟨_, Set.mem_range_self (⟨y, hy⟩ : momentLegendreDomain φ)⟩

/-- The true finite conjugate domain of an `L`-Lipschitz normalized potential
is contained in the closed Euclidean ball of radius `L`. -/
theorem norm_le_of_mem_momentLegendreDomain {n : ℕ} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hzero : φ 0 = 0)
    {y : Space n} (hy : y ∈ momentLegendreDomain φ) : ‖y‖ ≤ L := by
  by_contra h
  have hnorm : (L : ℝ) < ‖y‖ := lt_of_not_ge h
  have hpos : 0 < ‖y‖ := lt_of_le_of_lt L.property hnorm
  let D : ℝ := (normalizedLegendreTransform φ y).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  let t : ℝ := (D + 1) / (‖y‖ * (‖y‖ - L))
  have hden : 0 < ‖y‖ * (‖y‖ - L) := mul_pos hpos (sub_pos.mpr hnorm)
  have ht : 0 < t := div_pos (by linarith) hden
  have htden : t * (‖y‖ * (‖y‖ - L)) = D + 1 := div_mul_cancel₀ _ hden.ne'
  have hyoung := normalizedLegendreTransform_young φ hy (t • y)
  have hupper := le_trans (le_abs_self (φ (t • y)))
    (normalizedConvexLipschitzPotentials_pointwise_bound hLip hzero (t • y))
  rw [inner_smul_right, real_inner_self_eq_norm_sq] at hyoung
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hupper
  change t * ‖y‖ ^ 2 ≤ φ (t • y) + D at hyoung
  nlinarith

end KLS
end

#print axioms KLS.normalizedLegendre_biconjugate_isLUB
#print axioms KLS.normalizedLegendre_biconjugate_eq
#print axioms KLS.norm_le_of_mem_momentLegendreDomain
