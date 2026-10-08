import KLS.TiltDerivatives

/-!
# Mixed covariance and cumulant differentiation

These cumulants are actual centered integrals under the normalized tilted
probability law. The fourth cumulant subtracts the three covariance pairings.
Compact support discharges all moment and differentiation hypotheses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section
namespace KLS

theorem memLp_two_continuous_tilted {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f) :
    MemLp f 2 (μ.tilted q) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact integrable_tilted_of_compact_support hμ hq
    (integrable_of_continuous_compact_support_measure hμ (by fun_prop))

def tiltThirdCumulant {n : ℕ} (μ : Measure (Space n))
    (q f g h : Space n → ℝ) : ℝ :=
  tiltAverage μ q (fun x => (f x - tiltAverage μ q f) *
    (g x - tiltAverage μ q g) * (h x - tiltAverage μ q h))

def tiltFourthCumulant {n : ℕ} (μ : Measure (Space n))
    (q f g h s : Space n → ℝ) : ℝ :=
  tiltAverage μ q (fun x => (f x - tiltAverage μ q f) *
    (g x - tiltAverage μ q g) * (h x - tiltAverage μ q h) *
    (s x - tiltAverage μ q s)) -
    covariance f g (μ.tilted q) * covariance h s (μ.tilted q) -
    covariance f h (μ.tilted q) * covariance g s (μ.tilted q) -
    covariance f s (μ.tilted q) * covariance g h (μ.tilted q)

theorem tiltThirdCumulant_eq {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f g h : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    tiltThirdCumulant μ q f g h =
      tiltAverage μ q (fun x => f x * g x * h x) -
      tiltAverage μ q (fun x => f x * g x) * tiltAverage μ q h -
      tiltAverage μ q (fun x => f x * h x) * tiltAverage μ q g -
      tiltAverage μ q (fun x => g x * h x) * tiltAverage μ q f +
      2 * tiltAverage μ q f * tiltAverage μ q g * tiltAverage μ q h := by
  have := tilted_isProbability_of_compact_support hμ hq
  have hi (a : Space n → ℝ) (ha : Continuous a) : Integrable a (μ.tilted q) :=
    integrable_tilted_of_compact_support hμ hq
      (integrable_of_continuous_compact_support_measure hμ ha)
  let A := tiltAverage μ q f
  let B := tiltAverage μ q g
  let C := tiltAverage μ q h
  have hex : (fun x => (f x - A) * (g x - B) * (h x - C)) =
      (fun x => f x * g x * h x - (f x * g x) * C - (f x * h x) * B -
        (g x * h x) * A + f x * (B * C) + g x * (A * C) + h x * (A * B) - A * B * C) := by
    funext x
    ring
  change (∫ x, (f x - A) * (g x - B) * (h x - C) ∂μ.tilted q) = _
  rw [hex]
  simp (disch := exact hi _ (by fun_prop)) only [integral_sub, integral_add,
    integral_mul_const, integral_const, probReal_univ, one_smul]
  dsimp [A, B, C, tiltAverage]
  ring

theorem tiltFourthCumulant_eq {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f g h s : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) (hs : Continuous s) :
    tiltFourthCumulant μ q f g h s =
      tiltAverage μ q (fun x => f x * g x * h x * s x) -
      tiltAverage μ q (fun x => f x * g x * h x) * tiltAverage μ q s -
      tiltAverage μ q (fun x => f x * g x * s x) * tiltAverage μ q h -
      tiltAverage μ q (fun x => f x * h x * s x) * tiltAverage μ q g -
      tiltAverage μ q (fun x => g x * h x * s x) * tiltAverage μ q f -
      tiltAverage μ q (fun x => f x * g x) * tiltAverage μ q (fun x => h x * s x) -
      tiltAverage μ q (fun x => f x * h x) * tiltAverage μ q (fun x => g x * s x) -
      tiltAverage μ q (fun x => f x * s x) * tiltAverage μ q (fun x => g x * h x) +
      2 * (tiltAverage μ q (fun x => f x * g x) * tiltAverage μ q h * tiltAverage μ q s +
        tiltAverage μ q (fun x => f x * h x) * tiltAverage μ q g * tiltAverage μ q s +
        tiltAverage μ q (fun x => f x * s x) * tiltAverage μ q g * tiltAverage μ q h +
        tiltAverage μ q (fun x => g x * h x) * tiltAverage μ q f * tiltAverage μ q s +
        tiltAverage μ q (fun x => g x * s x) * tiltAverage μ q f * tiltAverage μ q h +
        tiltAverage μ q (fun x => h x * s x) * tiltAverage μ q f * tiltAverage μ q g) -
      6 * tiltAverage μ q f * tiltAverage μ q g * tiltAverage μ q h * tiltAverage μ q s := by
  have := tilted_isProbability_of_compact_support hμ hq
  have hi (a : Space n → ℝ) (ha : Continuous a) : Integrable a (μ.tilted q) :=
    integrable_tilted_of_compact_support hμ hq
      (integrable_of_continuous_compact_support_measure hμ ha)
  have h2 (a : Space n → ℝ) (ha : Continuous a) := memLp_two_continuous_tilted hμ hq ha
  rw [tiltFourthCumulant, covariance_eq_sub (h2 _ hf) (h2 _ hg),
    covariance_eq_sub (h2 _ hh) (h2 _ hs), covariance_eq_sub (h2 _ hf) (h2 _ hh),
    covariance_eq_sub (h2 _ hg) (h2 _ hs), covariance_eq_sub (h2 _ hf) (h2 _ hs),
    covariance_eq_sub (h2 _ hg) (h2 _ hh)]
  let A := tiltAverage μ q f
  let B := tiltAverage μ q g
  let C := tiltAverage μ q h
  let D := tiltAverage μ q s
  have hex : (fun x => (f x - A) * (g x - B) * (h x - C) * (s x - D)) =
      (fun x => f x * g x * h x * s x - (f x * g x * h x) * D -
        (f x * g x * s x) * C - (f x * h x * s x) * B - (g x * h x * s x) * A +
        (f x * g x) * (C * D) + (f x * h x) * (B * D) + (f x * s x) * (B * C) +
        (g x * h x) * (A * D) + (g x * s x) * (A * C) + (h x * s x) * (A * B) -
        f x * (B * C * D) - g x * (A * C * D) - h x * (A * B * D) -
        s x * (A * B * C) + A * B * C * D) := by
    funext x
    ring
  change (∫ x, (f x - A) * (g x - B) * (h x - C) * (s x - D) ∂μ.tilted q) - _ - _ - _ = _
  rw [hex]
  simp (disch := exact hi _ (by fun_prop)) only [integral_sub, integral_add,
    integral_mul_const, integral_const, probReal_univ, one_smul]
  dsimp [A, B, C, D, tiltAverage, Pi.mul_apply]
  ring

theorem hasDerivAt_tilted_covariance {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f g s : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hs : Continuous s) (t : ℝ) :
    HasDerivAt (fun u : ℝ => covariance f g (μ.tilted (fun x => q x + u * s x)))
      (tiltThirdCumulant μ (fun x => q x + t * s x) f g s) t := by
  have hd (a : Space n → ℝ) (ha : Continuous a) := hasDerivAt_tiltAverage hμ hq hs
    (integrable_of_continuous_compact_support_measure hμ ha) t
  have heq (u : ℝ) : covariance f g (μ.tilted (fun x => q x + u * s x)) =
      tiltAverage μ (fun x => q x + u * s x) (fun x => f x * g x) -
      tiltAverage μ (fun x => q x + u * s x) f *
      tiltAverage μ (fun x => q x + u * s x) g := by
    have := tilted_isProbability_of_compact_support hμ (q := fun x => q x + u * s x)
      (by fun_prop)
    exact covariance_eq_sub (memLp_two_continuous_tilted hμ (by fun_prop) hf)
      (memLp_two_continuous_tilted hμ (by fun_prop) hg)
  simp_rw [heq]
  rw [tiltThirdCumulant_eq hμ (by fun_prop) hf hg hs]
  convert (hd (fun x => f x * g x) (hf.mul hg)).sub ((hd f hf).mul (hd g hg)) using 1
  ring

theorem hasDerivAt_tiltThirdCumulant {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f g h s : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) (hs : Continuous s) (t : ℝ) :
    HasDerivAt (fun u : ℝ => tiltThirdCumulant μ (fun x => q x + u * s x) f g h)
      (tiltFourthCumulant μ (fun x => q x + t * s x) f g h s) t := by
  have hd (a : Space n → ℝ) (ha : Continuous a) := hasDerivAt_tiltAverage hμ hq hs
    (integrable_of_continuous_compact_support_measure hμ ha) t
  have heq (u : ℝ) := tiltThirdCumulant_eq hμ
    (q := fun x => q x + u * s x) (by fun_prop) hf hg hh
  simp_rw [heq]
  rw [tiltFourthCumulant_eq hμ (by fun_prop) hf hg hh hs]
  convert (((hd (fun x => f x * g x * h x) (by fun_prop)).sub
    ((hd (fun x => f x * g x) (by fun_prop)).mul (hd h hh))).sub
    ((hd (fun x => f x * h x) (by fun_prop)).mul (hd g hg))).sub
    ((hd (fun x => g x * h x) (by fun_prop)).mul (hd f hf)) |>.add
    ((((hd f hf).const_mul 2).mul (hd g hg)).mul (hd h hh)) using 1
  simp only [Pi.mul_apply]
  ring

end KLS
end

#print axioms KLS.tiltThirdCumulant_eq
#print axioms KLS.tiltFourthCumulant_eq
#print axioms KLS.hasDerivAt_tilted_covariance
#print axioms KLS.hasDerivAt_tiltThirdCumulant
