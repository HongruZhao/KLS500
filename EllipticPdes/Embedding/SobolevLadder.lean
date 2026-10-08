/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.GagliardoNirenberg

/-!
# The Sobolev ladder

One Gagliardo-Nirenberg-Sobolev rung raises the exponent from `p` to `p'` with
`1/p' = 1/p - 1/d`. Iterating it `s` times from `p₀` lands on `1/p₀ - s/d`, the exponent of
Guo, *Partial Differential Equations*, Theorem IV.2.3, and `EllipticPdes.Embedding.morrey_ball`
asks for an exponent above `d`.

The iteration is stated once, over an abstract conclusion `G s q x`, in
`EllipticPdes.Embedding.ladder_induction`. It contains all of the exponent arithmetic: the
reciprocal `1/p₀ - s/d` stays positive up to the top rung, a target at or above the conjugate
exponent is reached by one rung from the rung below, and a target below it is reached by one
rung from `p₀` that overshoots it, after which the exponent is lowered onto the target.

## Families

The family that pays for the rungs is an index type `ι`, a function `F i` for each index, a
successor `nxt i k` naming a weak `k`-derivative of `F i`, and a depth `dep i` with
`dep (nxt i k) ≤ dep i + 1`. The supply is `m`: indices of depth below `m` have their weak
gradient in the family, and running `s` rungs on `F i` consumes `s` of the orders above `dep i`,
so the conclusion is for those `i` with `dep i + s ≤ m`. A family closed at every order is the
case `dep = 0`.

`EllipticPdes.Embedding.FamilyBound` states the conclusion with its constant: one constant,
chosen before the family, takes a uniform `L^{p₀}` bound over the data domain to an `Lq` bound on
the target domain. `EllipticPdes.Embedding.exists_const_ladder` proves it for any family of
domains on which a rung is available. A ball inside a ball, with the cutoff of the whole-space
inequality shrinking the ball at each rung, is the case of this file; a bounded domain with `C¹`
boundary, where an extension operator supplies the cutoff once, is the case of
`EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`.

## Main declarations

* `EllipticPdes.Embedding.ladder_induction`: the induction on the rung.
* `EllipticPdes.Embedding.exists_const_ladder`: the ladder with its constant, over any domains.
* `EllipticPdes.Embedding.memLp_of_gradClosed_general`: the ladder on balls from a general base
  exponent.
* `EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep`: the ladder from `L²` run to
  `L^{2d}`, which is what `EllipticPdes.Embedding.morrey_ball` consumes.

## References

Guo, *Partial Differential Equations*, Theorem IV.2.3.
Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1 and §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-! ### Exponent arithmetic -/

/-- A positive real is the reciprocal of a nonnegative real. -/
theorem exists_nnreal_inv_eq {t : ℝ} (ht : 0 < t) : ∃ Q : ℝ≥0, (Q : ℝ)⁻¹ = t :=
  ⟨t⁻¹.toNNReal, by rw [Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), inv_inv]⟩

/-- Reciprocals reverse the order of positive exponents. -/
theorem le_of_coe_inv_le_coe_inv {p Q : ℝ≥0} (hp : 0 < p) (hQ : 0 < Q)
    (h : (Q : ℝ)⁻¹ ≤ (p : ℝ)⁻¹) : p ≤ Q := by
  rw [← NNReal.coe_le_coe]
  exact (inv_le_inv₀ (NNReal.coe_pos.mpr hQ) (NNReal.coe_pos.mpr hp)).mp h

/-- **The exponent of a rung.** If `p₀ s < d` then `1/p₀ - s/d` is the reciprocal of an exponent
`Q ≥ p₀`. -/
theorem exists_rung_exponent {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (hd : 0 < d) {s : ℕ}
    (hsd : (p₀ : ℝ) * s < d) :
    ∃ Q : ℝ≥0, p₀ ≤ Q ∧ (Q : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - s * (d : ℝ)⁻¹ := by
  have hp : 0 < p₀ := hp₀.trans_lt' one_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h : (s : ℝ) * (d : ℝ)⁻¹ < (p₀ : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ hd' (NNReal.coe_pos.mpr hp)]
    linarith
  obtain ⟨Q, hQ⟩ := exists_nnreal_inv_eq (sub_pos.mpr h)
  have hQpos : 0 < Q := NNReal.coe_pos.mp (inv_pos.mp (hQ ▸ sub_pos.mpr h))
  refine ⟨Q, le_of_coe_inv_le_coe_inv hp hQpos ?_, hQ⟩
  rw [hQ]
  have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
  linarith

/-- **Exponents of a rung onto a target at or above the conjugate exponent.** The rung below has
exponent `Q`, with `1/Q = 1/p₀ - s/d`, and the inequality is applied at `p ≤ Q` with
`1/q = 1/p - 1/d`. -/
theorem exists_ladder_exponents {p₀ q : ℝ≥0} (hp₀ : 1 ≤ p₀) {s : ℕ} (hd : 0 < d)
    (hsd : (p₀ : ℝ) * (s + 1) ≤ d) (hpq : p₀ ≤ q)
    (hqs : (p₀ : ℝ)⁻¹ - (s + 1) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹)
    (hu : (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1) :
    ∃ Q p : ℝ≥0, p₀ ≤ Q ∧ (Q : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - s * (d : ℝ)⁻¹ ∧ 1 ≤ p ∧ p ≤ Q ∧
      (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
  have hp₀0 : (0 : ℝ) < p₀ := by exact_mod_cast hp₀.trans_lt' one_pos
  obtain ⟨Q, hp₀Q, hQ⟩ := exists_rung_exponent hp₀ hd (s := s) (by nlinarith)
  have hu0 : 0 < (q : ℝ)⁻¹ + (d : ℝ)⁻¹ := by
    have : (0 : ℝ) < q := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    positivity
  obtain ⟨p, hp⟩ := exists_nnreal_inv_eq hu0
  have hppos : 0 < p := NNReal.coe_pos.mp (inv_pos.mp (hp ▸ hu0))
  refine ⟨Q, p, hp₀Q, hQ, le_of_coe_inv_le_coe_inv (p := 1) one_pos hppos
    (by simpa [hp] using hu), le_of_coe_inv_le_coe_inv hppos
    ((hp₀.trans_lt' one_pos).trans_le hp₀Q) ?_, by rw [hp]; ring⟩
  rw [hQ, hp]
  linarith

/-- **Exponent of a rung that overshoots.** If the target `q ≥ p₀` lies below the conjugate
exponent, one rung from `p₀` lands on an exponent `P ≥ q`. -/
theorem exists_overshoot_exponent {p₀ q : ℝ≥0} (hp₀ : 1 ≤ p₀) (hd : 1 < d) (hpq : p₀ ≤ q)
    (hu : ¬ (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1) :
    ∃ P : ℝ≥0, q ≤ P ∧ (P : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
  have hp : 0 < p₀ := hp₀.trans_lt' one_pos
  have hd2 : (d : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ two_pos (by exact_mod_cast hd)
  have hqp : (q : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := inv_anti₀ (NNReal.coe_pos.mpr hp) (by exact_mod_cast hpq)
  have hp1 : (p₀ : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp₀)
  have hpos : 0 < (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ := by linarith [not_le.mp hu]
  obtain ⟨P, hP⟩ := exists_nnreal_inv_eq hpos
  have hPpos : 0 < P := NNReal.coe_pos.mp (inv_pos.mp (hP ▸ hpos))
  exact ⟨P, le_of_coe_inv_le_coe_inv (hp.trans_le hpq) hPpos
    (by rw [hP]; linarith [not_le.mp hu]), hP⟩

/-! ### The induction -/

/-- **The Sobolev ladder as an induction.** `G s q x` states the conclusion at rung `s`, at
exponent `q` and at the position `x`, where a position `x` with `V x` shrinks to `shrink x`. The
bottom rung is `G 0 p₀`. A step consumes `G s Q (shrink x)` and one Gagliardo-Nirenberg-Sobolev
rung with `p ≤ Q` and `1/q = 1/p - 1/d`. A target below the conjugate exponent is reached from
`G 0 p₀` by one rung that overshoots it. The conclusion is `G s q x` for every `q ≥ p₀` with
`1/q ≥ 1/p₀ - s/d` and `p₀ s ≤ d`, in dimension `d > 1` as soon as `s > 0`. -/
theorem ladder_induction {X : Type*} (G : ℕ → ℝ≥0 → X → Prop) (V : X → Prop) (shrink : X → X)
    {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (hV : ∀ x, V x → V (shrink x))
    (base : ∀ x, V x → G 0 p₀ x)
    (step : ∀ (s : ℕ) x, V x → ∀ p Q q : ℝ≥0, 1 ≤ p → p ≤ Q →
      (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ → G s Q (shrink x) → G (s + 1) q x)
    (overshoot : ∀ (s : ℕ) x, V x → ∀ P q : ℝ≥0, p₀ ≤ q → q ≤ P →
      (P : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ → G 0 p₀ (shrink x) → G (s + 1) q x) :
    ∀ (s : ℕ) {q : ℝ≥0} (x : X), V x → (0 < s → 1 < d) → (p₀ : ℝ) * s ≤ d → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - s * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → G s q x := by
  intro s
  induction s with
  | zero =>
    intro q x hx _ _ hpq hqs
    obtain rfl : q = p₀ := le_antisymm (le_of_coe_inv_le_coe_inv ((hp₀.trans_lt' one_pos).trans_le
      hpq) (hp₀.trans_lt' one_pos) (by simpa using hqs)) hpq
    exact base x hx
  | succ s ih =>
    intro q x hx hds hsd hpq hqs
    have hd := hds s.succ_pos
    push_cast at hsd hqs
    by_cases hu : (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1
    · obtain ⟨Q, p, hp₀Q, hQ, hp1, hpQ, hqp⟩ :=
        exists_ladder_exponents hp₀ (by omega) hsd hpq hqs hu
      refine step s x hx p Q q hp1 hpQ hqp (ih (shrink x) (hV x hx) (fun _ => hd) ?_ hp₀Q hQ.ge)
      have : (0 : ℝ) ≤ p₀ := p₀.2
      nlinarith
    · obtain ⟨P, hqP, hP⟩ := exists_overshoot_exponent hp₀ hd hpq hu
      exact overshoot s x hx P q hpq hqP hP (base _ (hV x hx))

/-! ### The ladder with its constant -/

/-- **A rung is available from `D` to `D'`.** For every `1 ≤ p ≤ q` and every `p'` with
`1/p' = 1/p - 1/d`, a rung with data at `q` has some constant. -/
def IsSobolevRung (d : ℕ) (D D' : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ p q p' : ℝ≥0, 1 ≤ p → p ≤ q → (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ →
    ∃ K : ℝ≥0, RungBound D D' q p' K

/-- **Uniform bound along a family.** For every family `F` closed under weak differentiation as
far as the supply `m`, with weak gradients over `D₀`, every member of depth at most `m` in
`L^{p₀}(D₀)` and the `L^{p₀}(D₀)` seminorms of the members of depth at most `m` bounded by `M`,
the member `F i` with `dep i + s ≤ m` is in `Lq(D)` with seminorm at most `K * M`. -/
def FamilyBound (ι : Type*) (D₀ D : Set (EuclideanSpace ℝ (Fin d))) (p₀ q : ℝ≥0) (s : ℕ)
    (K : ℝ≥0) : Prop :=
  ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι} {dep : ι → ℕ} {m : ℕ},
    (∀ i k, dep (nxt i k) ≤ dep i + 1) →
    (∀ i, dep i < m → HasWeakGradOn D₀ (F i) (fun k => F (nxt i k))) →
    (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict D₀)) →
    ∀ M : ℝ≥0∞, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict D₀) ≤ M) →
    ∀ i, dep i + s ≤ m →
      MemLp (F i) q (volume.restrict D) ∧ eLpNorm (F i) q (volume.restrict D) ≤ (K : ℝ≥0∞) * M

variable {D₀ D D' : Set (EuclideanSpace ℝ (Fin d))} {p₀ q Q : ℝ≥0}

/-- The bottom rung of a family bound is the hypothesis, restricted to a smaller domain. -/
theorem FamilyBound.zero {ι : Type*} (h : D ⊆ D₀) : FamilyBound ι D₀ D p₀ p₀ 0 1 := by
  intro F nxt dep m _ _ hmem M hM i hi
  refine ⟨(hmem i (by omega)).mono_measure (Measure.restrict_mono h le_rfl), ?_⟩
  rw [ENNReal.coe_one, one_mul]
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl)).trans (hM i (by omega))

/-- One rung extends a family bound at the rung below from `D'` to `D`, at the cost of the
constants of the rung and of the `d + 1` members it consumes. -/
theorem FamilyBound.rung {ι : Type*} {s : ℕ} {K Kr : ℝ≥0} (hD' : D' ⊆ D₀)
    (hr : RungBound D' D Q q Kr)
    (h : FamilyBound ι D₀ D' p₀ Q s K) :
    FamilyBound ι D₀ D p₀ q (s + 1) (Kr * ((d + 1) * K)) := by
  intro F nxt dep m hdep hgrad hmem M hM i hi
  have hQ : ∀ j, dep j + s ≤ m → MemLp (F j) Q (volume.restrict D') ∧
      eLpNorm (F j) Q (volume.restrict D') ≤ (K : ℝ≥0∞) * M :=
    fun j hj => h hdep hgrad hmem M hM j hj
  obtain ⟨hmemq, hbd⟩ := hr (F i) (fun k => F (nxt i k)) (hQ i (by omega)).1
    (fun k => (hQ (nxt i k) (by have := hdep i k; omega)).1)
    ((hgrad i (by omega)).mono hD')
  refine ⟨hmemq, hbd.trans ?_⟩
  push_cast
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_right (add_sum_le_of_le (hQ i (by omega)).2
    fun k => (hQ (nxt i k) (by have := hdep i k; omega)).2) _

/-- A family bound holds at any larger supply of derivatives. -/
theorem FamilyBound.mono_supply {ι : Type*} {s s' : ℕ} {K : ℝ≥0} (hs : s ≤ s')
    (h : FamilyBound ι D₀ D p₀ q s K) : FamilyBound ι D₀ D p₀ q s' K :=
  fun hdep hgrad hmem M hM i hi => h hdep hgrad hmem M hM i (by omega)

/-- A family bound at the exponent `P` gives one at any smaller exponent `q` on a domain of
finite measure. -/
theorem FamilyBound.mono_exponent {ι : Type*} [IsFiniteMeasure (volume.restrict D)] {s : ℕ}
    {K : ℝ≥0}
    (hq : 0 < q) (hqP : q ≤ Q) (h : FamilyBound ι D₀ D p₀ Q s K) :
    ∃ K' : ℝ≥0, FamilyBound ι D₀ D p₀ q s K' := by
  obtain ⟨A, hA⟩ := exists_const_eLpNorm_le_of_le (μ := volume.restrict D) (E := ℝ)
    (p := (q : ℝ≥0∞)) (q := (Q : ℝ≥0∞)) (by exact_mod_cast hq.ne') (by exact_mod_cast hqP)
  refine ⟨A * K, fun {F nxt dep m} hdep hgrad hmem M hM i hi => ?_⟩
  obtain ⟨hmemQ, hbd⟩ := h hdep hgrad hmem M hM i hi
  refine ⟨hmemQ.mono_exponent (by exact_mod_cast hqP), ?_⟩
  push_cast
  rw [mul_assoc]
  exact (hA _ hmemQ.aestronglyMeasurable).trans (mul_le_mul_right hbd _)

/-- **The Sobolev ladder with its constant, over any domains.** Let `D x` be the target domain
at the position `x`, let `D (shrink x)` be the domain feeding the rung onto it, and let both lie
in the domain `D₀` on which the family is given. If a rung is available from `D (shrink x)` to
`D x` and `D x` has finite measure, then at rung `s` with `p₀ s ≤ d` one constant takes a
uniform `L^{p₀}` bound on the family to an `Lq` bound on every member of depth at most `m - s`,
for any `q ≥ p₀` whose reciprocal is at least `1/p₀ - s/d`. -/
theorem exists_const_ladder (ι : Type*) {X : Type*} (D : X → Set (EuclideanSpace ℝ (Fin d)))
    (V : X → Prop) (shrink : X → X) (D₀ : Set (EuclideanSpace ℝ (Fin d))) (hp₀ : 1 ≤ p₀)
    (hV : ∀ x, V x → V (shrink x)) (hsub : ∀ x, V x → D x ⊆ D₀)
    (hfin : ∀ x, V x → IsFiniteMeasure (volume.restrict (D x)))
    (hrung : ∀ x, V x → IsSobolevRung d (D (shrink x)) (D x)) :
    ∀ (s : ℕ) {q : ℝ≥0} (x : X), V x → (0 < s → 1 < d) → (p₀ : ℝ) * s ≤ d → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - s * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ →
      ∃ K : ℝ≥0, FamilyBound ι D₀ (D x) p₀ q s K := by
  have hp₀0 : 0 < p₀ := hp₀.trans_lt' one_pos
  refine ladder_induction (fun s q x => ∃ K : ℝ≥0, FamilyBound ι D₀ (D x) p₀ q s K) V shrink
    hp₀ hV (fun x hx => ⟨1, FamilyBound.zero (hsub x hx)⟩) ?_ ?_
  · rintro s x hx p Q q hp hpQ hpq ⟨K, hK⟩
    obtain ⟨Kr, hKr⟩ := hrung x hx p Q q hp hpQ hpq
    exact ⟨_, hK.rung (hsub _ (hV x hx)) hKr⟩
  · rintro s x hx P q hpq hqP hP ⟨K, hK⟩
    have := hfin x hx
    obtain ⟨Kr, hKr⟩ := hrung x hx p₀ p₀ P hp₀ le_rfl hP
    exact FamilyBound.mono_exponent (hp₀0.trans_le hpq) hqP (FamilyBound.mono_supply
      (s' := s + 1) (by omega) (hK.rung (hsub _ (hV x hx)) hKr))

/-- The exponent `2d` of the ladder, as an extended real, in the two forms the Morrey
statement and the ladder use. -/
theorem ofReal_two_mul_natCast (d : ℕ) :
    ENNReal.ofReal (2 * (d : ℝ)) = 2 * ((d : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofReal_mul zero_le_two]
  simp

/-! ### The ladder on balls -/

/-- **The ladder with its constant on concentric balls.** On `Metric.ball c R` the family is given;
each rung shrinks the ball, because the whole-space inequality is fed through a cutoff, and the
conclusion is on `Metric.ball c r` for any `r < R`. -/
theorem exists_const_ladder_ball (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d)) (ι : Type*)
    {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (s : ℕ) {q : ℝ≥0}
    (hds : 0 < s → 1 < d) (hsd : (p₀ : ℝ) * s ≤ d) (hpq : p₀ ≤ q)
    (hqs : (p₀ : ℝ)⁻¹ - s * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0, FamilyBound ι (Metric.ball c R) (Metric.ball c r) p₀ q s K :=
  exists_const_ladder ι (fun r => Metric.ball c r) (fun r => 0 < r ∧ r < R) (fun r => (r + R) / 2)
    (Metric.ball c R) hp₀ (fun r hr => ⟨by linarith [hr.1, hr.2], by linarith [hr.1, hr.2]⟩)
    (fun r hr => Metric.ball_subset_ball hr.2.le) (fun _ _ => inferInstance)
    (fun r hr p q p' hp hpq hpp' => exists_eLpNorm_sobolevConj_le_of_le hd c hp hpq hpp' hr.1
      (by linarith [hr.1, hr.2]))
    s r ⟨hr, hrR⟩ hds hsd hpq hqs

/-- **Sobolev ladder from a general base exponent.** Let `F` assign a function to each index
of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let `dep`
record how far an index sits above the root. If every index of depth at most `m` lies in
`L^{p₀}` there and every index of depth below `m` has its weak gradient in the family, then at
rung `s` with `p₀ s ≤ d` every index of depth at most `m - s` lies in `L^q` on
`Metric.ball c r`, for any `q ≥ p₀` whose reciprocal is at least `1/p₀ - s/d`. -/
theorem memLp_of_gradClosed_general (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R))) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  intro s q r R hsd hpq hqs hr hrR hgrad hmem i hi
  obtain ⟨K, hK⟩ := exists_const_ladder_ball (by omega) c ι hp₀ hr hrR s (fun _ => hd) hsd hpq hqs
  exact (hK hdep hgrad hmem ⊤ (fun _ _ => le_top) i hi).1

/-- **Ladder at the exponent case (i) names.** Under the strict rung condition
`p₀ s < d`, which is the `k < n/p` of Evans §5.6.3 Theorem 6, the reciprocal `1/p₀ - s/d` is
positive and names a finite exponent; the ladder lands on it. -/
theorem memLp_of_gradClosed_general_ideal (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (s : ℕ) {r R : ℝ}
    (hsd : (p₀ : ℝ) * s < (d : ℝ)) (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R)))
    (i : ι) (hi : dep i + s ≤ m) :
    MemLp (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹)
      (volume.restrict (Metric.ball c r)) := by
  obtain ⟨Q, hp₀Q, hQ⟩ := exists_rung_exponent hp₀ (by omega) hsd
  rw [← hQ, inv_inv, Real.toNNReal_coe]
  exact memLp_of_gradClosed_general hd c hp₀ hdep s hsd.le hp₀Q hQ.ge hr hrR hgrad hmem i hi

/-! ### The ladder from `L²` -/

/-- **Sobolev bootstrap at the full step to bounded depth.** Let `F` assign a function to each
index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let
`dep` record how far an index sits above the root, so that differentiating adds at most one. If
every index of depth at most `m` lies in `L²` there and every index of depth below `m` has its
weak gradient in the family, then at step `s` with `2 * s ≤ d` every index of depth at most
`m - s` lies in `Lq` on `Metric.ball c r`, for any exponent `q ≥ 2` whose reciprocal is at least
`1/2 - s/d`. -/
theorem memLp_of_gradClosed_fullStep (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, 2 * s ≤ d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  intro s q r R hsd hq hqs hr hrR hgrad hmem i hi
  obtain ⟨K, hK⟩ := exists_const_ladder_ball hd c ι (p₀ := 2) one_le_two hr hrR s
    (fun _ => by omega) (by push_cast; exact_mod_cast hsd) hq (by simpa using hqs)
  exact (hK hdep hgrad hmem ⊤ (fun _ _ => le_top) i hi).1

/-- **Full-step ladder run to the top.** An index of depth at most `m - ⌊d/2⌋` in a family
closed under weak differentiation as far as `m`, with every member of depth at most `m` in `L²`
on `Metric.ball c R`, lies in `L^{2d}` on any smaller concentric ball. Since `2d > d`, this is
the exponent `EllipticPdes.Embedding.morrey_ball` asks for, in every dimension.

The rung count is `⌊d/2⌋`, and the reciprocal it lands on is `1/2 - ⌊d/2⌋/d`, which is `0` when
`d` is even and `1/(2d)` when `d` is odd. Both are at most `1/(2d)`. -/
theorem memLp_two_mul_of_gradClosed_fullStep (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R)))
    (i : ι) (hi : dep i + d / 2 ≤ m) :
    MemLp (F i) (2 * (d : ℝ≥0)) (volume.restrict (Metric.ball c r)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmod : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
  refine memLp_of_gradClosed_fullStep hd c hdep (d / 2) (by omega) ?_ ?_ hr hrR hgrad hmem i hi
  · rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  · push_cast
    rw [mul_inv, ← sub_nonneg]
    have : 2⁻¹ * (d : ℝ)⁻¹ - (2⁻¹ - ((d / 2 : ℕ) : ℝ) * (d : ℝ)⁻¹) =
        (2 * ((d / 2 : ℕ) : ℝ) + 1 - d) * (2⁻¹ * (d : ℝ)⁻¹) := by field_simp; ring
    rw [this]
    exact mul_nonneg (by linarith) (by positivity)

/-- **Full-step ladder with a constant.** One constant, depending on the dimension, the rung
count, the exponent and the two radii alone, takes a uniform `L²` bound on the family over the
outer ball to an `L^q` bound on the inner one, at every index the rungs reach.

Guo's `‖u‖_{L^q} ≤ C‖u‖_{W^{k,p}}` at `p = 2` is this estimate: the bound is by the `L²` data
alone, uniformly over the members the rungs consume. -/
theorem exists_const_eLpNorm_le_of_gradClosed_fullStep (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) (ι : Type*) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, 2 * s ≤ d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      ∃ K : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
        {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
        (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
        (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
        ∀ M : ℝ≥0, (∀ j, dep j ≤ m →
            eLpNorm (F j) 2 (volume.restrict (Metric.ball c R)) ≤ M) →
        ∀ i, dep i + s ≤ m →
          eLpNorm (F i) q (volume.restrict (Metric.ball c r)) ≤ (K : ℝ≥0∞) * M := by
  intro s q r R hsd hq hqs hr hrR
  obtain ⟨K, hK⟩ := exists_const_ladder_ball hd c ι (p₀ := 2) one_le_two hr hrR s
    (fun _ => by omega) (by push_cast; exact_mod_cast hsd) hq (by simpa using hqs)
  exact ⟨K, fun hdep hgrad hmem M hM i hi => (hK hdep hgrad hmem M hM i hi).2⟩

/-! ### The half-step ladder -/

/-- **Sobolev ladder on a family closed under differentiation.** Let `F` assign a function to
each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let
every `F i` lie in `L²` there. Then at rung `s < d` every `F i` lies in `Lq` on `Metric.ball c r`,
for any exponent `q ≥ 2` whose reciprocal is at least `1/2 - s/(2d)`. -/
theorem memLp_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι} :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, s < d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ / 2 ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ i, MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  intro s q r R hsd hq hqs hr hrR hgrad hmem i
  have hs2 : (s : ℝ) ≤ 2 * (((s + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : s ≤ 2 * ((s + 1) / 2))
  refine memLp_of_gradClosed_fullStep (dep := fun _ => 0) (m := d) hd c (fun _ _ => Nat.zero_le _)
    ((s + 1) / 2) (by omega) hq ?_ hr hrR (fun i _ => hgrad i) (fun i _ => hmem i) i
    (by simp; omega)
  have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  nlinarith

/-- **Ladder run to the top.** A family closed under differentiation, in `L²` on
`Metric.ball c R`, lies in `L^{2d}` on any smaller concentric ball. Since `2d > d`, this is the
exponent `EllipticPdes.Embedding.morrey_ball` asks for, in every dimension. -/
theorem memLp_two_mul_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) (i : ι) :
    MemLp (F i) (2 * (d : ℝ≥0)) (volume.restrict (Metric.ball c r)) :=
  memLp_two_mul_of_gradClosed_fullStep (dep := fun _ => 0) (m := d) hd c (fun _ _ => Nat.zero_le _)
    hr hrR (fun i _ => hgrad i) (fun i _ => hmem i) i (by simp; omega)

end EllipticPdes.Embedding
