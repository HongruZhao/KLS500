import KLS.Vendored.StatLeanPrekopaLeindler
import KLS.Definitions

/-!
# Prékopa--Leindler in the actual Euclidean spaces

The selectively vendored, independently checked StatLean proof works with
finite products of real coordinates. This wrapper transports that exact
inequality through the volume-preserving Euclidean coordinate equivalence.
-/

open MeasureTheory Set
open scoped ENNReal

namespace KLS

theorem prekopaLeindler {n : ℕ} {f g h : Space n → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hle : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have hp := AsymptoticStatistics.prekopaLeindler
    (hf.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    (hg.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    (hh.comp (PiLp.volume_preserving_toLp (Fin n)).measurable) ht0 ht1
    (fun x y => hle (WithLp.toLp 2 x) (WithLp.toLp 2 y))
  simpa only [Function.comp_def, (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hf,
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hg,
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hh] using hp

end KLS

#print axioms KLS.prekopaLeindler
