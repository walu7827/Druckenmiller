import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory MeasureTheory.Measure Set

noncomputable section

 theorem gap_mul_lintegral_le_image_of_antitoneOn
    {s : Set ℝ} {f f' : ℝ → ℝ} (q : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s)
    {gap : ℝ} (hgap : 0 < gap)
    (hderiv : ∀ x ∈ s, gap ≤ -f' x) :
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
      ∫⁻ u in f '' s, q u := by
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf q]
  rw [← lintegral_const_mul]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hderiv x hx)) _

 theorem gap_mul_lintegral_le_total_of_antitoneOn
    {s : Set ℝ} {f f' : ℝ → ℝ} (q : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s)
    {gap : ℝ} (hgap : 0 < gap)
    (hderiv : ∀ x ∈ s, gap ≤ -f' x) :
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
      ∫⁻ u, q u := by
  calc
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
        ∫⁻ u in f '' s, q u :=
      gap_mul_lintegral_le_image_of_antitoneOn q hs hf' hf hgap hderiv
    _ ≤ ∫⁻ u, q u :=
      lintegral_mono_measure (Measure.restrict_le_self)

#check gap_mul_lintegral_le_total_of_antitoneOn
