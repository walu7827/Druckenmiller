import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set

noncomputable section

 theorem gap_mul_lintegral_le_image_of_antitoneOn
    {s : Set ℝ} {f f' : ℝ → ℝ} (q : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hfmeas : Measurable f) (hq : Measurable q)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s)
    {gap : ℝ} (hderiv : ∀ x ∈ s, gap ≤ -f' x) :
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
      ∫⁻ u in f '' s, q u := by
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hf' hf q]
  rw [← lintegral_const_mul (ENNReal.ofReal gap) (hq.comp hfmeas)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hderiv x hx)) _

 theorem gap_mul_lintegral_le_total_of_antitoneOn
    {s : Set ℝ} {f f' : ℝ → ℝ} (q : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hfmeas : Measurable f) (hq : Measurable q)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : AntitoneOn f s)
    {gap : ℝ} (hderiv : ∀ x ∈ s, gap ≤ -f' x) :
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
      ∫⁻ u, q u := by
  calc
    ENNReal.ofReal gap * (∫⁻ x in s, q (f x)) ≤
        ∫⁻ u in f '' s, q u :=
      gap_mul_lintegral_le_image_of_antitoneOn q hs hfmeas hq hf' hf hderiv
    _ ≤ ∫⁻ u in (Set.univ : Set ℝ), q u :=
      lintegral_mono_set (Set.subset_univ _)
    _ = ∫⁻ u, q u := by simp

#check gap_mul_lintegral_le_total_of_antitoneOn
