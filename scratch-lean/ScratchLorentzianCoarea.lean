import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

noncomputable section

def lorentz (epsilon u : ℝ) : ℝ :=
  epsilon / (Real.pi * (u ^ 2 + epsilon ^ 2))

theorem lorentz_nonneg {epsilon : ℝ} (hepsilon : 0 < epsilon) (u : ℝ) :
    0 ≤ lorentz epsilon u := by
  unfold lorentz
  positivity

theorem continuous_lorentz {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Continuous (lorentz epsilon) := by
  unfold lorentz
  fun_prop

theorem measurable_ofReal_lorentz {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Measurable (fun u : ℝ ↦ ENNReal.ofReal (lorentz epsilon u)) :=
  ENNReal.measurable_ofReal.comp (continuous_lorentz hepsilon).measurable

axiom integrable_lorentz {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Integrable (lorentz epsilon)
axiom integral_lorentz {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∫ u : ℝ, lorentz epsilon u = 1

theorem lintegral_ofReal_lorentz_eq_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∫⁻ u : ℝ, ENNReal.ofReal (lorentz epsilon u) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_lorentz hepsilon)]
  · rw [integral_lorentz hepsilon]
    norm_num
  · exact Filter.Eventually.of_forall (lorentz_nonneg hepsilon)

theorem pairBranch_monotone_lorentz_bound
    {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hfmeas : Measurable f)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : MonotoneOn f s)
    {gap epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hderiv : ∀ x ∈ s, gap ≤ f' x) :
    ENNReal.ofReal gap *
        (∫⁻ x in s, ENNReal.ofReal (lorentz epsilon (f x))) ≤ 1 := by
  have hq := measurable_ofReal_lorentz hepsilon
  calc
    ENNReal.ofReal gap *
        (∫⁻ x in s, ENNReal.ofReal (lorentz epsilon (f x))) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal (lorentz epsilon u) := by
      rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hf' hf]
      rw [← lintegral_const_mul (ENNReal.ofReal gap) (hq.comp hfmeas)]
      apply lintegral_mono'
        (Measure.restrict_mono (Set.image_subset_range f s) le_rfl) le_rfl
    _ = 1 := lintegral_ofReal_lorentz_eq_one hepsilon

#check lintegral_ofReal_lorentz_eq_one
