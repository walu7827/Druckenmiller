import Mathlib

open MeasureTheory Set
open scoped Interval

noncomputable section

def derv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (epsilon : ℝ) (f : ℝ → H) (r : ℝ) : H :=
  (Complex.I * (epsilon : ℂ)) • f r

def src {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (epsilon : ℝ) (f : ℝ → H) (T : ℝ) : H :=
  ∫ r in (0 : ℝ)..T, derv epsilon f r

theorem norm_derv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (epsilon : ℝ) (f : ℝ → H) (r : ℝ) :
    ‖derv epsilon f r‖ = |epsilon| * ‖f r‖ := by
  unfold derv
  rw [norm_smul, norm_mul]
  simp [Real.norm_eq_abs]

theorem norm_src_le_const
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (epsilon : ℝ) (f : ℝ → H) (T M : ℝ)
    (hM : ∀ r ∈ Ι (0 : ℝ) T, ‖f r‖ ≤ M) :
    ‖src epsilon f T‖ ≤ (|epsilon| * M) * |T| := by
  unfold src
  have hderivative : ∀ r ∈ Ι (0 : ℝ) T,
      ‖derv epsilon f r‖ ≤ |epsilon| * M := by
    intro r hr
    rw [norm_derv]
    exact mul_le_mul_of_nonneg_left (hM r hr) (abs_nonneg epsilon)
  simpa using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := T)
      (C := |epsilon| * M) (f := derv epsilon f) hderivative)

#check norm_src_le_const
