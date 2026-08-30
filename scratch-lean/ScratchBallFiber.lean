import Mathlib

open Set Metric

 def fiber (center : ℝ × ℝ) (r m : ℝ) : Set ℝ :=
  {x | (m, x) ∈ Metric.ball center r}

 theorem fiber_eq_ball_of_mem
    (center : ℝ × ℝ) (r m : ℝ)
    (hm : m ∈ Metric.ball center.1 r) :
    fiber center r m = Metric.ball center.2 r := by
  ext x
  unfold fiber
  rw [← ball_prod_same center.1 center.2 r]
  simp [hm]

 theorem fiber_eq_empty_of_not_mem
    (center : ℝ × ℝ) (r m : ℝ)
    (hm : m ∉ Metric.ball center.1 r) :
    fiber center r m = ∅ := by
  ext x
  unfold fiber
  rw [← ball_prod_same center.1 center.2 r]
  simp [hm]

 theorem fiber_eq_Ioo_of_mem
    (center : ℝ × ℝ) (r m : ℝ)
    (hm : m ∈ Metric.ball center.1 r) :
    fiber center r m = Ioo (center.2 - r) (center.2 + r) := by
  rw [fiber_eq_ball_of_mem center r m hm, Real.ball_eq_Ioo]

#check fiber_eq_Ioo_of_mem
