import Mathlib

open Filter Topology

 theorem norm_add_sq_le_two_mul
    {H : Type*} [NormedAddCommGroup H]
    (x y : H) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hadd : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hnonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
  have hsumNonneg : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    sq_le_sq₀ hnonneg hsumNonneg |>.2 hadd
  have hcross : 2 * ‖x‖ * ‖y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  nlinarith

#check norm_add_sq_le_two_mul
