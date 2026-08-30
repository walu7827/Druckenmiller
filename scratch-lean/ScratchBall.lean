import Mathlib

open Set

 theorem exists_ball_subset_inter
    {X : Type*} [PseudoMetricSpace X]
    {U V : Set X} {x : X}
    (hU : IsOpen U) (hV : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∩ V := by
  have hopen : IsOpen (U ∩ V) := hU.inter hV
  have hx : x ∈ U ∩ V := ⟨hxU, hxV⟩
  rcases Metric.isOpen_iff.mp hopen x hx with ⟨r, hr, hsub⟩
  exact ⟨r, hr, hsub⟩

#check exists_ball_subset_inter
