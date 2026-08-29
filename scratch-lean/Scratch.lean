import Mathlib

open Set

noncomputable section

inductive Evidence (center : ℝ × ℝ) : Type where
  | left (radius : ℝ) (hradius : 0 < radius)
  | right (radius : ℝ) (hradius : 0 < radius)

theorem evidence_nonempty (center : ℝ × ℝ) : Nonempty (Evidence center) :=
  ⟨.left 1 one_pos⟩

noncomputable def chosenEvidence (center : ℝ × ℝ) : Evidence center :=
  Classical.choice (evidence_nonempty center)

def Evidence.radius {center : ℝ × ℝ} (evidence : Evidence center) : ℝ :=
  match evidence with
  | .left radius _ => radius
  | .right radius _ => radius

theorem Evidence.radius_pos {center : ℝ × ℝ}
    (evidence : Evidence center) : 0 < evidence.radius := by
  cases evidence with
  | left radius hradius => exact hradius
  | right radius hradius => exact hradius

def Evidence.neighborhood {center : ℝ × ℝ}
    (evidence : Evidence center) : Set (ℝ × ℝ) :=
  Prod.snd ⁻¹' Ioo (center.2 - evidence.radius)
    (center.2 + evidence.radius)

theorem Evidence.isOpen_neighborhood {center : ℝ × ℝ}
    (evidence : Evidence center) : IsOpen evidence.neighborhood := by
  exact isOpen_Ioo.preimage continuous_snd

theorem Evidence.center_mem_neighborhood {center : ℝ × ℝ}
    (evidence : Evidence center) : center ∈ evidence.neighborhood := by
  change center.2 - evidence.radius < center.2 ∧
    center.2 < center.2 + evidence.radius
  constructor <;> linarith [evidence.radius_pos]

inductive PhysicalChartEvidence (center : ℝ × ℝ)
    (U : Set (ℝ × ℝ)) : Prop where
  | regular (hbound : ∀ point ∈ U, point.1 = point.1)
  | fold (hbound : ∀ point ∈ U, point.2 = point.2)

theorem PhysicalChartEvidence.mono
    {center : ℝ × ℝ} {U V : Set (ℝ × ℝ)}
    (evidence : PhysicalChartEvidence center U)
    (hVU : V ⊆ U) : PhysicalChartEvidence center V := by
  cases evidence with
  | regular hbound =>
      exact .regular fun point hpoint => hbound point (hVU hpoint)
  | fold hbound =>
      exact .fold fun point hpoint => hbound point (hVU hpoint)

structure CertifiedChart (center : ℝ × ℝ) where
  carrier : Set (ℝ × ℝ)
  isOpen_carrier : IsOpen carrier
  center_mem : center ∈ carrier
  evidence : PhysicalChartEvidence center carrier

def CertifiedChart.restrictToEvidenceNeighborhood
    {center : ℝ × ℝ} (chart : CertifiedChart center)
    (sublevel : Evidence center) : CertifiedChart center where
  carrier := chart.carrier ∩ sublevel.neighborhood
  isOpen_carrier := chart.isOpen_carrier.inter sublevel.isOpen_neighborhood
  center_mem := ⟨chart.center_mem, sublevel.center_mem_neighborhood⟩
  evidence := chart.evidence.mono inter_subset_left

theorem CertifiedChart.restrict_carrier_subset
    {center : ℝ × ℝ} (chart : CertifiedChart center)
    (sublevel : Evidence center) :
    (chart.restrictToEvidenceNeighborhood sublevel).carrier ⊆
      sublevel.neighborhood :=
  inter_subset_right

end
