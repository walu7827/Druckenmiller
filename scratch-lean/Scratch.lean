import Mathlib

open Filter Set
open scoped BigOperators Topology

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

inductive PowerData : Type where
  | morse (radius gap : ℝ)
  | fold (radius gap : ℝ)

def toyMorseMass (epsilon : ℝ) : ℝ := ‖epsilon‖ + ‖2 * epsilon‖
def toyFoldMass (epsilon : ℝ) : ℝ := ‖3 * epsilon‖ + ‖4 * epsilon‖

def PowerData.scaledMass (data : PowerData) : ℝ → ℝ :=
  match data with
  | .morse _ _ => fun epsilon => epsilon * toyMorseMass epsilon
  | .fold _ _ => fun epsilon => epsilon * toyFoldMass epsilon

def PowerData.envelope (data : PowerData) : ℝ → ℝ :=
  match data with
  | .morse radius gap => fun epsilon => radius * epsilon + gap * epsilon
  | .fold radius gap => fun epsilon => radius * epsilon + gap * epsilon

theorem PowerData.scaledMass_nonneg
    (data : PowerData) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    0 ≤ data.scaledMass epsilon := by
  cases data with
  | morse _ _ =>
      unfold PowerData.scaledMass
      exact mul_nonneg hepsilon (by
        unfold toyMorseMass
        positivity)
  | fold _ _ =>
      unfold PowerData.scaledMass
      exact mul_nonneg hepsilon (by
        unfold toyFoldMass
        positivity)

theorem PowerData.tendsto_envelope_zero (data : PowerData) :
    Tendsto data.envelope (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  cases data with
  | morse radius gap =>
      have hcontinuous : ContinuousAt
          (fun epsilon : ℝ => radius * epsilon + gap * epsilon) 0 := by
        fun_prop
      have hfull : Tendsto
          (fun epsilon : ℝ => radius * epsilon + gap * epsilon)
          (nhds 0) (nhds 0) := by
        simpa only [ContinuousAt, mul_zero, add_zero] using hcontinuous
      simpa [PowerData.envelope] using hfull.mono_left inf_le_left
  | fold radius gap =>
      have hcontinuous : ContinuousAt
          (fun epsilon : ℝ => radius * epsilon + gap * epsilon) 0 := by
        fun_prop
      have hfull : Tendsto
          (fun epsilon : ℝ => radius * epsilon + gap * epsilon)
          (nhds 0) (nhds 0) := by
        simpa only [ContinuousAt, mul_zero, add_zero] using hcontinuous
      simpa [PowerData.envelope] using hfull.mono_left inf_le_left

structure FiniteAtlas where
  centers : Finset Nat
  evidence : ∀ _center : {c // c ∈ centers}, PowerData

def FiniteAtlas.totalEnvelope (atlas : FiniteAtlas) (epsilon : ℝ) : ℝ :=
  ∑ center : {c // c ∈ atlas.centers},
    (atlas.evidence center).envelope epsilon

theorem FiniteAtlas.tendsto_totalEnvelope_zero (atlas : FiniteAtlas) :
    Tendsto atlas.totalEnvelope (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  unfold FiniteAtlas.totalEnvelope
  simpa using tendsto_finset_sum Finset.univ fun center _ =>
    (atlas.evidence center).tendsto_envelope_zero

def morseEnv (radius gap epsilon : ℝ) : ℝ :=
  (1 / Real.pi) *
      (2 * Real.sqrt (2 * Real.sqrt epsilon / gap)) +
    (epsilon / Real.pi) * (2 * radius)

def foldEnv (radius gap epsilon : ℝ) : ℝ :=
  (1 / Real.pi) *
      Real.sqrt (Real.sqrt (Real.sqrt epsilon / gap)) +
    (epsilon / Real.pi) * radius

theorem tendsto_morseEnv_zero (radius gap : ℝ) :
    Tendsto (morseEnv radius gap) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcontinuous : ContinuousAt (morseEnv radius gap) 0 := by
    unfold morseEnv
    fun_prop
  have hfull : Tendsto (morseEnv radius gap) (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, morseEnv, Real.sqrt_zero, zero_div,
      mul_zero, add_zero] using hcontinuous
  exact hfull.mono_left inf_le_left

theorem tendsto_foldEnv_zero (radius gap : ℝ) :
    Tendsto (foldEnv radius gap) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcontinuous : ContinuousAt (foldEnv radius gap) 0 := by
    unfold foldEnv
    fun_prop
  have hfull : Tendsto (foldEnv radius gap) (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, foldEnv, Real.sqrt_zero, zero_div,
      mul_zero, add_zero] using hcontinuous
  exact hfull.mono_left inf_le_left

end
