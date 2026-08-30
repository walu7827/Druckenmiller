import Mathlib

open Set
open Filter
open scoped Topology BigOperators

inductive KindEvidence (center : ℝ × ℝ) : Type where
  | morse (radius gap : ℝ) (hradius : 0 < radius) (hgap : 0 < gap)
  | fold (radius gap : ℝ) (hradius : 0 < radius) (hgap : 0 < gap)

def KindEvidence.radius {center : ℝ × ℝ}
    (evidence : KindEvidence center) : ℝ :=
  match evidence with
  | .morse radius _ _ _ => radius
  | .fold radius _ _ _ => radius

theorem KindEvidence.radius_pos {center : ℝ × ℝ}
    (evidence : KindEvidence center) : 0 < evidence.radius := by
  cases evidence with
  | morse radius gap hradius hgap => exact hradius
  | fold radius gap hradius hgap => exact hradius

def KindEvidence.phaseNeighborhood {center : ℝ × ℝ}
    (evidence : KindEvidence center) : Set (ℝ × ℝ) :=
  {point | |point.2 - center.2| < evidence.radius}

theorem KindEvidence.isOpen_phaseNeighborhood {center : ℝ × ℝ}
    (evidence : KindEvidence center) : IsOpen evidence.phaseNeighborhood := by
  unfold KindEvidence.phaseNeighborhood
  exact isOpen_lt (by fun_prop) continuous_const

theorem KindEvidence.center_mem_phaseNeighborhood {center : ℝ × ℝ}
    (evidence : KindEvidence center) : center ∈ evidence.phaseNeighborhood := by
  change |center.2 - center.2| < evidence.radius
  simpa using evidence.radius_pos

inductive ChartEvidence (center : ℝ × ℝ) (U : Set (ℝ × ℝ)) : Prop where
  | regular (gap : ℝ) (hgap : 0 < gap)
      (hbound : ∀ point ∈ U, gap ≤ |point.2 - center.2| + 1)
  | fold (hbound : ∀ point ∈ U, 0 ≤ point.1 ^ 2)

private theorem chartEvidence_mono
    {center : ℝ × ℝ} {U V : Set (ℝ × ℝ)}
    (evidence : ChartEvidence center U) (hVU : V ⊆ U) :
    ChartEvidence center V := by
  cases evidence with
  | regular gap hgap hbound =>
      exact .regular gap hgap (fun point hpoint ↦ hbound point (hVU hpoint))
  | fold hbound =>
      exact .fold (fun point hpoint ↦ hbound point (hVU hpoint))

structure Chart (center : ℝ × ℝ) where
  carrier : Set (ℝ × ℝ)
  isOpen_carrier : IsOpen carrier
  center_mem : center ∈ carrier
  evidence : ChartEvidence center carrier

private def restrictChart {center : ℝ × ℝ}
    (chart : Chart center) (sublevel : KindEvidence center) : Chart center where
  carrier := chart.carrier ∩ sublevel.phaseNeighborhood
  isOpen_carrier := chart.isOpen_carrier.inter sublevel.isOpen_phaseNeighborhood
  center_mem := ⟨chart.center_mem, sublevel.center_mem_phaseNeighborhood⟩
  evidence := chartEvidence_mono chart.evidence inter_subset_left

private theorem restrictChart_carrier_subset {center : ℝ × ℝ}
    (chart : Chart center) (sublevel : KindEvidence center) :
    (restrictChart chart sublevel).carrier ⊆ sublevel.phaseNeighborhood :=
  inter_subset_right

structure FiniteAtlas (centersAll : Type*) [Fintype centersAll]
    (point : centersAll → ℝ × ℝ) where
  selected : Finset centersAll
  charts : ∀ center, Chart (point center)
  evidence : ∀ center : {c // c ∈ selected}, KindEvidence (point center.1)
  carrier_subset_phaseNeighborhood : ∀ center : {c // c ∈ selected},
    (charts center.1).carrier ⊆ (evidence center).phaseNeighborhood

def FiniteAtlas.stationaryNeighborhood
    {centersAll : Type*} [Fintype centersAll]
    {point : centersAll → ℝ × ℝ} (atlas : FiniteAtlas centersAll point) :
    Set (ℝ × ℝ) :=
  ⋃ center ∈ atlas.selected, (atlas.charts center).carrier

def FiniteAtlas.phaseNeighborhoodUnion
    {centersAll : Type*} [Fintype centersAll]
    {point : centersAll → ℝ × ℝ} (atlas : FiniteAtlas centersAll point) :
    Set (ℝ × ℝ) :=
  ⋃ center : {c // c ∈ atlas.selected},
    (atlas.evidence center).phaseNeighborhood

theorem FiniteAtlas.stationaryNeighborhood_subset_phaseNeighborhoodUnion
    {centersAll : Type*} [Fintype centersAll]
    {point : centersAll → ℝ × ℝ} (atlas : FiniteAtlas centersAll point) :
    atlas.stationaryNeighborhood ⊆ atlas.phaseNeighborhoodUnion := by
  intro x hx
  unfold FiniteAtlas.stationaryNeighborhood at hx
  rcases Set.mem_iUnion.mp hx with ⟨center, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hcenter, hx⟩
  unfold FiniteAtlas.phaseNeighborhoodUnion
  refine Set.mem_iUnion.mpr ⟨⟨center, hcenter⟩, ?_⟩
  exact atlas.carrier_subset_phaseNeighborhood ⟨center, hcenter⟩ hx

#check restrictChart_carrier_subset
#check FiniteAtlas.stationaryNeighborhood_subset_phaseNeighborhoodUnion
