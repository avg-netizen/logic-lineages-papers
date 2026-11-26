module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FamilyProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains CoherentConstructorLattice

theorem familyNatural (tau : Ty) (P Q : World input) (h : Extends P Q) :
    weaken h (familyValue tau P) = familyValue tau Q := by
  cases tau with
  | ground =>
    change (family input .ground).restrict h ((RecursiveNaturalLatticesProof.bounds input .ground).inf P ∅) = _
    rw [(RecursiveNaturalLatticesProof.bounds input .ground).infRestriction]
    simp only [Set.image_empty]
    rfl
  | arrow sigma tau =>
    exact ExecutableDomainBottomProof.weakeningBottom Unit inferInstance (fun _ => 0) input (.arrow sigma tau) P Q h

theorem coherent : Targets.ConcreteFamilyCoherent := by
  constructor
  · intro f tau P a b hab
    exact le_rfl
  · intro f tau P Q h a
    exact familyNatural tau.val P Q h

noncomputable def constructor : Constructors input := ⟨familyRaw, coherent⟩

theorem groundNotBottom (P : World input) :
    familyValue .ground P ≠ ExecutableDomainBottom.bottomValue input .ground P := by
  let alive : Value input .ground P := groundFromBits (fun _ => (true,(fun _ => false),(fun _ => false)))
  have hl : alive ≤ familyValue .ground P :=
    ((RecursiveNaturalLatticesProof.bounds input .ground).infSpec P ∅).2 (by intro a ha; cases ha)
  intro he
  rw [he] at hl
  have hv := (RecursiveNaturalDomainsProof.transportOrder
    (family input .ground) (NaturalTupleLayerProof.layerFamily input .ground (lower input .ground))
    (familyEquation input .ground) P alive (ExecutableDomainBottom.bottomValue input .ground P)).mp hl
  change layerView input .ground P alive ≤ layerView input .ground P (ExecutableDomainBottom.bottomValue input .ground P) at hv
  have hb := hv.1 ⟨P,fun _ hx => hx⟩
  change (layerView input .ground P alive).val.1 ⟨P,fun _ hx => hx⟩ ≤
    (layerView input .ground P (ExecutableDomainBottom.bottomValue input .ground P)).val.1 ⟨P,fun _ hx => hx⟩ at hb
  dsimp [alive,groundFromBits] at hb
  rw [RecursiveNaturalDomainsProof.layerViewFold,ExecutableDomainBottomProof.bottomLayer] at hb
  have bad : (true : Bool) ≤ false := hb.1
  exact (by decide : ¬ ((true : Bool) ≤ false)) bad
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FamilyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FamilyProof
