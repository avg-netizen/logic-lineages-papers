module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment
open FullListValueApplication CoherentConstructorLattice OriginalSpineActions
open ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport
open ActualLimitSubstitution

/-- A literal finite source input with the zero head and both required types. -/
def input : Input Unit (fun _ => 0) where
  context := []
  sourceType := .ground
  targetType := .arrow .ground .ground
  source := .zeroC
  target := .succC

/-- Constant top at ground type and constant bottom at every arrow type.
No cross-type constructor equation is built into the original `Good` predicate. -/
noncomputable def familyValue (tau : Ty) (P : World input) : Value input tau P :=
  match tau with
  | .ground => (RecursiveNaturalLatticesProof.bounds input .ground).inf P ∅
  | .arrow sigma tau => ExecutableDomainBottom.bottomValue input (.arrow sigma tau) P

noncomputable def familyRaw : Raw input := fun _ tau P _ => familyValue tau.val P

/-- Exact arbitrary-family version of the existing fixed-point scanner law.
All confinement, environment agreement and protected-variable conditions are
retained. Only `limit I above` is replaced by the quantified constructor M. -/
def ScannerSubstitutionAt (M : Constructors input) : Prop :=
  ∀ (Gamma Delta : List Ty) (tau : Ty) (q : ConfinedTerm input Gamma tau)
    (s : MarkedSubstitution Unit (fun _ => 0) Gamma Delta)
    (hs : RangeConfined input s) (P : World input)
    (rho : Environment input Gamma P) (eta : Environment input Delta P)
    (sourceMask : Protected Gamma) (targetMask : Protected Delta),
  Agreement M s hs rho eta → ProtectedCompatible input s sourceMask targetMask →
  ∀ (types : List Ty) (upsilon : Ty) (args : Values input types P)
    (h : tau = arrows types upsilon),
  scan (substituteSource s hs q) M P eta targetMask types upsilon args h =
    scan q M P rho sourceMask types upsilon args h
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily
