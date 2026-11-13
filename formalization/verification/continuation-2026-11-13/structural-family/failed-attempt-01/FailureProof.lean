module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FamilyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FailureProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment
open FullListValueApplication CoherentConstructorLattice OriginalSpineActions
open ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport
open ActualLimitSubstitution FamilyProof

abbrev arrow : Ty := .arrow .ground .ground

def marked : MarkedTerm Unit (fun _ => 0) [] arrow := .marked .zero arrow .nil [] .nil

def replacement : MarkedSubstitution Unit (fun _ => 0) [arrow] []
  | _, .here => marked
  | _, .there v => nomatch v

theorem markedConfined : Confined input marked := by decide

theorem replacementConfined : RangeConfined input replacement := by
  intro tau v ht
  cases v with
  | here => exact markedConfined
  | there v => cases v

def variable : ConfinedTerm input [arrow] arrow := ⟨.var .here, by decide⟩

def world : World input := ⟨[], by decide⟩

def emptyEnvironment : Environment input [] world := fun {_} v => nomatch v

noncomputable def sourceEnvironment : Environment input [arrow] world
  | _, .here => ExecutableDomainBottom.bottomValue input arrow world
  | _, .there v => nomatch v

theorem agreement : Agreement constructor replacement replacementConfined sourceEnvironment emptyEnvironment := by
  intro tau v ht
  cases v with
  | here => rfl
  | there v => cases v

theorem compatibility : ProtectedCompatible input replacement (fun {_} _ => false) (fun {_} _ => false) := by
  intro tau v ht
  cases v with
  | here =>
    constructor
    · intro h; cases h
    · intro _; exact ⟨True.intro,True.intro⟩
  | there v => cases v

noncomputable def arguments : Values input [.ground] world :=
  fun _ => ExecutableDomainBottom.bottomValue input .ground world

theorem markedScanValue :
    scan (substituteSource replacement replacementConfined variable) constructor world emptyEnvironment
      (fun {_} _ => false) [.ground] .ground arguments rfl = familyValue .ground world := by
  rfl

theorem variableScanValue :
    scan variable constructor world sourceEnvironment (fun {_} _ => false)
      [.ground] .ground arguments rfl = ExecutableDomainBottom.bottomValue input .ground world := by
  change applyValue (ExecutableDomainBottom.bottomValue input arrow world)
    (fullSuffix [.ground] .ground (by simp)) arguments = _
  exact ExecutableDomainBottomProof.allTablesBottom Unit inferInstance (fun _ => 0) input arrow world
    ⟨world,fun _ hx => hx⟩ (fullSuffix [.ground] .ground (by simp)) arguments

theorem scannerFails : ¬ ScannerSubstitutionAt constructor := by
  intro h
  have he := h [arrow] [] arrow variable replacement replacementConfined world sourceEnvironment
    emptyEnvironment (fun {_} _ => false) (fun {_} _ => false) agreement compatibility
    [.ground] .ground arguments rfl
  rw [markedScanValue,variableScanValue] at he
  exact groundNotBottom world he

theorem concrete : Targets.ConcreteScannerFailure := ⟨constructor,rfl,scannerFails⟩

theorem generic : Targets.GenericScannerFailure := by
  intro h
  exact scannerFails (h constructor)
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FailureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.FailureProof
