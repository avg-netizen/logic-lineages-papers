module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.RawStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem atObservations (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (result n arguments raw xs)) :=
  InductionBindingProof.atRawApply n arity H arguments raw xs (RawStepProof.allRaw n arity H raw) ho

theorem internalTermFields : Targets.InternalTermFields := by
  intro n arity H body alpha Delta seed param context types heads typ raw gamma count pair size maxLabel labels tupleBound
    hcontext htypes hheads hclosed ha hlength hbounds hpair hsize hlabel
  let xs : Fin 11 → OTerm alpha := ![seed,param,context,types,heads,typ,gamma,count,pair,size,maxLabel]
  have ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)) :=
    ObservationsProof.assemble n arity H false raw xs hcontext htypes hheads hclosed ha hlength hbounds hpair
  have hi := atObservations n arity H false raw xs ho
  have hf := CapacityBindingProof.applyBound n raw xs labels tupleBound
    (ObservationsProof.enclosing n false raw xs hi) hsize hlabel
  exact hf

theorem internalArgumentsFields : Targets.InternalArgumentsFields := by
  intro n arity H body alpha Delta seed param context types heads typ raw gamma count pair size maxLabel labels tupleBound
    hcontext htypes hheads hclosed ha hlength hbounds hpair hsize hlabel
  let xs : Fin 11 → OTerm alpha := ![seed,param,context,types,heads,typ,gamma,count,pair,size,maxLabel]
  have ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)) :=
    ObservationsProof.assemble n arity H true raw xs hcontext htypes hheads hclosed ha hlength hbounds hpair
  have hi := atObservations n arity H true raw xs ho
  have hf := CapacityBindingProof.applyBound n raw xs labels tupleBound
    (ObservationsProof.enclosing n true raw xs hi) hsize hlabel
  exact andIntro hf (TypesProof.monotone typ types size tupleBound
    (ObservationsProof.argumentTypes n raw xs hi) hsize)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Proof
