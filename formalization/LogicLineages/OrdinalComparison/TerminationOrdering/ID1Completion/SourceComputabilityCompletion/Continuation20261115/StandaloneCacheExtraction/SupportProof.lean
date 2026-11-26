module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def relation (raw param table value : OTerm alpha) : Formula alpha :=
  ((graph2 ArgumentEntriesRecursor.extract value raw param).imp
    (graph2 ExchangeMapGraph.lookup (suc value) table raw)) ⊓
  ((graph2 ExchangeMapGraph.lookup (suc value) table raw).imp
    (graph2 ArgumentEntriesRecursor.extract value raw param))

theorem relationRename {beta : Type} (raw param table value : OTerm alpha) (j : alpha → beta) :
    (relation raw param table value).relabel j =
      relation (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) := by
  simp only [relation,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,graph2Rename,sucRelabel]

theorem tableTransport (old table raw value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old table)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) old raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table raw)) := by
  unfold graph2 programGraph at hl ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula ExchangeMapGraph.lookup) (suc value) ![old,raw] ![table,raw] _ hl
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl raw⟩

theorem relationAtValue (raw param table value inner : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract inner raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc inner) table raw))) :
    Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply andIntro
  · have hv : Nonempty (Derivation body (graph2 ArgumentEntriesRecursor.extract value raw param :: Delta)
        (graph2 ArgumentEntriesRecursor.extract value raw param)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique ArgumentEntriesRecursor.extract inner value ![raw,param] (withHyp he _) hv
    obtain ⟨hout⟩ := outputTransport ExchangeMapGraph.lookup (suc inner) (suc value) ![table,raw]
      ⟨congSuc hq⟩ (withHyp hl _)
    exact ⟨Derivation.implicationIntroduction hout⟩
  · have hv : Nonempty (Derivation body (graph2 ExchangeMapGraph.lookup (suc value) table raw :: Delta)
        (graph2 ExchangeMapGraph.lookup (suc value) table raw)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique ExchangeMapGraph.lookup (suc inner) (suc value) ![table,raw] (withHyp hl _) hv
    obtain ⟨hout⟩ := outputTransport ArgumentEntriesRecursor.extract inner value ![raw,param]
      ⟨cancelSuc hq⟩ (withHyp he _)
    exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.SupportProof
