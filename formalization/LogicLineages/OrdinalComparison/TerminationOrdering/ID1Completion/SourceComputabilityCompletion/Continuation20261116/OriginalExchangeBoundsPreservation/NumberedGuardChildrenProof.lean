module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261114 Continuation20261115
open OriginalEnumerationFields.Boolean.ListCasesProof (memberHead memberTail)

theorem atLists (n : Nat) (raw label hd typ head types tail rest children : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,hd,typ,head,types,tail])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode children head rest))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) head)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)) := by
  have hchildren := ArgumentEntriesChildren.InternalProof.internalNumbered body alpha Delta raw label hd typ head types tail rest children hc hr hl
  exact ⟨OriginalDecodedDependencyClosure.ChildrenProof.childrenClosed n body alpha Delta raw children head hg hchildren (memberHead children head rest hl),
    OriginalDecodedDependencyClosure.ChildrenProof.childrenClosed n body alpha Delta raw children tail hg hchildren
      (memberTail children head rest tail hl (memberHead rest tail z hr))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardChildrenProof
