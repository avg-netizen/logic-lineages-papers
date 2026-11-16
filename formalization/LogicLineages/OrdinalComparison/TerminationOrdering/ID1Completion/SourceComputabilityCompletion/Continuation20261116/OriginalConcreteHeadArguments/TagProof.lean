module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.TagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalConcreteHeadSignature
open Continuation20261114.OriginalHeadClass.InternalProof (chooseFactor constantTransfer)
attribute [local irreducible] programGraph
theorem internalTagFactor : Targets.InternalTagFactor := by
  intro n arity body alpha Delta tag raw payload out hp
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha raw (numeral tag.val) payload) hp
  have ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral tag.val) raw)) :=
    ⟨Derivation.conjunctionLeft hi⟩
  have hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)) :=
    ⟨Derivation.conjunctionRight hi⟩
  have comp (k : Nat) :
      Nonempty (Derivation body Delta (graph1 (atPayload n arity k) out raw)) ↔
      Nonempty (Derivation body Delta (graph1 (branchArguments n arity k) out payload)) :=
    ⟨fun h => unaryRecover (branchArguments n arity k) InternalUnpair.right out payload ![raw] h hr,
      fun h => unaryValue (branchArguments n arity k) InternalUnpair.right out payload ![raw] h hr⟩
  fin_cases tag <;> simp [arguments,chooseFactor _ raw out ht]
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact comp 4
  · exact comp 5

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.TagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadArguments.TagProof
