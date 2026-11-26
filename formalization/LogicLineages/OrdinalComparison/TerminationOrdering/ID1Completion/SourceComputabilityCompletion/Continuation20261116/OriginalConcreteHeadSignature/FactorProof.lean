module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.OutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.FactorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem validSignature : Targets.InternalValidSignature := by
  intro n arity body alpha Delta raw result args packed hr ha hp
  constructor
  · intro hv
    apply GuardProof.cases n raw _
    · intro beta j Theta hj hg
      simp only [graph1Rename,sucRelabel,zRelabel]
      have hvj := renameInto hv j Theta hj
      simp only [graph1Rename,sucRelabel] at hvj
      have hz := OutputProof.failureValue n arity (raw.relabel j) hg
      obtain ⟨he⟩ := valueUnique (signature n arity) (suc (packed.relabel j)) z ![raw.relabel j] hvj hz
      exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
    · intro beta j Theta hj hg
      simp only [graph1Rename,sucRelabel,zRelabel]
      exact hg
  · intro hg
    exact OutputProof.successValue n arity raw result args packed hr ha hp hg

theorem invalidSignature : Targets.InternalInvalidSignature := by
  intro n arity body alpha Delta raw
  constructor
  · intro hv
    apply GuardProof.cases n raw _
    · intro beta j Theta hj hg
      simp only [graph1Rename,zRelabel]
      exact hg
    · intro beta j Theta hj hg
      simp only [graph1Rename,zRelabel]
      have hvj := renameInto hv j Theta hj
      simp only [graph1Rename,zRelabel] at hvj
      have ho := successorBranchElim (Continuation20261115.OriginalHeadDecoderValidity.check n)
        (constant 1 0) (succOf (pairOf Continuation20261114.OriginalHeadResult.headResult (arguments n arity)))
        z z ![raw.relabel j] hg hvj
      obtain ⟨hn⟩ := OutputProof.successorProgramNonzero _ (raw.relabel j) z ho
      exact ⟨Derivation.explosion (Derivation.implicationElimination hn (refl z))⟩
  · intro hg
    exact OutputProof.failureValue n arity raw hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.FactorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.FactorProof
