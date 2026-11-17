module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeRejectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261116
open Induction InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem argumentsTag (n : Nat) (arity : Fin n → Nat) (tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7)
    (raw typ gamma context : OTerm alpha) (psi : Formula alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral tag) raw)))
    (ha : Nonempty (Derivation body Delta (accepted n arity true typ raw gamma context))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.right ![raw] psi
  intro beta j Theta payload hj hr
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hr
  have htag' := renameInto htag j Theta hj
  rw [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htag'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  have hpair := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
    (raw.relabel j) (numeral tag) payload htag' hr
  exact OriginalUniverseDecoderTransportRejectedProof.argumentsOther
    (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) tag h6 h7 (raw.relabel j) payload (typ.relabel j)
    (gamma.relabel j) (context.relabel j) (psi.relabel j) hpair ha'

theorem termSeven (n : Nat) (arity : Fin n → Nat) 
    (raw typ gamma context : OTerm alpha) (psi : Formula alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 7) raw)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ raw gamma context))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.right ![raw] psi
  intro beta j Theta payload hj hr
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hr
  have htag' := renameInto htag j Theta hj
  rw [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htag'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  have hpair := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
    (raw.relabel j) (numeral 7) payload htag' hr
  exact OriginalUniverseDecoderTransportRejectedProof.termSeven
    (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) payload (typ.relabel j)
    (gamma.relabel j) (context.relabel j) (psi.relabel j) hpair ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeRejectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeRejectionProof
