module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open Induction InductionSyntaxProof MatrixSyntaxProof
open Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases left _ hlt
  intro beta j Theta lm lc ld hj hlc
  rw [acceptedRename]
  have hrtj := renameInto hrt j Theta hj
  have henvj := renameInto henv j Theta hj
  have hedgej := renameInto hedge j Theta hj
  have ihj := renameInto ih j Theta hj
  have haj := renameInto ha j Theta hj
  have hpj := renameInto hp j Theta hj
  rw [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrtj
  rw [environmentRename] at henvj
  rw [edgeRename] at hedgej
  rw [belowRawRename] at ihj
  rw [acceptedRename] at haj
  rw [plainRename] at hpj
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases (right.relabel j) _ hrtj
  intro eta k Xi rm rc rd hk hrc
  rw [acceptedRename]
  have henvk := renameInto henvj k Xi hk
  have hedgek := renameInto hedgej k Xi hk
  have ihk := renameInto ihj k Xi hk
  have hak := renameInto haj k Xi hk
  have hpk := renameInto hpj k Xi hk
  have hlck := renameInto hlc k Xi hk
  rw [graph3Rename] at hlck
  rw [environmentRename] at henvk
  rw [edgeRename] at hedgek
  rw [belowRawRename] at ihk
  rw [acceptedRename] at hak
  rw [plainRename] at hpk
  have ht := ApplicationProof.preserved n arity ((left.relabel j).relabel k) ((right.relabel j).relabel k) (lm.relabel k) rm (lc.relabel k) (ld.relabel k) rc rd ((node.relabel j).relabel k) ((window.relabel j).relabel k) ((context.relabel j).relabel k) ((symbols.relabel j).relabel k) ((types.relabel j).relabel k) hlck hrc henvk hedgek ihk
  exact PlainAwareStructuralBindingProof.transferApply n arity
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    false ((left.relabel j).relabel k) ((right.relabel j).relabel k) ((typ.relabel j).relabel k) ((gamma.relabel j).relabel k) ((context.relabel j).relabel k) ht hak hpk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedApplicationProof
