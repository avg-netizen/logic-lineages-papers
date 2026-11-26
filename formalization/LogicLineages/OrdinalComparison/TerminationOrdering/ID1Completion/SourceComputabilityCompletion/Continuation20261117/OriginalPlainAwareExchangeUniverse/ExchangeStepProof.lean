module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ActiveDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ExchangeStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Induction InductionSyntaxProof MatrixSyntaxProof
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  apply OriginalDecodedRank.SupportProof.pairCases left _
  intro beta j Theta st sp hj hl
  rw [acceptedRename]
  have henvj := renameInto henv j Theta hj
  have hedgej := renameInto hedge j Theta hj
  have ihj := renameInto ih j Theta hj
  have haj := renameInto ha j Theta hj
  have hpj := renameInto hp j Theta hj
  rw [environmentRename] at henvj
  rw [edgeRename] at hedgej
  rw [belowRawRename] at ihj
  rw [acceptedRename] at haj
  rw [plainRename] at hpj
  apply OriginalDecodedRank.SupportProof.pairCases (right.relabel j) _
  intro eta k Xi tt tp hk hr
  rw [acceptedRename]
  have henvk := renameInto henvj k Xi hk
  have hedgek := renameInto hedgej k Xi hk
  have ihk := renameInto ihj k Xi hk
  have hak := renameInto haj k Xi hk
  have hpk := renameInto hpj k Xi hk
  rw [environmentRename] at henvk
  rw [edgeRename] at hedgek
  rw [belowRawRename] at ihk
  rw [acceptedRename] at hak
  rw [plainRename] at hpk
  have hlk := renameInto hl k Xi hk
  rw [graph2Rename] at hlk
  have hs := OriginalDecodedSuccessShape.CoreProof.successShape n arity
    ((node.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    (st.relabel k) (sp.relabel k) tt tp ((window.relabel j).relabel k)
    (andLeft hedgek) hlk hr (andRight (andRight (andRight hedgek)))
  exact ActiveDispatchProof.preserved n arity arguments
    ((left.relabel j).relabel k) ((right.relabel j).relabel k) ((node.relabel j).relabel k)
    ((window.relabel j).relabel k) ((typ.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((context.relabel j).relabel k) ((symbols.relabel j).relabel k) ((types.relabel j).relabel k)
    (st.relabel k) tt (pairLeft _ _ _ hlk) (pairLeft _ _ _ hr) (andLeft hs) (andRight hs)
    henvk hedgek ihk hak hpk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ExchangeStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ExchangeStepProof
