module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open Induction InductionSyntaxProof MatrixSyntaxProof InductionBindingProof
open Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromAllRaw (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source target node window context symbols types : OTerm alpha)
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity source target node window)))
    (h : Nonempty (Derivation body Delta (AtRaw n arity source))) :
    Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      arguments source target context)) := by
  apply PlainAwareStructuralBindingProof.transferIntro
  intro beta j Theta typ gamma hj ha hp
  have henv' := renameInto henv j Theta hj
  have hedge' := renameInto hedge j Theta hj
  have h' := renameInto h j Theta hj
  rw [environmentRename] at henv'
  rw [edgeRename] at hedge'
  rw [atRawRename] at h'
  obtain ⟨hr⟩ := atModeApply n arity arguments (source.relabel j) typ (target.relabel j) gamma
    (context.relabel j) (symbols.relabel j) (types.relabel j) (window.relabel j) (node.relabel j)
    (atRawMode n arity arguments (source.relabel j) h')
  have ha' : Nonempty (Derivation body Theta
      (accepted n arity arguments typ (source.relabel j) gamma (context.relabel j))) := by
    cases arguments <;> exact ha
  have hp' : Nonempty (Derivation body Theta
      (plain n arity arguments typ (target.relabel j) gamma)) := hp
  obtain ⟨he⟩ := andIntro henv' hedge'
  obtain ⟨hh⟩ := andIntro ha' hp'
  have out : Nonempty (Derivation body Theta
      (accepted n arity arguments typ (target.relabel j) gamma (context.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.implicationElimination hr he) hh⟩
  cases arguments <;> exact out

theorem fromBelow (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (parent source target node window context symbols types : OTerm alpha)
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity source target node window)))
    (hbelow : Nonempty (Derivation body Delta (BelowRaw n arity parent)))
    (hless : Nonempty (Derivation body Delta (InternalLessThan.strictLess source parent))) :
    Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      arguments source target context)) :=
  fromAllRaw n arity arguments source target node window context symbols types henv hedge
    (belowRawAt n arity parent source hbelow hless)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
