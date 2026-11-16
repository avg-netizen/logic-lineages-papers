module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.BasicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.RankedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.BranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Continuation20261114
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open GuardedSourceSyntaxProof (numeralRename)

theorem basic (n : Nat) (arity : Fin n → Nat) (raw tag payload symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hb : Nonempty (Derivation body Delta ((eqn tag (numeral 0) ⊔ eqn tag (numeral 1)) ⊓ eqn payload (numeral 0)))) :
    Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) := by
  have go {Theta : List (Formula alpha)} (which : Fin 2)
      (hpt : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing raw tag payload)))
      (hwt : Nonempty (Derivation body Theta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
      (he : Nonempty (Derivation body Theta (eqn tag (numeral which.val))))
      (hz : Nonempty (Derivation body Theta (eqn payload (numeral 0)))) :
      Nonempty (Derivation body Theta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) := by
    have hpair : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing raw (numeral which.val) (numeral 0))) := by
      unfold graph2 programGraph at hpt ⊢
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Theta
        (OrdinaryArithmetic.graphFormula InternalPairing.pairing) raw ![tag,payload] ![numeral which.val,numeral 0] _ hpt
      intro i
      fin_cases i
      · rw [InternalSourceInversionSupportProof.onEquality]; exact he
      · rw [InternalSourceInversionSupportProof.onEquality]; exact hz
    exact WindowSourceHeadInclusion.BasicProof.proof n arity body alpha Theta which raw symbols types hpair hwt
  apply orCases (andLeft hb)
  · intro Theta inc he
    exact go 0 (weakenProof hp inc) (weakenProof hw inc) he (weakenProof (andRight hb) inc)
  · intro Theta inc he
    exact go 1 (weakenProof hp inc) (weakenProof hw inc) he (weakenProof (andRight hb) inc)

theorem unary (n : Nat) (arity : Fin n → Nat) (which : Fin 2) (raw tag payload symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hc : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral (which.val+2))))) :
    Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) :=
  WindowSourceHeadInclusion.UnaryProof.proof n arity body alpha Delta which raw payload symbols types hc
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral raw tag payload (which.val+2) hp he) hw

theorem application (n : Nat) (arity : Fin n → Nat) (raw tag payload symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral 4)))) :
    Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) := by
  have hl := OriginalEnumerationMembership.GuardPairProof.pairLiteral raw tag payload 4 hp he
  apply Continuation20261115.OriginalDecodedRank.SupportProof.pairCases payload _
  intro beta j Theta sigma tau hj hpair
  simp only [graph3Rename,numeralRename]
  have hlj := renameInto hl j Theta hj
  have hwj := renameInto hw j Theta hj
  simp only [graph2Rename,graph3Rename,numeralRename] at hlj hwj
  exact WindowSourceHeadInclusion.ApplicationProof.proof n arity body beta Theta
    (raw.relabel j) (payload.relabel j) sigma tau (symbols.relabel j) (types.relabel j) hlj hpair hwj

theorem ranked (n : Nat) (arity : Fin n → Nat) (raw tag payload symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral 5)))) :
    Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)) :=
  WindowSourceHeadInclusion.RankedProof.proof n arity body alpha Delta raw payload symbols types
    (OriginalEnumerationMembership.GuardPairProof.pairLiteral raw tag payload 5 hp he) hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.BranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.BranchProof
