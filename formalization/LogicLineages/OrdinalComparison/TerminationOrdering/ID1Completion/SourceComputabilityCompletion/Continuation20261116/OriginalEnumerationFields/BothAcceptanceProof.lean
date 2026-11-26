module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalAcceptanceSupportProof
open Continuation20261114.HeadWindowBooleanRange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leftOne {k : Nat} (p q : Program k) (xs : Fin k → OTerm alpha)
    (hr : ProgramRangeProof.Ranged p)
    (h : Nonempty (Derivation body Delta (programGraph (both p q) (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs)) := by
  apply programCases p xs _
  intro beta j Theta value hj hp
  simp only [programRename,sucRelabel,zRelabel]
  have hh := renameInto h j Theta hj
  simp only [programRename,sucRelabel,zRelabel] at hh
  have hn : Nonempty (Derivation body Theta (eqn value z).not) := by
    have hz : Nonempty (Derivation body (eqn value z :: Theta) (eqn value z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hpz := outputTransport p value z (fun i => (xs i).relabel j) hz (withHyp hp (eqn value z))
    have hb := zeroBranchElim p (constant k 0) q (suc z) (fun i => (xs i).relabel j)
      hpz (withHyp hh (eqn value z))
    obtain ⟨he⟩ := valueUnique (constant k 0) (suc z) z (fun i => (xs i).relabel j)
      hb (constantValue 0 (fun i => (xs i).relabel j))
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩
  have he := SourceProof.nonzeroOne value (hr body beta Theta value (fun i => (xs i).relabel j) hp) hn
  exact outputTransport p value (suc z) (fun i => (xs i).relabel j) he hp

theorem rightOne {k : Nat} (p q : Program k) (xs : Fin k → OTerm alpha)
    (hr : ProgramRangeProof.Ranged p)
    (h : Nonempty (Derivation body Delta (programGraph (both p q) (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph q (suc z) xs)) :=
  successorBranchElim p (constant k 0) q (suc z) z xs (leftOne p q xs hr h) h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothAcceptanceProof
