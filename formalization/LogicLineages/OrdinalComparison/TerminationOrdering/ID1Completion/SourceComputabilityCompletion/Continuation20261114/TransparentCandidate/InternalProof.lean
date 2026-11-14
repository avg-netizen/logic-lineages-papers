module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem acceptedValue (T : Program 2) (input parameter : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 T (suc z) input parameter))) :
    Nonempty (Derivation body Delta (graph2 (candidate T) input input parameter)) :=
  successorBranchIntro T (InternalAcceptance.constantZero 2) (.projection 0)
    input z ![input,parameter] hT (projectionValue 0 ![input,parameter])

theorem rejectedValue (T : Program 2) (input parameter : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 T z input parameter))) :
    Nonempty (Derivation body Delta (graph2 (candidate T) z input parameter)) :=
  zeroBranchIntro T (InternalAcceptance.constantZero 2) (.projection 0)
    z ![input,parameter] hT (constantZeroValue ![input,parameter])

theorem acceptedGraph : Targets.AcceptedGraph := by
  intro T body alpha Delta input parameter out hT
  have hv := acceptedValue T input parameter hT
  constructor
  · intro h
    rw [equalEqn]
    exact valueUnique (candidate T) out input ![input,parameter] h hv
  · intro h
    rw [equalEqn] at h
    obtain ⟨h⟩ := h
    exact outputTransport (candidate T) input out ![input,parameter] ⟨symm h⟩ hv

theorem rejectedGraph : Targets.RejectedGraph := by
  intro T body alpha Delta input parameter out hT
  have hv := rejectedValue T input parameter hT
  constructor
  · intro h
    rw [equalEqn]
    exact valueUnique (candidate T) out z ![input,parameter] h hv
  · intro h
    rw [equalEqn] at h
    obtain ⟨h⟩ := h
    exact outputTransport (candidate T) z out ![input,parameter] ⟨symm h⟩ hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.InternalProof
