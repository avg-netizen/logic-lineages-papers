module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftRuntimeProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- The original source window and types are closed, while Gamma's code
and all values remain symbolic. The normalized membership slice derives
the only generic arithmetic guard absent from the source antecedent. -/
theorem runtimeLift (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (oldStep : Program 4)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (parameter gammaCode x y a certificate out other lifted : OTerm α)
    (h : Nonempty (Derivation body Delta
      (runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData data) oldStep sigma tau parameter gammaCode
        x y a certificate out other lifted))) :
    Nonempty (Derivation body Delta
      (result (normalizeData data) oldStep (numeral (typeNumber tau)) out other lifted parameter)) := by
  let normalized := normalizeData data
  have hp := andLeft h
  have hi := andLeft (andRight h)
  have hlift := andRight (andRight h)
  have hmArrow := andLeft (InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    normalized.oldRepresentative (InternalOriginalUniformDescentSelection.validity normalized)
    normalized.member x (numeral (typeNumber (.arrow sigma tau))) parameter (andLeft hi))
  have hm := InternalOriginalUniformApplicationTypingMembershipProof.codomainMembership
    n arity data hc symbols S table hS sigma tau parameter gammaCode hp hmArrow
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral
    (body := body) (Gamma := Delta) (α := α) sigma tau
  have hcore : Nonempty (Derivation body Delta
      (corePremises normalized oldStep (numeral (typeNumber (.arrow sigma tau)))
        (numeral (typeNumber sigma)) (numeral (typeNumber tau))
        x y a certificate out other parameter)) := andIntro (andIntro har hm) hi
  exact andIntro
    (InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof.applicationLift
      normalized oldStep (numeral (typeNumber (.arrow sigma tau)))
      (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      x y a certificate out other lifted parameter hcore hlift)
    (InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof.applicationTypedOutputs
      normalized oldStep (numeral (typeNumber (.arrow sigma tau)))
      (numeral (typeNumber sigma)) (numeral (typeNumber tau))
      x y a certificate out other parameter hcore)

theorem actualOriginalUniformNormalizedQuotientEdgeApplicationLift :
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalUniformNormalizedQuotientEdgeApplicationLift := by
  intro n arity data hc oldStep symbols S table hS body α Delta sigma tau
    parameter gammaCode x y a certificate out other lifted
  let P := runtimePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (normalizeData data) oldStep sigma tau parameter gammaCode x y a certificate out other lifted
  obtain ⟨h⟩ := runtimeLift (body := body) (Delta := P :: Delta)
    n arity data hc oldStep symbols S table hS sigma tau
    parameter gammaCode x y a certificate out other lifted
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftRuntimeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftRuntimeProof
