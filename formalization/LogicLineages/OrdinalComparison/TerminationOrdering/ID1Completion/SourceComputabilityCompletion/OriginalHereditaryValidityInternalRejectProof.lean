module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof OriginalHereditaryValidityInternalStateSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open OriginalHereditaryValidityInternalRejectSupportProof

theorem actualOriginalHereditaryRejectTransition :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryRejectTransition := by
  intro body s t m α state out
  let A := (graph1 status (numeral 1) state).not
  let B := LiveWork state ⊓ (graph1 (nodeCheck s t m) (numeral 1) state).not
  let H := A ⊔ B
  have ha : Nonempty (Derivation body (A :: [H]) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: [H]) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨da⟩ := graphAtValue (transition s t m) out z (Fin.cons state Fin.elim0)
    (rejectStatus s t m state ha)
  obtain ⟨db⟩ := graphAtValue (transition s t m) out z (Fin.cons state Fin.elim0)
    (rejectNode s t m state (andLeft hb) (andRight hb))
  exact ⟨Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (Derivation.implicationIntroduction da) (Derivation.implicationIntroduction db))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectProof
