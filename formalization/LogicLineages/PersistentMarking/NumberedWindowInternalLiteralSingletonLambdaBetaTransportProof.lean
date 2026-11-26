module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenBetaLambdaBodyTarget)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Replace the second input of a binary program graph along a derived
equation. `programGraph` is deliberately left unfoldable in this module. -/
theorem exact_OpenInstanceBodyTransport (p : Program 2) (out a s t : OTerm α)
    (same : D B Γ (eqn s t)) (held : D B Γ (programGraph p out ![a,s])) :
    D B Γ (programGraph p out ![a,t]) := by
  apply graphInputTransport B α 2 Γ _ out ![a,s] ![a,t] _ held
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact ⟨refl a⟩
  · rw [onEquality]; exact same

/-- The beta leaf delivers its instance graph at an abstract body term.
When that body is derivably a packed lambda node, the accepted target
is the rebuilt node, with the child computed at literal depth one. -/
theorem exact_OpenBetaLambdaBodyTargetAt (V : Program 1) (H : Program 2) (U : Program 3)
    (a body ty b b' r : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (shape : D B Γ (eqn body (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U (suc b') ![a,suc z,b]))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U)) (suc r) ![a,body])) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm ty b'))) :=
  exact_OpenBetaLambdaBodyTarget V H U a ty b b' r inserted typedNode child
    (exact_OpenInstanceBodyTransport (zeroDepthInstance (singletonLambda V H U)) (suc r) a body
      (rawLambdaTerm ty b) shape held)

#print axioms exact_OpenInstanceBodyTransport
#print axioms exact_OpenBetaLambdaBodyTargetAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
