module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenBetaLambdaBodyTarget)
open NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof (exact_OpenSingletonLambdaRowZero)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof (exact_OpenAcceptedBetaSingletonSyntax)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rawLambdaTermRename {β : Type} (ty b : OTerm α) (j : α → β) :
    (rawLambdaTerm ty b).relabel j = rawLambdaTerm (ty.relabel j) (b.relabel j) :=
  namedRename 2 ty b j

/-- A successful installed beta computation on a lambda supplies its
successful child computation at depth one and the rebuilt target
equation. The continuation uses the written child program `U`. -/
theorem exact_OpenAcceptedBetaLambdaChild (V : Program 1) (H : Program 2) (U : Program 3)
    (a body ty b r : OTerm α) (goal : Formula α)
    (shape : D B Γ (eqn body (rawLambdaTerm ty b)))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph U (suc u) ![a.relabel j,suc z,b.relabel j]) →
      D B Δ (eqn (suc (r.relabel j)) (suc (rawLambdaTerm (ty.relabel j) u))) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let p := singletonLambda V H U
  let I := zeroDepthInstance p
  have canonical :
      D B Γ (programGraph I (suc r) ![a,rawLambdaTerm ty b]) :=
    exact_OpenInstanceBodyTransport I (suc r) a body (rawLambdaTerm ty b) shape held
  have transport : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph I (suc (r.relabel j))
        ![a.relabel j,rawLambdaTerm (ty.relabel j) (b.relabel j)]) := by
    intro β j Δ keep
    simpa only [programRename,binaryInputsRename,sucRelabel,rawLambdaTermRename] using
      renameInto canonical j Δ keep
  apply optionGraphCases U (![a,suc z,b] : Fin 3 → OTerm α) goal
  · intro β j Δ keep failed
    have accepted := transport β j Δ keep
    have child : D B Δ (programGraph U z ![a.relabel j,suc z,b.relabel j]) := by
      simpa only [tripleInputsRename,sucRelabel,zRelabel] using failed
    obtain ⟨inserted,lambdaNode⟩ :=
      exact_OpenAcceptedBetaSingletonSyntax V H U (a.relabel j)
        (rawLambdaTerm (ty.relabel j) (b.relabel j)) (r.relabel j) accepted
    have invalid := exact_OpenSingletonLambdaRowZero V H U (a.relabel j) z
      (ty.relabel j) (b.relabel j) inserted lambdaNode child
    have zero := exact_OpenZeroDepthInstance p (a.relabel j)
      (rawLambdaTerm (ty.relabel j) (b.relabel j)) z invalid
    obtain ⟨same⟩ := valueUnique I (suc (r.relabel j)) z
      ![a.relabel j,rawLambdaTerm (ty.relabel j) (b.relabel j)] accepted zero
    exact ⟨Derivation.explosion (sucNeZeroApply same)⟩
  · intro β j Δ u keep hit
    have accepted := transport β j Δ keep
    have child : D B Δ (programGraph U (suc u) ![a.relabel j,suc z,b.relabel j]) := by
      simpa only [tripleInputsRename,sucRelabel,zRelabel] using hit
    obtain ⟨inserted,lambdaNode⟩ :=
      exact_OpenAcceptedBetaSingletonSyntax V H U (a.relabel j)
        (rawLambdaTerm (ty.relabel j) (b.relabel j)) (r.relabel j) accepted
    exact use β j Δ u keep child
      (exact_OpenBetaLambdaBodyTarget V H U (a.relabel j) (ty.relabel j) (b.relabel j)
        u (r.relabel j) inserted lambdaNode child accepted)

#print axioms rawLambdaTermRename
#print axioms exact_OpenAcceptedBetaLambdaChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof
