module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaBoundIndexProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl trans congSuc)
open ID1Completion.InternalAdditionLawsProof (add congAddLeft)
open ID1Completion.InternalMultiplicationLawsProof (congAddRight)
open ID1Completion.InternalSquareRootArithmetic (square)
open ID1Completion.InternalSquareRootArithmeticSupportProof (squareCongr)
open ID1Completion.InternalQuotientComparisonProof (zeroLessSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (exact_OpenSingletonBoundAtZero)
open NumberedWindowInternalLiteralSingletonBoundOpenLowerProof (exact_OpenSingletonBoundAboveDepth)
open NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof (boundTermRename)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof (exact_OpenAcceptedBetaSingletonSyntax)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consCongr {h h' t t' : OTerm α}
    (head : Derivation B Γ (eqn h h')) (tail : Derivation B Γ (eqn t t')) :
    Derivation B Γ (eqn (rawCons h t) (rawCons h' t')) :=
  congSuc (trans
    (congAddRight h (squareCongr (trans (congAddRight t head) (congAddLeft h' tail))))
    (congAddLeft (square (add h' t')) head))

private theorem indexCongr (t : OTerm α) {i j : OTerm α}
    (indices : Derivation B Γ (eqn i j)) :
    Derivation B Γ (eqn (boundTerm t i) (boundTerm t j)) :=
  consCongr (refl (numeral 1))
    (consCongr (refl t) (consCongr indices (refl z)))

/-- At an accepted bound body the actual instance returns the replacement
at index zero and the predecessor-index node at a successor. Each
continuation receives the equation for the unchanged accepted output. -/
theorem exact_OpenAcceptedBetaBoundIndexCases (V : Program 1) (H : Program 2) (U : Program 3)
    (a body t i r : OTerm α) (goal : Formula α)
    (shape : D B Γ (eqn body (boundTerm t i)))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U))
      (suc r) ![a,body]))
    (atZero : D B (eqn i z :: Γ) (eqn (suc r) (suc a)) → D B (eqn i z :: Γ) goal)
    (atSuccessor : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (eqn (i.relabel ρ) (suc j)) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (boundTerm (t.relabel ρ) j))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  let p := singletonLambda V H U
  let I := zeroDepthInstance p
  apply zeroSuccessorCases Γ i goal
  · let Z := eqn i z
    obtain ⟨shape⟩ := shape
    obtain ⟨held⟩ := held
    have atZ : Derivation B (Z :: Γ) (eqn body (boundTerm t z)) :=
      trans (addHyp shape Z) (indexCongr t (Derivation.hypothesis List.mem_cons_self))
    have accepted := exact_OpenInstanceBodyTransport I (suc r) a body (boundTerm t z)
      ⟨atZ⟩ ⟨addHyp held Z⟩
    obtain ⟨inserted,typedNode⟩ := exact_OpenAcceptedBetaSingletonSyntax V H U a (boundTerm t z) r accepted
    have run := exact_OpenZeroDepthInstance p a (boundTerm t z) (suc a)
      (exact_OpenSingletonBoundAtZero V H (singletonLambdaDispatch U) a t inserted typedNode)
    exact atZero (valueUnique I (suc r) (suc a) ![a,boundTerm t z] accepted run)
  · intro β ρ Δ j keep indices
    have shape' : D B Δ (eqn (body.relabel ρ) (boundTerm (t.relabel ρ) (i.relabel ρ))) := by
      simpa only [eqnRelabel,boundTermRename] using renameInto shape ρ Δ keep
    have held' : D B Δ (programGraph I (suc (r.relabel ρ)) ![a.relabel ρ,body.relabel ρ]) := by
      simpa only [programRename,binaryInputsRename,sucRelabel] using renameInto held ρ Δ keep
    obtain ⟨decoded⟩ := shape'
    obtain ⟨idx⟩ := indices
    have exactShape := trans decoded (indexCongr (t.relabel ρ) idx)
    have accepted := exact_OpenInstanceBodyTransport I (suc (r.relabel ρ)) (a.relabel ρ)
      (body.relabel ρ) (boundTerm (t.relabel ρ) (suc j)) ⟨exactShape⟩ held'
    obtain ⟨inserted,typedNode⟩ := exact_OpenAcceptedBetaSingletonSyntax V H U
      (a.relabel ρ) (boundTerm (t.relabel ρ) (suc j)) (r.relabel ρ) accepted
    have run := exact_OpenZeroDepthInstance p (a.relabel ρ) (boundTerm (t.relabel ρ) (suc j))
      (suc (boundTerm (t.relabel ρ) j))
      (exact_OpenSingletonBoundAboveDepth V H (singletonLambdaDispatch U) (a.relabel ρ)
        z (t.relabel ρ) j inserted typedNode ⟨zeroLessSuccessor j⟩)
    exact atSuccessor β ρ Δ j keep ⟨idx⟩
      (valueUnique I (suc (r.relabel ρ)) (suc (boundTerm (t.relabel ρ) j))
        ![a.relabel ρ,boundTerm (t.relabel ρ) (suc j)] accepted run)

#print axioms exact_OpenAcceptedBetaBoundIndexCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaBoundIndexProof
