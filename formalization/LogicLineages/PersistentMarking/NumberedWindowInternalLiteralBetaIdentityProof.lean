module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictClassRawSourceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding varBind)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast fullAuxiliaryDecorator)
open NumberedWindowInternalLiteralStrictClassRawSourceProof (exact_OpenStrictClassStackReport)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralStrictForkRetapeProof (exact_OpenStrictRetapeContext)
open NumberedWindowInternalLiteralStrictImageRetapeProof (exact_OpenStrictRetapeTypeAndRaw)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenPhysicalBetaBoundZero)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof (exact_OpenAcceptedBetaSingletonSyntax)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The installed top-beta row for the discharged variable emits the
argument's own address. Its target and operand are compared using the
same guarded child least graph. -/
theorem exact_OpenAlignedIdentityBetaAddress (L₀ : Program 3)
    (V : Program 1) (H : Program 2) (U : Program 3)
    {x u ctx result dom cod fn arg sc st after q r d e f a bind body y bodyType : OTerm α}
    (parsed : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg))
    (row : AlignedBetaRow L₀ (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀)))
      (zeroDepthInstance (singletonLambda V H U)) B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (scope : D B Γ (eqn sc ctx))
    (sameType : D B Γ (eqn st d))
    (identity : D B Γ (eqn body (boundTerm bodyType z))) :
    D B Γ (eqn u y) := by
  let I := zeroDepthInstance (singletonLambda V H U)
  let node := boundTerm bodyType z
  have held := exact_OpenInstanceBodyTransport I (suc r) a body node identity row.instanceRun
  obtain ⟨inserted,typedNode⟩ := exact_OpenAcceptedBetaSingletonSyntax V H U a node r held
  have run : D B Γ (programGraph I (suc a) ![a,node]) :=
    exact_OpenPhysicalBetaBoundZero V H (singletonLambdaDispatch U) a bodyType inserted typedNode
  obtain ⟨output⟩ := valueUnique I (suc r) (suc a) ![a,node] held run
  let child := childGuardedLeast L₀
  have outer := exact_OpenStrictClassStackReport L₀ sc st r after row.targetClass
  obtain ⟨stack⟩ := exact_OpenLiteralAuxClassLeastReport child sc st r after outer
  have target := exact_OpenStrictRetapeContext child sc ctx st r (suc after)
    scope ⟨Derivation.conjunctionLeft stack⟩
  have compared := exact_OpenStrictRetapeTypeAndRaw child ctx st d r a (suc after)
    sameType ⟨cancelSuc output⟩ target
  obtain ⟨selected⟩ := valueUnique child (suc after) (suc arg) ![ctx,d,a] compared row.argumentClass
  obtain ⟨ty⟩ := sameType
  obtain ⟨domain⟩ := row.domain
  obtain ⟨targetAddress⟩ := rebuildAddress y sc st after ctx dom arg row.targetAddress scope
    ⟨trans ty domain⟩ ⟨cancelSuc selected⟩
  obtain ⟨inputs⟩ := parsed
  unfold parsedApplicationInputs at inputs
  let reports := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight inputs))
  let equalities := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight reports))
  have argumentAddress : Derivation B Γ (eqn u (addressTerm ctx dom arg)) :=
    Derivation.conjunctionRight (Derivation.conjunctionRight equalities)
  exact ⟨trans argumentAddress (symm targetAddress)⟩

/-- Transport the original argument's computability at the common type
to the actual emitted reduct of this identity row. -/
theorem exact_OpenAlignedIdentityBetaComputability (L₀ : Program 3)
    (V : Program 1) (H : Program 2) (U : Program 3) (p : Program 3) (τ : Ty)
    {x u ctx result dom cod fn arg sc st after q r d e f a bind body y bodyType : OTerm α}
    (parsed : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg))
    (row : AlignedBetaRow L₀ (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀)))
      (zeroDepthInstance (singletonLambda V H U)) B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (scope : D B Γ (eqn sc ctx))
    (sameType : D B Γ (eqn st d))
    (identity : D B Γ (eqn body (boundTerm bodyType z)))
    (argument : D B Γ (formula p τ u)) : D B Γ (formula p τ y) := by
  obtain ⟨same⟩ := exact_OpenAlignedIdentityBetaAddress L₀ V H U parsed row scope sameType identity
  obtain ⟨computed⟩ := argument
  let θ : Formula (α ⊕ Fin 1) := formula p τ (.var (.inr 0))
  have atTerm (x : OTerm α) : instantiate θ (emb x) = formula p τ x := by
    change instantiate (formula p τ (.var (.inr 0))) (emb x) = formula p τ x
    rw [instantiate,bindEmbedding,exact_FormulaSubstitution p τ (α ⊕ Fin 1) α _,varBind]
  have moved := Derivation.equalityElimination θ (emb u) (emb y) same (by rw [atTerm]; exact computed)
  rw [atTerm] at moved
  exact ⟨moved⟩

#print axioms exact_OpenAlignedIdentityBetaAddress
#print axioms exact_OpenAlignedIdentityBetaComputability
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityProof
