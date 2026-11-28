module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (singletonSyntax)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof
  (exact_OpenSingletonLambdaRowZero exact_OpenSingletonBoundGuardZero
    exact_OpenSingletonLambdaGuardZero)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem requiredGuard {n : Nat} (P : Program n) (xs : Fin n → OTerm α)
    (r : OTerm α) (guard : Formula α)
    (held : D B Γ (programGraph P (suc r) xs))
    (failed : D B (guard.not :: Γ) (programGraph P z xs)) :
    D B Γ guard := by
  obtain ⟨held⟩ := held
  obtain ⟨same⟩ := valueUnique P (suc r) z xs ⟨addHyp held guard.not⟩ failed
  exact ⟨disjunctionElimination (excludedMiddle guard)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply same)))⟩

private theorem syntaxZeroOfRejection (V : Program 1) (a d q : OTerm α)
    (rejected : D B Γ (bit (singletonSyntax V) ![a,d,q]).not) :
    D B Γ (programGraph (singletonSyntax V) z ![a,d,q]) :=
  conjunctionReject (onRaw V 0) (onRaw V 2) ![a,d,q] rejected

private theorem tapeSyntax (V : Program 1) (xs : Fin 3 → OTerm α) (i : Fin 3)
    (held : D B Γ (bit (onRaw V i) xs)) :
    D B Γ (unary V (suc z) (xs i)) := by
  apply compositionRecover V (fun _ : Fin 1 => .projection i) (suc z) xs ![xs i] held
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

private theorem syntaxParts (V : Program 1) (a d q : OTerm α)
    (held : D B Γ (bit (singletonSyntax V) ![a,d,q])) :
    D B Γ (unary V (suc z) a) ∧ D B Γ (unary V (suc z) q) := by
  let xs : Fin 3 → OTerm α := ![a,d,q]
  obtain ⟨both⟩ := conjunctionRecover (onRaw V 0) (onRaw V 2) xs held
  exact ⟨tapeSyntax V xs 0 ⟨Derivation.conjunctionLeft both⟩,
    tapeSyntax V xs 2 ⟨Derivation.conjunctionRight both⟩⟩

/-- A successful zero-depth instance carries both outer syntax checks. -/
theorem exact_OpenAcceptedBetaSingletonSyntax (V : Program 1) (H : Program 2)
    (U : Program 3) (a q r : OTerm α)
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U))
      (suc r) ![a,q])) :
    D B Γ (unary V (suc z) a) ∧ D B Γ (unary V (suc z) q) := by
  let p := singletonLambda V H U
  let I := zeroDepthInstance p
  let guard := bit (singletonSyntax V) ![a,z,q]
  have zero : D B (guard.not :: Γ) (programGraph I z ![a,q]) := by
    have rejected := syntaxZeroOfRejection (B := B) (Γ := guard.not :: Γ) V a z q
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact exact_OpenZeroDepthInstance p a q z
      (exact_OpenSingletonLambdaGuardZero V H U a z q rejected)
  exact syntaxParts V a z q (requiredGuard I ![a,q] r guard held zero)

/-- Success of the installed instance on a lambda supplies the syntax
bits for the replacement, that lambda, and its child when the child
program is the guarded singleton bound dispatch. -/
theorem exact_OpenAcceptedBetaSingletonLambdaChildGuards (V : Program 1) (H : Program 2)
    (W : Program 3) (a body ty b r : OTerm α)
    (shape : D B Γ (eqn body (rawLambdaTerm ty b)))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body])) :
    D B Γ (unary V (suc z) a) ∧
    D B Γ (unary V (suc z) (rawLambdaTerm ty b)) ∧
    D B Γ (unary V (suc z) b) := by
  let U := singletonBound V H W
  let p := singletonLambda V H U
  let I := zeroDepthInstance p
  let node := rawLambdaTerm ty b
  have accepted : D B Γ (programGraph I (suc r) ![a,node]) :=
    exact_OpenInstanceBodyTransport I (suc r) a body node shape held
  obtain ⟨inserted,lambdaNode⟩ := exact_OpenAcceptedBetaSingletonSyntax V H U a node r accepted
  let inner := bit (singletonSyntax V) ![a,suc z,b]
  have innerZero : D B (inner.not :: Γ) (programGraph I z ![a,node]) := by
    have rejected := syntaxZeroOfRejection (B := B) (Γ := inner.not :: Γ) V a (suc z) b
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have child := exact_OpenSingletonBoundGuardZero V H W a (suc z) b rejected
    obtain ⟨inserted⟩ := inserted
    obtain ⟨lambdaNode⟩ := lambdaNode
    exact exact_OpenZeroDepthInstance p a node z
      (exact_OpenSingletonLambdaRowZero V H U a z ty b
        ⟨addHyp inserted inner.not⟩ ⟨addHyp lambdaNode inner.not⟩ child)
  have innerHeld := requiredGuard I ![a,node] r inner accepted innerZero
  exact ⟨inserted,lambdaNode,(syntaxParts V a (suc z) b innerHeld).2⟩

#print axioms exact_OpenAcceptedBetaSingletonSyntax
#print axioms exact_OpenAcceptedBetaSingletonLambdaChildGuards
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof
