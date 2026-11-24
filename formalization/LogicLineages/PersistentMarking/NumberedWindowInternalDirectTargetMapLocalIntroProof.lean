module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursionProof (nilValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalDirectInsertedTargetsMapTargets
  (atHead targetBase targetStep tailPayload joined scratchTargets parserPayload insertedTargets)
open NumberedWindowInternalDirectTargetMapIntroTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onHead (p : Program 1) (o h t : OTerm α)
    (ok : D B Γ (unary p o h)) : D B Γ (programGraph (atHead p) o ![h,t]) := by
  apply compositionValue p (Fin.cons (.projection 0) Fin.elim0) o ![h,t] ![h] ok
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![h,t]

theorem exact_OpenTargetProjectionNil : ExactOpenTargetProjectionNil := by
  intro B α Γ
  exact nilValue targetBase targetStep (suc z) Fin.elim0 (literalGraph 1 Fin.elim0)

theorem exact_OpenTargetProjectionStepIntro : ExactOpenTargetProjectionStepIntro := by
  intro B α Γ row target prior out guard f0 cell
  let xs : Fin 2 → OTerm α := ![row,suc prior]
  have guardAtHead := onHead (guardAt 4) (suc z) row (suc prior) guard
  have targetAtHead := onHead (field 0) target row (suc prior) f0
  have tailAt : D B Γ (programGraph tailPayload prior xs) := by
    unfold tailPayload
    rw [exact_DispatchControlAST.2.2.1]
    apply compositionValue predecessor (Fin.cons (.projection 1) Fin.elim0)
      prior xs ![suc prior] (predecessorSuccessor prior)
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  have mapped : D B Γ (programGraph joined out xs) := by
    apply compositionValue consCode (Fin.cons (atHead (field 0)) (Fin.cons tailPayload Fin.elim0))
      out xs ![target,prior] cell
    intro i
    exact Fin.cases targetAtHead (Fin.cases tailAt (fun k => Fin.elim0 k)) i
  let made : Program 2 := .composition .succ (Fin.cons joined Fin.elim0)
  have pushed : D B Γ (programGraph made (suc out) xs) := by
    apply compositionValue .succ (Fin.cons joined Fin.elim0) (suc out) xs ![out]
      (successorValue ![out])
    intro i
    obtain rfl := Fin.eq_zero i
    exact mapped
  have inner := successorBranchIntro (.projection 1) (constantZero 2) made
    (suc out) prior xs (projectionValue 1 xs) pushed
  have selected := conjunctionAccept (atHead (guardAt 4)) (literal 2 1)
    xs guardAtHead (literalGraph 1 xs)
  simp only [targetStep,exact_DispatchControlAST.2.2.2.2.1,
    exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.1]
  exact successorBranchIntro (conjunction (atHead (guardAt 4)) (literal 2 1))
    (constantZero 2) (branch (.projection 1) (constantZero 2) made) (suc out)
    z xs selected inner

theorem exact_OpenRawTargetProjectionIntro : ExactOpenRawTargetProjectionIntro := by
  intro B α Γ raw scratch projected rawView map
  let xs : Fin 1 → OTerm α := ![raw]
  have decoded : D B Γ (programGraph parserPayload scratch xs) := by
    unfold parserPayload
    rw [exact_DispatchControlAST.2.2.1]
    apply compositionValue predecessor (Fin.cons parser Fin.elim0)
      scratch xs ![suc scratch] (predecessorSuccessor scratch)
    intro i
    obtain rfl := Fin.eq_zero i
    exact rawView
  have lifted : D B Γ (programGraph (.composition scratchTargets (Fin.cons parserPayload Fin.elim0))
      (suc projected) xs) := by
    apply compositionValue scratchTargets (Fin.cons parserPayload Fin.elim0) (suc projected)
      xs ![scratch] map
    intro i
    obtain rfl := Fin.eq_zero i
    exact decoded
  simp only [insertedTargets,unary,exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.1]
  exact successorBranchIntro parser (constantZero 1) (.composition scratchTargets (Fin.cons parserPayload Fin.elim0))
    (suc projected) scratch xs rawView lifted

#print axioms exact_OpenTargetProjectionNil
#print axioms exact_OpenTargetProjectionStepIntro
#print axioms exact_OpenRawTargetProjectionIntro

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
