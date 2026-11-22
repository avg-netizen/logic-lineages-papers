module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafTypeTest)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider argumentExists)

def typeOnlyHeadGuard (s : Settings) : Program 1 := conjunction (header 3 1) (leafTypeTest s)

def ExactCoverTypeOnlyHeadGuardNumeric : Prop :=
  ∀ (s : Settings) (raw : Nat),
    run (typeOnlyHeadGuard s) raw = 1 ↔ ∃ ty, unpackNode raw = some (3,[ty]) ∧ ty ∈ s.types

def ExactOpenCoverTypeOnlyHeadProvider : Prop :=
  ∀ (s : Settings) (M : Program 1) (body : Positive (Fin 1)),
    HeadProvider (typeLeafSharedMeasure M) (typeOnlyHeadGuard s) s body

def ExactOpenCoverTypeOnlyArgumentList : Prop :=
  ∀ (s : Settings) (M : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (raw : OTerm α),
    Nonempty (Derivation body Γ (unary (argumentReject (typeOnlyHeadGuard s)) z raw)) →
    Nonempty (Derivation body Γ (argumentExists (typeLeafSharedMeasure M) s raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
