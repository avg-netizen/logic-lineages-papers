module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open ID1Completion.InternalAcceptance (branch)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne maximum)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs)
open NumberedWindowInternalCoverOrdinaryMeasureTargets
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypePrograms)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets

def numberedArgCode (A : Program 1) (i : Nat) : Program 1 :=
  callOne (selectedArgsMeasure A) (field i)

def numberedMeasureApply (A : Program 1) : Program 1 :=
  .composition numberedJoin ![field 2,numberedArgCode A 3,numberedArgCode A 4]

def numberedMeasureBase (M A : Program 1) : Program 1 :=
  branch (header 5 5) M (numberedMeasureApply A)

abbrev numberedSharedMeasure (M A : Program 1) : Program 1 :=
  ordinarySharedMeasure (numberedMeasureBase M A) A

abbrev numberedMeasuredPrograms (s : Settings) (V TV M A : Program 1) (B : Program 2) (T : Program 1) : Programs :=
  numberedTypePrograms s V TV (numberedMeasureBase M A) A B T

def ExactCoverNumberedMeasureBase : Prop :=
  ∀ M A : Program 1, TermMeasureCalibrated M → ArgsMeasureCalibrated A →
    TermMeasureCalibrated (numberedMeasureBase M A)

def ExactCoverNumberedSharedMeasure : Prop :=
  ∀ M A : Program 1, TermMeasureCalibrated M → ArgsMeasureCalibrated A →
    TermMeasureCalibrated (numberedSharedMeasure M A)

def ExactOpenCoverNumberedMeasureCut : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k l r p : OTerm α),
    Nonempty (Derivation body Γ (unary (numberedSharedMeasure M A) p (numberedTerm h ty k l r))) →
    Nonempty (Derivation body Γ (unary (numberedMeasureApply A) p (numberedTerm h ty k l r)))

structure NumberedMeasuredArgs (A : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (k l r p ml mr dl dr wl wr width : OTerm α) : Prop where
  leftReport : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) ml l))
  rightReport : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) mr r))
  leftPair : Nonempty (Derivation body Γ (codePair ml dl wl))
  rightPair : Nonempty (Derivation body Γ (codePair mr dr wr))
  paid : NumberedJoinBounds body Γ p k dl dr wl wr width

def ExactOpenCoverNumberedMeasuredArgs : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k l r p : OTerm α) (Q : Formula α),
    Nonempty (Derivation body Γ (unary (numberedSharedMeasure M A) p (numberedTerm h ty k l r))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ml mr dl dr wl wr width : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      NumberedMeasuredArgs A body Δ (k.relabel j) (l.relabel j) (r.relabel j) (p.relabel j)
        ml mr dl dr wl wr width →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
