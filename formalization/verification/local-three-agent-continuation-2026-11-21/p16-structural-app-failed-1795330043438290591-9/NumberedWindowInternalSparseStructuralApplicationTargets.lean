module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalAuxExchangeMemoGuardedTargets (paired)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)

def syntaxWindow (baseW : Program 3) (V : Program 1) : Program 3 :=
  conjunction baseW (.composition V (fun _ : Fin 1 => .projection 2))

abbrev window (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1) :=
  coveredWindow C s (syntaxWindow baseW V)

abbrev exchange (C : Program 3) (s : Settings) (base : Program 2) (V : Program 1) :=
  guardedExchange C s (paired base V)

def ExactSyntaxWindowCalibration : Prop := ∀ (s : Settings) (baseW : Program 3) (V : Program 1),
  ActualPackedWindow s baseW → ActualRawSyntax V → ActualPackedWindow s (syntaxWindow baseW V)

def ExactWindowSyntaxReport : Prop := ∀ (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α),
    Nonempty (Derivation body Γ ((windowAt (window C s baseW V) ctx ty seed).imp (syntaxOne V seed)))

def parentReports {α : Type} (C : Program 3) (s : Settings) (W : Program 3)
    (ctx cod a b left right : OTerm α) : Formula α :=
  (windowAt W ctx cod a ⊓ windowAt W ctx cod b) ⊓
    (unary (coverOption C s) left a ⊓ (unary (coverOption C s) right b ⊓ eqn left right))

/-- Preserve the actual edge and the selected application result, on the same
argument. The parent window calls and the two checked cover outputs are explicit. -/
def FunctionEdgeAt (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg left right value : OTerm α),
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    let E := edge4 X W
    let source := acceptEdge E ctx (rawCons dom cod) f g ⊓ parentReports C s W ctx cod a b left right
    Nonempty (Derivation body Γ (source.imp (acceptEdge E ctx cod a b ⊓
      ((leastGraph C X W s ctx cod a value).imp (leastGraph C X W s ctx cod b value)))))

def ExactStructuralFunctionEdge : Prop :=
  ∀ (C : Program 3) (s : Settings) (base : Program 2) (baseW : Program 3) (V : Program 1),
    FunctionEdgeAt C s (exchange C s base V) (window C s baseW V)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
