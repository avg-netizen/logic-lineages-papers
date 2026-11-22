module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated lambdaSyntaxUpdate lambdaTape)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate auxTape)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasureUpdate)

def lambdaDispatch : Program 4 := binaryAfter equalityTest (unaryAfter cellHead currentKey) (literal 4 2)

def sharedUpdate (aux lam : Program 4) : Program 4 := branch lambdaDispatch aux lam

/-- The tag dispatcher works on the same original four physical inputs.
Each recursive program is a row update, not a new child-query callback. -/
def sharedSyntaxUpdate (V T : Program 1) : Program 4 :=
  sharedUpdate (auxSyntaxUpdate V T) (lambdaSyntaxUpdate V T)

def sharedMeasureUpdate (M : Program 1) : Program 4 :=
  sharedUpdate (measureUpdate M chosenCombine) (lambdaMeasureUpdate M)

def sharedSyntax (V T : Program 1) : Program 1 := selectedMeasure (sharedSyntaxUpdate V T)

def sharedMeasure (M : Program 1) : Program 1 := selectedMeasure (sharedMeasureUpdate M)

def ExactCoverSharedSyntaxStep : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = (syntaxBits n).1.toNat) →
    evaluate (sharedSyntaxUpdate V T) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = (syntaxBits (i+1)).1.toNat

def ExactCoverSharedSyntax : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
    TermSyntaxCalibrated (sharedSyntax V T)

def ExactCoverSharedMeasureStep : Prop :=
  ∀ (M : Program 1), TermMeasureCalibrated M →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = Encodable.encode (bounds n).1) →
    evaluate (sharedMeasureUpdate M) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = Encodable.encode (bounds (i+1)).1

def ExactCoverSharedMeasure : Prop :=
  ∀ (M : Program 1), TermMeasureCalibrated M → TermMeasureCalibrated (sharedMeasure M)

/-- Both directions at the literal lambda tape, with no change to its old
table value or provisional output. Applies to both chosen shared updaters. -/
def ExactOpenCoverSharedLambdaCut : Prop :=
  ∀ (aux lam : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q old out : OTerm α),
    Nonempty (Derivation body Γ (programGraph (sharedUpdate aux lam) out (lambdaTape ty q old))) ↔
    Nonempty (Derivation body Γ (programGraph lam out (lambdaTape ty q old)))

/-- The actual sparse tag 6 is not tag 2. Keep the entire same-tape
update, rather than compare scratch reports from independent recursors. -/
def ExactOpenCoverSharedAuxCut : Prop :=
  ∀ (aux lam : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old out : OTerm α),
    Nonempty (Derivation body Γ (programGraph (sharedUpdate aux lam) out (auxTape dom cod fn arg old))) ↔
    Nonempty (Derivation body Γ (programGraph aux out (auxTape dom cod fn arg old)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
