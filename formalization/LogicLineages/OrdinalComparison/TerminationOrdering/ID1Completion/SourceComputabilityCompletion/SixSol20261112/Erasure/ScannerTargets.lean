module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Read-only observation of the unchanged original edge state. Its three
original selectors and separate parameter feed the actual mixed recognizer. -/
def stateRecognizes (source : Program 2) (leaf : Program 4) : Program 2 :=
 InternalParameterizedApplicationResultStack.wireP
  (OriginalMixedDirectBottomTrace.recognizes source leaf)
  ![InternalApplicationCertificateConstructors.source,target,step]

/-- Every actual scanner step preserves recognition. Failed guards preserve
the complete state; successful guards must agree with the actual application
child despite the recognizer's lambda-first priority. -/
def ScannerPreservesRecognition : Prop :=
 ∀ (source : Program 2) (leaf : Program 4) (endpoint : Program 6)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (state next parameter : OTerm alpha),
 Nonempty (Derivation body Delta
  (graph2 (InternalParameterizedApplicationStepChecker.transitionP endpoint) next state parameter)) →
 Nonempty (Derivation body Delta
  (graph2 (stateRecognizes source leaf) (suc z) state parameter)) →
 Nonempty (Derivation body Delta
  (graph2 (stateRecognizes source leaf) (suc z) next parameter))

/-- Recognition supplies the ACTUAL original selected checker, for every
endpoint/source/leaf. Original path, edge state and parameter are untouched;
no supplied scanner invariant, source edge, simulation or repeat law occurs. -/
def RecognizedSelectedChecker : Prop :=
 ∀ (source : Program 2) (leaf : Program 4) (endpoint : Program 6)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta
  (graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf) (suc z) s t cert parameter)) →
 Nonempty (Derivation body Delta
  (graph4 (InternalParameterizedApplicationStepChecker.checkerP endpoint leaf)
   (suc z) s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerTargets
