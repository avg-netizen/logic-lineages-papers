module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- External finite indexing of the four literal OTHER root tags only. -/
def tag (i : Fin 4) : Nat := if i.val = 0 then 0 else i.val + 2
def bottomFlag (i : Fin 4) : Nat := if i.val = 1 then 1 else 0

/-- Actual original observer value; source and literal tag only. -/
def ActualShape : Prop :=
 ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (i : Fin 4) (input parameter shape : OTerm alpha),
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i)) input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing shape (numeral (tag i)) (numeral 0))) →
 Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark shape input))

/-- Actual original observer value; source and literal tag only. -/
def ActualNeutrality : Prop :=
 ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (i : Fin 4) (input parameter : OTerm alpha),
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i)) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark (numeral 0) input))

/-- Actual original observer value; source and literal tag only. -/
def ActualSpine : Prop :=
 ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (i : Fin 4) (input parameter spine : OTerm alpha),
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i)) input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing spine (numeral (bottomFlag i)) (numeral 0))) →
 Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure spine input))

/-- Actual original observer value; source and literal tag only. -/
def ActualBottom : Prop :=
 ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (i : Fin 4) (input parameter : OTerm alpha),
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i)) input)) →
 Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest (numeral (bottomFlag i)) input))

/-- Nonvariable OTHER tags; the original normalized variable test is discharged
from the literal tag, not supplied by the caller. -/
def ActualNonvariableMark : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (i : Fin 3) (input : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (i.val + 3)) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark (numeral 0) input))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverTargets
