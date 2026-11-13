module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Local consumer of the SMALLER-context constructor induction conclusion.
The final constructor targets must generate hs by induction, not assume it.
Actual observation programs are opened at literal shared deletion metadata. -/
theorem atGeometry (R : Program 2)
 (left right erasedLeft erasedRight parameter deletedParameter c gamma deleted cutoff d a b : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing deletedParameter c deleted)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d cutoff left)))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d cutoff right)))
 (hs : Nonempty (Derivation body Delta (SameEvaluator R erasedLeft erasedRight deletedParameter)))
 (ha : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) a cutoff left parameter)))
 (hb : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) b cutoff right parameter))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn a b)) := by
 let E := OriginalHereditaryEvaluatorDefinitions.evaluator R
 have hva := EvaluatorErasureObservationProof.actualCell E left erasedLeft parameter deletedParameter
   c gamma deleted cutoff d a hp hn hl hd heL ha
 have hvb := EvaluatorErasureObservationProof.actualCell E right erasedRight parameter deletedParameter
   c gamma deleted cutoff d b hp hn hl hd heR hb
 have hsame := EvaluatorConstructorValueProof.evaluatorValue R erasedLeft erasedRight deletedParameter a hs hva
 exact valueUnique E a b (Fin.cons erasedRight (Fin.cons deletedParameter Fin.elim0)) hsame hvb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellProof
