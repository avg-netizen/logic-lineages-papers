module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual two-sided root construction at queried original application codecs.
The common retained/evaluator child values determine one common root value.
No parent evaluator relation or row equality is a hypothesis. -/
theorem commonAtCoordinates (Q : Program 2)
 (left right parameter typ domain fnType rawL rawR payloadL payloadR childrenL childrenR
  fnRawL fnRawR argRawL argRawR fnL fnR argL argR fnValue argValue
  fnObserved argObserved observations typedData data out : OTerm alpha)
 (hType : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)))
 (hPackedL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left typ rawL)))
 (hRawL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawL (numeral 2) payloadL)))
 (hPayloadL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payloadL domain childrenL)))
 (hChildrenL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childrenL fnRawL argRawL)))
 (hFnL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnL fnType fnRawL)))
 (hArgL : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argL domain argRawL)))
 (hFnValueL : Nonempty (Derivation body Delta (graph2 Q fnValue fnL parameter)))
 (hArgValueL : Nonempty (Derivation body Delta (graph2 Q argValue argL parameter)))
 (hPackedR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing right typ rawR)))
 (hRawR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawR (numeral 2) payloadR)))
 (hPayloadR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payloadR domain childrenR)))
 (hChildrenR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childrenR fnRawR argRawR)))
 (hFnR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnR fnType fnRawR)))
 (hArgR : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argR domain argRawR)))
 (hFnValueR : Nonempty (Derivation body Delta (graph2 Q fnValue fnR parameter)))
 (hArgValueR : Nonempty (Derivation body Delta (graph2 Q argValue argR parameter)))
 (hFO : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnObserved fnType fnValue)))
 (hAO : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argObserved domain argValue)))
 (hObs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fnObserved argObserved)))
 (hTD : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ observations)))
 (hData : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (hOut : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 2) data)))
 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out left parameter)) ∧
   Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out right parameter)) := by
 constructor
 · exact OriginalRootObservationInternalProof.applicationLaw Q body alpha Delta
     left parameter typ rawL domain childrenL payloadL fnRawL argRawL fnType fnL argL
     fnValue argValue fnObserved argObserved observations typedData data out
     hPackedL hRawL hPayloadL hChildrenL hType hFnL hArgL hFnValueL hArgValueL
     hFO hAO hObs hTD hData hOut
 · exact OriginalRootObservationInternalProof.applicationLaw Q body alpha Delta
     right parameter typ rawR domain childrenR payloadR fnRawR argRawR fnType fnR argR
     fnValue argValue fnObserved argObserved observations typedData data out
     hPackedR hRawR hPayloadR hChildrenR hType hFnR hArgR hFnValueR hArgValueR
     hFO hAO hObs hTD hData hOut
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootProof
