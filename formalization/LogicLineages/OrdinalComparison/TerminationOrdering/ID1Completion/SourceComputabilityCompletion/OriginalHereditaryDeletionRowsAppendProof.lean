module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalGraphCompositionFunctionalityProof InternalListCodecSupportProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Actual append over a cons preserves its first cell. Tail append is the
ordinary queried recursion witness, not a supplied observer conclusion. -/
theorem appendHead (front head tail suffix result out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
    (ht : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append result tail suffix)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out front suffix))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup head z out)) := by
  have hcons := InternalApplicationValidityStackAppendListProof.consForward
    front head tail suffix result out hc ht ha
  exact OriginalAllPositionContextDeleteBaseProof.lookupZero out head result hcons

/-- The actual successor lookup reduces to the appended tail. This is the
local constructor step for a bounded prefix/suffix lookup induction. -/
theorem appendLookupSuccessor (front head tail suffix result out cutoff value : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
    (ht : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append result tail suffix)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out front suffix))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup value (suc cutoff) out).iff
        (graph2 InternalRawListRecursion.lookup value cutoff result))) := by
  exact OriginalAllPositionContextDeleteDropProof.lookupConsIff out head result cutoff value
    (InternalApplicationValidityStackAppendListProof.consForward front head tail suffix result out hc ht ha)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsAppendProof
