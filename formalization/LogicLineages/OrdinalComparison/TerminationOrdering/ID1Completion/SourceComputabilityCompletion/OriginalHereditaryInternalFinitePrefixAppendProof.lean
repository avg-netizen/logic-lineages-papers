module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationValidityStackAppendListProof
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal one-child append gives an actual cons over the entire deletion row. -/
theorem unaryAppended (front first suffix out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front first z)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix))) :
 Nonempty (Derivation body Delta (consGraph out first suffix)) :=
 consForward front first z suffix suffix out hc (appendZeroValue suffix) ha

/-- For two children the intermediate cons is an ordinary queried graph,
not a suffix lookup or correctness assumption. -/
theorem binaryAppended (front first tail second suffix result out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front first tail)))
 (ht : Nonempty (Derivation body Delta (consGraph tail second z)))
 (hr : Nonempty (Derivation body Delta (consGraph result second suffix)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix))) :
 Nonempty (Derivation body Delta (consGraph out first result)) := by
 have htail := consBackward tail second z suffix suffix result ht (appendZeroValue suffix) hr
 exact consForward front first tail suffix result out hc htail ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
