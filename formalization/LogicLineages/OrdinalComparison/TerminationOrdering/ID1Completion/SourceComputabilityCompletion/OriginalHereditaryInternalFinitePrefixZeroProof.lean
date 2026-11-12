module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationValidityStackAppendListProof
open OriginalContextInsertion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroSuffix (suffix joined count index value : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined z suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index joined))) :
 Nonempty (Derivation body Delta (lengthGraph count suffix)) ∧
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index suffix)) := by
 have he := appendZeroRecover joined suffix ha
 exact ⟨headTransport length count joined suffix Fin.elim0 he hl,
   InternalCanonicalFixedWindowVertexDispatchInvariantProof.binaryInputsTransport
    InternalRawListRecursion.lookup value index joined index suffix ⟨refl index⟩ he hv⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
