module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Unchanged raw leaves require only a nonzero tag, including unknown tags
and malformed tag-six payloads. No source-domain or canonicality guard occurs. -/
theorem nonzeroLeafForward (mode : Mode) (out d k raw tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation body Delta (equal tag (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw))) :
    Nonempty (Derivation body Delta (UnchangedLeafResult mode out raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have htag := unaryValue InternalUnpair.left (.projection 2) tag raw xs ht (projectionValue 2 xs)
  have htest := sameReject (leftOf (.projection 2)) (constant 3 0) tag (numeral 0) xs
    htag (constantValue 0 xs) hn
  cases mode with
  | shift =>
    have h := zeroBranchElim _ _ _ out xs htest ho
    simpa only [UnchangedLeafResult,equalEqn] using
      valueUnique (.projection 2) out raw xs h (projectionValue 2 xs)
  | erase =>
    have h := zeroBranchElim _ _ _ out xs htest ho
    simpa only [UnchangedLeafResult,equalEqn] using
      valueUnique (.projection 2) out raw xs h (projectionValue 2 xs)
  | rank =>
    have h := zeroBranchElim _ _ _ out xs htest ho
    simpa only [UnchangedLeafResult,equalEqn] using
      valueUnique (constant 3 0) out (numeral 0) xs h (constantValue 0 xs)

theorem nonzeroLeafBackward (mode : Mode) (out d k raw tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation body Delta (equal tag (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation body Delta (graph3 (leaf mode) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  have htag := unaryValue InternalUnpair.left (.projection 2) tag raw xs ht (projectionValue 2 xs)
  have htest := sameReject (leftOf (.projection 2)) (constant 3 0) tag (numeral 0) xs
    htag (constantValue 0 xs) hn
  cases mode with
  | shift =>
    obtain ⟨he⟩ := ho
    apply zeroBranchIntro _ _ _ out xs htest
    exact outputTransport (.projection 2) raw out xs
      ⟨symm (by simpa only [UnchangedLeafResult,equalEqn] using he)⟩ (projectionValue 2 xs)
  | erase =>
    obtain ⟨he⟩ := ho
    apply zeroBranchIntro _ _ _ out xs htest
    exact outputTransport (.projection 2) raw out xs
      ⟨symm (by simpa only [UnchangedLeafResult,equalEqn] using he)⟩ (projectionValue 2 xs)
  | rank =>
    obtain ⟨he⟩ := ho
    apply zeroBranchIntro _ _ _ out xs htest
    exact outputTransport (constant 3 0) (numeral 0) out xs
      ⟨symm (by simpa only [UnchangedLeafResult,equalEqn] using he)⟩ (constantValue 0 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafProof
