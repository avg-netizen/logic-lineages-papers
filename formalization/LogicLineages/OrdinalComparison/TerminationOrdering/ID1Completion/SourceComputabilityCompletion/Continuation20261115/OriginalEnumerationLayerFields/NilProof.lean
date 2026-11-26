module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (symm refl)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consAt (xs : Fin 7 → OTerm alpha) (out value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.nils out xs)))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor value Fin.elim0))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value z)) := by
  have hval : Nonempty (Derivation body Delta
      (programGraph (.composition OriginalRawSyntaxTransport.nilConstructor Fin.elim0) value xs)) :=
    compositionValue OriginalRawSyntaxTransport.nilConstructor Fin.elim0 value xs Fin.elim0 hv (fun i => Fin.elim0 i)
  exact binaryRecover InternalListCodec.consCode
    (.composition OriginalRawSyntaxTransport.nilConstructor Fin.elim0) (InternalAcceptance.constantZero 7)
    out value z xs hg hval (InternalAcceptanceConjunctionProof.constantZeroValue xs)

theorem forward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.nils out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor code Fin.elim0)) := by
  apply programCases OriginalRawSyntaxTransport.nilConstructor Fin.elim0 _
  intro beta j Theta value hj hv
  simp only [emptyRename] at hv
  simp only [programRename,emptyRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hc := consAt (fun i => (xs i).relabel j) (out.relabel j) value hgj hv
  obtain ⟨he⟩ := OriginalAscendingRange.SupportProof.singletonMember (out.relabel j) value (code.relabel j) hc hmj
  exact outputTransport OriginalRawSyntaxTransport.nilConstructor value (code.relabel j) Fin.elim0 ⟨symm he⟩ hv

theorem backward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.nils out xs)))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor code Fin.elim0))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply containsHit out code z code (consAt xs out code hg hv)
  rw [equalEqn]
  exact ⟨refl code⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NilProof
