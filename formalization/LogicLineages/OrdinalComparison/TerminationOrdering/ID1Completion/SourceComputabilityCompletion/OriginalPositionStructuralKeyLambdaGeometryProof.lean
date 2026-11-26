module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRebuildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryWithConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalContextInsertionSyntaxProof (insertRename)
open InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSupportProof (refl)

theorem erasedConstructor (s sE child childE d e arrow erasedType cutoff deleted gamma : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e child arrow)))
    (hs : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw sE erasedType cutoff s)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childE erasedType (suc cutoff) child)))
    (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma))) :
    Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor sE d e childE)) := by
  apply OriginalLambdaErasureCasePayloadProof.packedFromFields s d e child arrow _ hf
  intro beta j Theta raw hj hp
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  have hs' := renameInto hs j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [graph3Rename,sucRelabel] at hs' hc'
  rw [insertRename] at hi'
  simp only [graph3Rename]
  apply OriginalLambdaErasureCaseSupportProof.namedSquare
    (s.relabel j) (sE.relabel j) (d.relabel j) (e.relabel j) raw (child.relabel j)
    (erasedType.relabel j) (cutoff.relabel j) (deleted.relabel j) (gamma.relabel j) _ hp
    (andRight (andRight (andRight (andRight hf')))) hs' hi'
  intro beta2 k Omega actualChild childGamma childExtended hk hresult
  simp only [graph3Rename]
  have hc'' := renameInto hc' k Omega hk
  simp only [graph3Rename,sucRelabel] at hc''
  have square := andLeft hresult
  have eqchild := valueUnique OriginalRawSyntaxTransport.erasePackedRaw actualChild ((childE.relabel j).relabel k)
    (Fin.cons ((erasedType.relabel j).relabel k)
      (Fin.cons (suc ((cutoff.relabel j).relabel k)) (Fin.cons ((child.relabel j).relabel k) Fin.elim0)))
    (andLeft (andRight square)) hc''
  apply graphInputTransport body beta2 3 Omega
    (OrdinaryArithmetic.graphFormula OriginalLambdaConstructor.constructor) ((sE.relabel j).relabel k)
    (Fin.cons ((d.relabel j).relabel k) (Fin.cons ((e.relabel j).relabel k) (Fin.cons actualChild Fin.elim0)))
    (Fin.cons ((d.relabel j).relabel k) (Fin.cons ((e.relabel j).relabel k) (Fin.cons ((childE.relabel j).relabel k) Fin.elim0))) _
    (andLeft square)
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q))) i
  · rw [onEquality]; exact ⟨refl _⟩
  · rw [onEquality]; exact ⟨refl _⟩
  · rw [onEquality]; exact eqchild

/-- The erased actual body is reused with the literal deleted contexts.
Insert is supplied by checked deletion geometry, not by a covariance oracle. -/
theorem erasedFields (s sE child childE d e parameter childParameter
    erasedType cutoff c deleted gamma deletedParam childDeleted deletedChildParam : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalLambdaTraversalInternal.LambdaFields s d e child parameter childParameter)))
    (hconstructor : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor s d e child)))
    (hs : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw sE erasedType cutoff s)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childE erasedType (suc cutoff) child)))
    (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing deletedParam c deleted)))
    (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted d deleted)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing deletedChildParam c childDeleted))) :
    Nonempty (Derivation body Delta
      (OriginalLambdaTraversalInternal.LambdaFields sE d e childE deletedParam deletedChildParam ⊓
        graph3 OriginalLambdaConstructor.constructor sE d e childE)) := by
  apply programCases OriginalLambdaConstructor.arrow (Fin.cons d (Fin.cons e Fin.elim0)) _
  intro beta j Theta arrow hj ha
  simp only [conjunctionRename,lambdaFieldsRename,graph3Rename]
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  have hconstructor' := renameInto hconstructor j Theta hj
  have hs' := renameInto hs j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hp' := renameInto hp j Theta hj
  have hext' := renameInto hext j Theta hj
  have hcp' := renameInto hcp j Theta hj
  simp only [graph3Rename,sucRelabel] at hconstructor' hs' hc'
  rw [insertRename] at hi'
  rw [graph2Rename] at hp' hext' hcp'
  simp only [consTermRename,emptyRename] at ha
  have ht := OriginalLambdaTraversalLambdaSelectorProof.bodyType (s.relabel j) (e.relabel j) (child.relabel j)
    (andLeft (andRight (andRight hf'))) (andLeft (andRight (andRight (andRight hf'))))
  have fields := OriginalLambdaConstructorGraphFieldsProof.constructorFields (s.relabel j) (d.relabel j)
    (e.relabel j) (child.relabel j) arrow hconstructor' ht ha
  have constructorE := erasedConstructor (s.relabel j) (sE.relabel j) (child.relabel j) (childE.relabel j)
    (d.relabel j) (e.relabel j) arrow (erasedType.relabel j) (cutoff.relabel j)
    (deleted.relabel j) (gamma.relabel j) fields hs' hc' hi'
  have htE := OriginalPackedApplicationErasureProof.eraseTypeCopy (child.relabel j) (childE.relabel j)
    (e.relabel j) (erasedType.relabel j) (suc (cutoff.relabel j)) ht hc'
  have hparam := OriginalLambdaBodyObjectSupportProof.childParameterAtPairs (s.relabel j) (d.relabel j)
    (c.relabel j) (deleted.relabel j) (deletedParam.relabel j) (childDeleted.relabel j)
    (deletedChildParam.relabel j) (andLeft (andRight hf')) hp' hext' hcp'
  have rebuilt := OriginalLambdaTraversalLambdaRebuildProof.rebuiltFields (s.relabel j) (sE.relabel j)
    (d.relabel j) (e.relabel j) (childE.relabel j) arrow (deletedParam.relabel j)
    (deletedChildParam.relabel j) (andLeft (andRight hf')) hparam ha htE constructorE
  exact andIntro (andLeft rebuilt) constructorE

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
