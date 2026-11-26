module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalSourceSyntaxProof
open OriginalLambdaTraversalLambdaSourceProof OriginalLambdaTraversalLambdaSelectorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryInputs (p : Program 2) (out x y x' y' : OTerm alpha)
    (hx : Nonempty (Derivation body Delta (eqn x x')))
    (hy : Nonempty (Derivation body Delta (eqn y y')))
    (hp : Nonempty (Derivation body Delta (graph2 p out x y))) :
    Nonempty (Derivation body Delta (graph2 p out x' y')) := by
  apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons x' (Fin.cons y' Fin.elim0)) _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact hx
  · rw [onEquality]; exact hy

/-- Bind all original root witnesses to the supplied ACTUAL selectors.
Both memberships and the full arrow graph are retained at the same parameter. -/
theorem sourceFieldsAt (data : Data) (raw parameter typ d e : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ raw)))
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawDomain d raw)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawCodomain e raw)))
    (hf : Nonempty (Derivation body Delta (SourceLambdaRootFactors data raw parameter))) :
    Nonempty (Derivation body Delta (sourceFields data raw parameter typ d e)) := by
  apply sourceCases data raw parameter _ hf
  intro beta j Theta actualType actualDomain actualCodomain hj hfields
  simp only [sourceFields,conjunctionRename,graph1Rename,graph2Rename,oneRename]
  have ht' := renameInto ht j Theta hj
  have hd' := renameInto hd j Theta hj
  have he' := renameInto he j Theta hj
  rw [graph1Rename] at ht' hd' he'
  let xx : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hactualType := andLeft hfields
  have hactualDomain := andLeft (andRight hfields)
  have hactualTail := andLeft (andRight (andRight hfields))
  have hactualArrow := andLeft (andRight (andRight (andRight hfields)))
  have hactualMembers := andRight (andRight (andRight (andRight hfields)))
  have hactualCodomain := unaryValue InternalListCodec.tailCode OriginalLambdaTraversal.rawType
    actualCodomain actualType xx hactualTail hactualType
  have et := valueUnique InternalUnpair.left actualType (typ.relabel j) xx hactualType ht'
  have ed := valueUnique OriginalLambdaTraversal.rawDomain actualDomain (d.relabel j) xx hactualDomain hd'
  have ee := valueUnique OriginalLambdaTraversal.rawCodomain actualCodomain (e.relabel j) xx hactualCodomain he'
  have ha := outputTransport OriginalLambdaConstructor.arrow actualType (typ.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) Fin.elim0)) et
    (binaryInputs OriginalLambdaConstructor.arrow actualType actualDomain actualCodomain
      (d.relabel j) (e.relabel j) ed ee hactualArrow)
  have hmType := headTransport data.member (numeral 1) actualType (typ.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0) et (andLeft hactualMembers)
  have hmDomain := headTransport data.member (numeral 1) actualDomain (d.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0) ed (andRight hactualMembers)
  exact andIntro ht' (andIntro hd'
    (andIntro (unaryRecover InternalListCodec.tailCode OriginalLambdaTraversal.rawType
      (e.relabel j) (typ.relabel j) xx he' ht')
      (andIntro ha (andIntro hmType hmDomain))))

/-- Source acceptance and the actual traversal fields reconstruct the parent
through the original lambda constructor, with its actual outer arrow type. -/
theorem sourceConstructor (rawData : Data) (window : Program 1)
    (raw d e child typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ raw)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) raw parameter))) :
    Nonempty (Derivation body Delta
      (graph2 OriginalLambdaConstructor.arrow typ d e ⊓
        graph3 OriginalLambdaConstructor.constructor raw d e child)) := by
  have hroot := andLeft (sourceAccepted (leafData rawData window)
    (OriginalLambdaTraversalSelectionValidityProof.leafSourceLambda rawData window)
    raw parameter (andLeft hf) hs)
  have hd := andLeft (andRight hf)
  have he := andLeft (andRight (andRight hf))
  have hb := andLeft (andRight (andRight (andRight hf)))
  have hr := sourceFieldsAt (leafData rawData window) raw parameter typ d e ht hd he hroot
  have ha := andLeft (andRight (andRight (andRight hr)))
  have fields : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields raw d e child typ)) :=
    andIntro (andLeft hf) (andIntro ht (andIntro ha (andIntro hd (bodyCodeAt raw e child he hb))))
  exact andIntro ha (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction
    raw d e child typ fields)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
