module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreasePushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceWeightLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalPairingSumBounds
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalResultLambdaSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceDecreasePushProof
open OriginalHereditaryValidityInternalRecurrenceWeightLambdaProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem lambdaResultDecrease (state out raw parameter rest payload tail previous : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 currentRaw raw state)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail))))
    (hres : Nonempty (Derivation body Delta (LambdaResult state out raw parameter rest))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply lambdaResultCases state out raw parameter rest _ hres
  intro beta j Theta child childParameterCode hj fields
  rw [decreasedRename]
  have hr' := renameInto hr j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hr' hp'
  have htag' := renameInto htag j Theta hj
  simp only [graph1Rename,oneRename] at htag'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hpush := andRight (andRight (andRight fields))
  apply lambdaPayloadCases (state.relabel j) (raw.relabel j) child (payload.relabel j) _
    hr' (andLeft fields) hp' htag'
  intro gamma k Xi bp hk hbp hbound
  rw [decreasedRename]
  have hpush' := renameInto hpush k Xi hk
  rw [pushedFrameRename] at hpush'
  have ht'' := renameInto ht' k Xi hk
  rw [fuelRename] at ht''
  have he'' := renameInto he' k Xi hk
  simp only [eqnRelabel,addRelabel,sucRelabel] at he''
  exact pushedLambdaDecrease ((out.relabel j).relabel k) (child.relabel k) (childParameterCode.relabel k)
    ((rest.relabel j).relabel k) ((payload.relabel j).relabel k)
    ((tail.relabel j).relabel k) ((previous.relabel j).relabel k) bp hpush' hbp ht'' hbound he''

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseLambdaProof
