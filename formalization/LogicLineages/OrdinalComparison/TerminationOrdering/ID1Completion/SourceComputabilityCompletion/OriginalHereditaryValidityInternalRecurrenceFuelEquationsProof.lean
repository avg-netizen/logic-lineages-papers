module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelEquationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof InternalAdditionLawsProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)

 theorem actualOriginalHereditaryInternalWorkFuelEquations :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalWorkFuelEquations := by
  constructor
  · intro body alpha out
    exact graphIffValue out z z nilValue
  · intro body alpha code frame raw parameter rest payload tail out
    let A := WorkCons code frame rest ⊓
      (FrameGraph frame raw parameter ⊓
        (graph1 InternalUnpair.right payload raw ⊓ WorkFuelGraph tail rest))
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := consValue code frame rest (suc payload) tail (andLeft h)
      (frameValue frame raw parameter payload (andLeft (andRight h))
        (andLeft (andRight (andRight h)))) (andRight (andRight (andRight h)))
    obtain ⟨d⟩ := graphIffValue out (add (suc payload) tail) code hv
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelEquationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelEquationsProof
