module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendApplicationProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendLambdaProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPopProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem nonapplicationCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix tag : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hjn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) joinedState)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not)) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply formulaCases (equal tag (numeral 1))
  · have htag1 : Nonempty (Derivation body (equal tag (numeral 1) :: Delta)
        (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)) := by
      apply outputTransport OriginalLambdaConstructor.tag tag (numeral 1) (Fin.cons raw Fin.elim0)
        ?_ (withHyp htag _)
      simpa only [equalEqn] using
        (show Nonempty (Derivation body (equal tag (numeral 1) :: Delta) (equal tag (numeral 1))) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact lambdaCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix
      (withHyp hs _) (withHyp hjs _) (withHyp ha _) (withHyp hn _) (withHyp hjn _) htag1
  · exact popCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix tag
      (withHyp hs _) (withHyp hjs _) (withHyp ha _) (withHyp hn _) (withHyp hjn _) (withHyp htag _)
      (withHyp h2 _) ⟨Derivation.hypothesis List.mem_cons_self⟩

 theorem tagCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix tag : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hjn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) joinedState)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply formulaCases (equal tag (numeral 2))
  · have htag2 : Nonempty (Derivation body (equal tag (numeral 2) :: Delta)
        (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)) := by
      apply outputTransport OriginalLambdaConstructor.tag tag (numeral 2) (Fin.cons raw Fin.elim0)
        ?_ (withHyp htag _)
      simpa only [equalEqn] using
        (show Nonempty (Derivation body (equal tag (numeral 2) :: Delta) (equal tag (numeral 2))) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact applicationCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix
      (withHyp hs _) (withHyp hjs _) (withHyp ha _) (withHyp hn _) (withHyp hjn _) htag2
  · exact nonapplicationCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix tag
      (withHyp hs _) (withHyp hjs _) (withHyp ha _) (withHyp hn _) (withHyp hjn _) (withHyp htag _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendDispatchProof
