module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseArithmeticProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseApplicationProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseLambdaProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem nonapplicationDecrease (s t m : Program 2)
    (state work frame raw parameter rest tag payload tail previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail))))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply formulaCases (equal tag (numeral 1))
  · have htag1 : Nonempty (Derivation body (equal tag (numeral 1) :: Delta)
        (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)) := by
      apply outputTransport OriginalLambdaConstructor.tag tag (numeral 1) (Fin.cons raw Fin.elim0)
        ?_ (withHyp htag _)
      simpa only [equalEqn] using
        (show Nonempty (Derivation body (equal tag (numeral 1) :: Delta) (equal tag (numeral 1))) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact lambdaResultDecrease state out raw parameter rest payload tail previous
      (frameRaw state work frame raw parameter rest (withHyp hs _)) htag1
      (withHyp hp _) (withHyp ht _) (withHyp he _)
      (OriginalHereditaryValidityInternalLambdaProof.lambdaForward s t m state work frame raw parameter rest out
        (withHyp hs _) (withHyp hn _) htag1 (withHyp ho _))
  · have hpop := OriginalHereditaryValidityInternalPopProof.popForward s t m state work frame raw parameter rest tag out
      (withHyp hs _) (withHyp hn _) (withHyp htag _) (withHyp h2 _)
      (show Nonempty (Derivation body ((equal tag (numeral 1)).not :: Delta) (equal tag (numeral 1)).not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp ho _)
    exact decreasedIntro out previous rest tail hpop (withHyp ht _)
      (tailLess payload tail previous (withHyp he _))

 theorem acceptingTagDecrease (s t m : Program 2)
    (state work frame raw parameter rest tag payload tail previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail))))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply formulaCases (equal tag (numeral 2))
  · have htag2 : Nonempty (Derivation body (equal tag (numeral 2) :: Delta)
        (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)) := by
      apply outputTransport OriginalLambdaConstructor.tag tag (numeral 2) (Fin.cons raw Fin.elim0)
        ?_ (withHyp htag _)
      simpa only [equalEqn] using
        (show Nonempty (Derivation body (equal tag (numeral 2) :: Delta) (equal tag (numeral 2))) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact applicationResultDecrease state out raw parameter rest payload tail previous
      (frameRaw state work frame raw parameter rest (withHyp hs _)) htag2
      (withHyp hp _) (withHyp ht _) (withHyp he _)
      (OriginalHereditaryValidityInternalApplicationProof.applicationForward s t m state work frame raw parameter rest out
        (withHyp hs _) (withHyp hn _) htag2 (withHyp ho _))
  · exact nonapplicationDecrease s t m state work frame raw parameter rest tag payload tail previous out
      (withHyp hs _) (withHyp hn _) (withHyp htag _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hp _) (withHyp ht _) (withHyp he _) (withHyp ho _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseDispatchProof
