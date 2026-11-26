module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open TransparentHeadBranches.Proof (identityImp andImp orImp applyImp)
theorem ordinary : Targets.InternalOrdinary := by
  intro n arity body alpha Delta source target f g base dest node child param symbols types hs ht hn hp hw
  have old := OriginalDecodedOrdinaryRecurrence.Proof.ordinaryRecurrence n arity body alpha Delta
    source target f g base dest node child param symbols types hs ht hn hp hw
  constructor
  · intro he
    have hr := old.mp he
    have hg := andLeft hr
    have hi := SupportProof.equalityImp n false source target z z f g z z base dest z z z z node z param hs ht hn hg
    have lift := orImp
      (identityImp (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types] ⊓
        graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) g f))
      (andImp (andLeft hi) (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param)))
    exact andIntro hg (applyImp lift (andRight hr))
  · intro hr
    have hg := andLeft hr
    have hi := SupportProof.equalityImp n false source target z z f g z z base dest z z z z node z param hs ht hn hg
    have lift := orImp
      (identityImp (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types] ⊓
        graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) g f))
      (andImp (andRight hi) (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param)))
    exact old.mpr (andIntro hg (applyImp lift (andRight hr)))

theorem numbered : Targets.InternalNumbered := by
  intro n arity body alpha Delta source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types hs ht hn hp0 hp3 hw
  have old := OriginalDecodedNumberedRecurrence.Proof.numberedRecurrence n arity body alpha Delta
    source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types hs ht hn hp0 hp3 hw
  constructor
  · intro he
    have hr := old.mp he
    have hg := andLeft hr
    have hi := SupportProof.equalityImp n true source target k l f g tau upsilon base dest ts us extras otherExtras node z param hs ht hn hg
    have lift := andImp (identityImp (eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)))
      (orImp
        (orImp (identityImp (eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]))
          (andImp (andImp (andLeft hi) (identityImp (eqn extras otherExtras)))
            (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param))))
        (andImp (andImp (andLeft hi) (identityImp (eqn base dest)))
          (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param))))
    exact andIntro hg (applyImp lift (andRight hr))
  · intro hr
    have hg := andLeft hr
    have hi := SupportProof.equalityImp n true source target k l f g tau upsilon base dest ts us extras otherExtras node z param hs ht hn hg
    have lift := andImp (identityImp (eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)))
      (orImp
        (orImp (identityImp (eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]))
          (andImp (andImp (andRight hi) (identityImp (eqn extras otherExtras)))
            (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param))))
        (andImp (andImp (andRight hi) (identityImp (eqn base dest)))
          (identityImp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param))))
    exact old.mpr (andIntro hg (applyImp lift (andRight hr)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Proof
