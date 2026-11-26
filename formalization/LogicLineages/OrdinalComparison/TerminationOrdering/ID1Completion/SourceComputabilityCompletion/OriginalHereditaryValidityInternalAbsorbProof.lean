module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof OriginalHereditaryValidityInternalStateSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open OriginalHereditaryValidityInternalRejectSupportProof

open InternalAdditionLawsProof InternalMultiplicationLawsProof

theorem notLessZero (x : OTerm α) :
    Nonempty (Derivation body Gamma (InternalOriginalOrderSyntaxProof.ltF x z).not) := by
  have h : Nonempty (Derivation body
      (InternalOriginalOrderSyntaxProof.ltF x z :: Gamma) (⊥ : Formula α)) := by
    apply InternalOriginalOrderProof.orderCases _ x z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta gap _ ⟨he⟩
    simp only [zRelabel] at he
    exact ⟨sucNeZeroApply (trans (symm (addSucc (x.relabel j) gap)) he)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem pairZero :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing (z : OTerm α) z z)) := by
  have hp := InternalPairingSupportProof.pairingOfNotLess (body := body) (Gamma := Gamma) z z (notLessZero z)
  apply outputTransport InternalPairing.pairing (add (add (mul z z) z) z) z
    (Fin.cons z (Fin.cons z Fin.elim0)) _ hp
  exact ⟨trans (addZero (add (mul z z) z)) (trans (addZero (mul z z)) (mulZero z))⟩

theorem failureFixed (s t m : Program 2) :
    Nonempty (Derivation body Gamma (graph1 (transition s t m) (z : OTerm α) z)) := by
  let xs : Fin 1 → OTerm α := Fin.cons z Fin.elim0
  have hs : Nonempty (Derivation body Gamma (graph1 status (z : OTerm α) z)) :=
    pairLeft z z z pairZero
  have he := InternalEqualityTestCompositionProof.rejectForwardGap (body := body) (Gamma := Gamma)
    (z : OTerm α) (suc z) z ⟨leftZero (suc z)⟩
  apply zeroBranchIntro _ _ _ z xs
  · exact binaryValue InternalEqualityTest.equalityTest status (InternalLessThan.constantOne 1)
      z z (suc z) xs he hs (InternalLessThanSupportProof.oneConstantValue xs)
  · exact InternalLessThanSupportProof.zeroConstantValue xs

theorem emptyFixed (s t m : Program 2) (state : OTerm α)
    (h : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) z))) :
    Nonempty (Derivation body Gamma (graph1 (transition s t m) state state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  apply successorBranchIntro _ _ _ state z xs
    (exactAccept status xs (pairLeft state (numeral 1) z h))
  exact zeroBranchIntro work _ _ state xs (pairRight state (numeral 1) z h) (projectionValue 0 xs)

theorem actualOriginalHereditaryAbsorbingStates :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryAbsorbingStates := by
  intro body s t m α state out
  constructor
  · exact graphAtValue (transition s t m) out z (Fin.cons z Fin.elim0) (failureFixed s t m)
  · let H := StateGraph state (numeral 1) z
    have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := graphAtValue (transition s t m) out state (Fin.cons state Fin.elim0)
      (emptyFixed s t m state h)
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
