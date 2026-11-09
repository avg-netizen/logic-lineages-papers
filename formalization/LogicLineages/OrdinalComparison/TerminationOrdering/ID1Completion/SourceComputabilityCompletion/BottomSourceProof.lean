module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceClosedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalOriginalUniformContextMembership (contextMember normalizedMember)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityCompletion.BottomRepresentative (bottomCode constant activeGraph windowAt)
open SourceComputabilityCompletion.BottomSource
open SourceComputabilityCompletion.BottomSourceShapeProof
open SourceComputabilityCompletion.BottomSourceClosedProof
open SourceComputabilityCompletion.BottomSourceValidityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem bottomCodeAtNumeral (tau : Ty) :
    Nonempty (Derivation body Gamma
      (graph1 bottomCode (bottomTerm tau) (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))) := by
  let typ : OTerm α := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  let payload : OTerm α := numeral (Nat.pair 3 (NumberedLeastCodeRepresentative.typeNumber tau))
  let xs : Fin 1 → OTerm α := ![typ]
  have hi := numeralPair (body := body) (α := α) (Delta := Gamma)
    3 (NumberedLeastCodeRepresentative.typeNumber tau)
  have ho := numeralPair (body := body) (α := α) (Delta := Gamma)
    (NumberedLeastCodeRepresentative.typeNumber tau)
    (Nat.pair 3 (NumberedLeastCodeRepresentative.typeNumber tau))
  have hp := binaryValue InternalPairing.pairing (constant 3) (.projection (0 : Fin 1))
    payload (numeral 3) typ xs hi (constantValue 3 xs) (projectionValue 0 xs)
  exact binaryValue InternalPairing.pairing (.projection (0 : Fin 1))
    (pairOf (constant 3) (.projection 0)) (bottomTerm tau) typ payload xs ho (projectionValue 0 xs) hp

theorem runtimeTypedBottom (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1)
    (hc : Calibrated n arity data)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (tau : Ty) (ht : tau ∈ S)
    (parameter gamma : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gamma))) :
    Nonempty (Derivation body Gamma (typedBottom data window tau parameter)) := by
  let selected := selection data window
  let beforeShape := BottomParameter.baseData data
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let contextTerm : OTerm α := numeral context
  let contextOnly : OTerm α := numeral (Nat.pair context 0)
  let typ : OTerm α := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  let input : OTerm α := bottomTerm tau
  let xs : Fin 2 → OTerm α := ![input,parameter]
  have hvalues := closedLeafValues n arity data hc symbols S table tau ht
  dsimp only at hvalues
  have hcode := bottomCodeAtNumeral (body := body) (α := α) (Gamma := Gamma) tau
  have hb := bottomAccept input typ hcode
  have hp0 := numeralPair (body := body) (α := α) (Delta := Gamma) context 0
  have hs0 := numeralGraph2 (body := body) (α := α) (Delta := Gamma) data.oldSource
    (bottomNumber tau) (Nat.pair context 0) 1 hvalues.1
  have ht0 := numeralGraph2 (body := body) (α := α) (Delta := Gamma) data.oldTarget
    (bottomNumber tau) (Nat.pair context 0) 1 hvalues.2.1
  have hs := BottomParameterInternalProof.normalizedValue data.oldSource (suc z) input
    parameter contextTerm gamma contextOnly hp hp0 hb hs0
  have hg := BottomParameterInternalProof.normalizedValue data.oldTarget (suc z) input
    parameter contextTerm gamma contextOnly hp hp0 hb ht0
  have hv := sourceBottom selected input typ parameter hcode hs hg
  have hm0 := numeralGraph2 (body := body) (α := α) (Delta := Gamma) (contextMember data.member)
    (NumberedLeastCodeRepresentative.typeNumber tau) context 1 hvalues.2.2
  have hm := InternalOriginalUniformContextMembershipInternalProof.sliceAccept data.member
    (suc z) typ parameter contextTerm gamma hp hm0
  have hw0 := numeralGraph1 (body := body) (α := α) (Delta := Gamma) window context 1
    (closedWindowValue n window hw symbols S table hS)
  have hleft := unaryValue InternalUnpair.left (.projection (1 : Fin 2)) contextTerm parameter xs
    (pairLeft parameter contextTerm gamma hp) (projectionValue 1 xs)
  have hwindow := unaryValue window (leftOf (.projection (1 : Fin 2))) (suc z) contextTerm xs hw0 hleft
  have ha : Nonempty (Derivation body Gamma (activeGraph beforeShape window input parameter)) :=
    InternalAcceptanceConjunctionProof.conjunctionAccept (windowAt window)
      (BottomDescent.selectedValidity beforeShape window) xs hwindow hv
  have hfixed := bottomStepFixed beforeShape window input typ parameter ha hcode
  have hl := bottomCodeLeft input typ hcode
  exact InternalOriginalUniformDescentSelectionInternalProof.typedAccept
    selected.oldRepresentative (InternalOriginalUniformDescentSelection.validity selected) selected.member
    input typ parameter (andIntro hm (andIntro hv (andIntro hl hfixed)))

theorem actualOriginalUniformBottomTyping : BottomSourceTargets.ActualOriginalUniformBottomTyping := by
  intro n arity data window hc hw symbols S table hS tau ht body α Delta parameter gamma
  let P := graph2 InternalPairing.pairing parameter
    (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gamma
  obtain ⟨d⟩ := runtimeTypedBottom (body := body) (Gamma := P :: Delta)
    n arity data window hc hw symbols S table hS tau ht parameter gamma
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceProof
