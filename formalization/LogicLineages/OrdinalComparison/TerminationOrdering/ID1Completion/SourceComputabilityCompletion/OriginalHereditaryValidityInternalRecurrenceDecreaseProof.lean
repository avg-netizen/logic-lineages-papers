module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseDispatchProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem acceptedDecrease (s t m : Program 2)
    (state work frame raw parameter rest previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous work)))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  let qs : Fin 3 → Program 2 := ![rightOf (.projection 0),
    .composition workFuel (fun _ : Fin 1 => .projection 1),
    .composition OriginalLambdaConstructor.tag (fun _ : Fin 1 => .projection 0)]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons rest Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [decreasedRename]
  simp only [xs,consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Theta hj
  rw [stateFrameRename] at hs'
  have hn' := renameInto hn j Theta hj
  simp only [graph1Rename,oneRename] at hn'
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  have ho' := renameInto ho j Theta hj
  rw [graph1Rename] at ho'
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (rest.relabel j) Fin.elim0)
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have ht := unaryRecover workFuel (.projection 1) (ys 1) (rest.relabel j) xx
    (hq 1) (projectionValue 1 xx)
  have htag := unaryRecover OriginalLambdaConstructor.tag (.projection 0) (ys 2) (raw.relabel j) xx
    (hq 2) (projectionValue 0 xx)
  have he := consRecover (work.relabel j) (frame.relabel j) (rest.relabel j)
    (suc (ys 0)) (ys 1) (previous.relabel j) (andLeft (andRight hs'))
    (frameValue (frame.relabel j) (raw.relabel j) (parameter.relabel j) (ys 0)
      (andRight (andRight hs')) hp) ht hf'
  exact acceptingTagDecrease s t m (state.relabel j) (work.relabel j) (frame.relabel j)
    (raw.relabel j) (parameter.relabel j) (rest.relabel j) (ys 2) (ys 0) (ys 1)
    (previous.relabel j) (out.relabel j) hs' hn' htag hp ht he ho'

/-- Full-output classification of an arbitrary actual nonempty framed visit.
The accepted branch constructs all measure witnesses; the rejected branch
uses original failure absorption, not any leaf Boolean assumption. -/
 theorem decreaseCore (s t m : Program 2)
    (state work frame raw parameter rest previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous work)))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply formulaCases (graph1 (nodeCheck s t m) (numeral 1) state)
  · exact acceptedDecrease s t m state work frame raw parameter rest previous out
      (withHyp hs _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _) (withHyp ho _)
  · let N := (graph1 (nodeCheck s t m) (numeral 1) state).not
    have hl : Nonempty (Derivation body (N :: Delta) (LiveWork state)) :=
      OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof.stateFrameLive
        state work frame raw parameter rest (withHyp hs N)
    have hz := OriginalHereditaryValidityInternalRejectSupportProof.rejectNode s t m state hl
      (show Nonempty (Derivation body
        ((graph1 (nodeCheck s t m) (numeral 1) state).not :: Delta)
        (graph1 (nodeCheck s t m) (numeral 1) state).not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have he := valueUnique (transition s t m) out z (Fin.cons state Fin.elim0) (withHyp ho N) hz
    apply failedIntro out previous
    simpa only [equalEqn] using he

 theorem actualOriginalHereditaryInternalWorkDecrease :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalWorkDecrease := by
  intro body s t m alpha state work frame raw parameter rest previous out
  let A := StateFrame state work frame raw parameter rest ⊓ WorkFuelGraph previous work
  let G := graph1 (transition s t m) out state
  have h : Nonempty (Derivation body [G,A] A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨d⟩ := decreaseCore s t m state work frame raw parameter rest previous out
    (andLeft h) (andRight h) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseProof
