module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackReturnSupportProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendFrameQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Proof-only uniform handling of the unchanged component and the appended
component. The enabled AST is literally the frozen original append program. -/
def extend (enabled : Bool) : Program 2 :=
  if enabled then InternalApplicationValidityStackAppend.append else .projection 0

theorem identityExtend (value background : OTerm α) :
    Nonempty (Derivation body Gamma (graph2 (extend false) value value background)) :=
  projectionValue 0 (Fin.cons value (Fin.cons background Fin.elim0))

theorem identityExtendRecover (out value background : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 (extend false) out value background))) :
    Nonempty (Derivation body Gamma (eqn out value)) :=
  valueUnique (extend false) out value (Fin.cons value (Fin.cons background Fin.elim0))
    h (identityExtend value background)

theorem extendConsBackward (mode : Bool) (front head tail background tailOut out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode front head tail)))
    (ht : Nonempty (Derivation body Gamma (graph2 (extend mode) tailOut tail background)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head tailOut))) :
    Nonempty (Derivation body Gamma (graph2 (extend mode) out front background)) := by
  cases mode with
  | true => exact consBackward front head tail background tailOut out hc ht ho
  | false =>
    have he := identityExtendRecover tailOut tail background ht
    have hc' := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalListCodec.consCode out head tailOut tail he ho
    have hf := valueUnique InternalListCodec.consCode front out
      (Fin.cons head (Fin.cons tail Fin.elim0)) hc hc'
    exact outputTransport (extend false) front out
      (Fin.cons front (Fin.cons background Fin.elim0)) hf (identityExtend front background)

theorem extendConsForward (mode : Bool) (front head tail background tailOut out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode front head tail)))
    (ht : Nonempty (Derivation body Gamma (graph2 (extend mode) tailOut tail background)))
    (ho : Nonempty (Derivation body Gamma (graph2 (extend mode) out front background))) :
    Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head tailOut)) := by
  cases mode with
  | true => exact consForward front head tail background tailOut out hc ht ho
  | false =>
    obtain ⟨he⟩ := identityExtendRecover tailOut tail background ht
    obtain ⟨hf⟩ := identityExtendRecover out front background ho
    have hc' := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalListCodec.consCode front head tail tailOut ⟨symm he⟩ hc
    exact outputTransport InternalListCodec.consCode front out
      (Fin.cons head (Fin.cons tailOut Fin.elim0)) ⟨symm hf⟩ hc'

/-- Actual current selectors from a live state's original raw cons graph. -/
theorem currentFields (state stack results frame tail tag value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value))) :
    Nonempty (Derivation body Gamma
      (graph1 currentFrame frame state ⊓ (graph1 rest tail state ⊓
        (graph1 frameTag tag state ⊓ graph1 currentValue value state)))) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hw := andLeft (liveStateFields state stack results hs)
  have hd := InternalListCodecSupportProof.consDestruction stack frame tail hc
  have hf := unaryValue InternalListCodec.headCode work frame stack xs (andLeft hd) hw
  exact andIntro hf (andIntro
    (unaryValue InternalListCodec.tailCode work tail stack xs (andLeft (andRight hd)) hw)
    (andIntro (unaryValue InternalUnpair.left currentFrame tag frame xs (pairLeft frame tag value hp) hf)
      (unaryValue InternalUnpair.right currentFrame value frame xs (pairRight frame tag value hp) hf)))

/-- Common status/work envelope. The actual nonempty transition branches
remain literal sub-ASTs of the unchanged machine. -/
theorem liveInner (guard leaf : Program 1) (combine : Program 4)
    (state stack results frame tail out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hi : Nonempty (Derivation body Gamma (graph1
      (InternalAcceptance.branch
        (InternalApplicationStepPeel.same frameTag (InternalAcceptance.constantZero 1))
        (InternalAcceptance.branch (InternalApplicationValidityStack.exactOne frameTag)
          (InternalAcceptance.constantZero 1)
          (InternalAcceptance.branch InternalApplicationResultStack.results (InternalAcceptance.constantZero 1)
            (InternalAcceptance.branch (tailOf InternalApplicationResultStack.results)
              (InternalAcceptance.constantZero 1) (finishReturned combine))))
        (InternalAcceptance.branch
          (.composition (openGuard guard) (fun _ : Fin 1 => currentValue))
          (leafReturned leaf) expanded)) out state))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hd := InternalListCodecSupportProof.consDestruction stack frame tail hc
  apply successorBranchIntro _ _ _ out z xs
    (sameAccept status (InternalLessThan.constantOne 1) (suc z) xs
      (liveStatus state stack results hs) (InternalLessThanSupportProof.oneConstantValue xs))
  exact nonzeroBranchIntro _ _ _ out stack xs (andLeft (liveStateFields state stack results hs))
    (by simpa only [equalEqn] using andRight (andRight hd)) hi

/-- A malformed frame fails; no claim is made about any other state. -/
theorem malformedFailure (guard leaf : Program 1) (combine : Program 4)
    (state stack results frame tail tag value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) z state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have ht := andLeft (andRight (andRight (currentFields state stack results frame tail tag value hs hc hp)))
  apply liveInner guard leaf combine state stack results frame tail z hs hc
  apply zeroBranchIntro _ _ _ z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z xs hz ht (constantZeroValue xs))
  exact zeroBranchIntro _ _ _ z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      z tag (suc z) xs h1 ht (InternalLessThanSupportProof.oneConstantValue xs)) (constantZeroValue xs)

/-- Finish underflow with no result is an actual zero transition. -/
theorem emptyResultsFailure (guard leaf : Program 1) (combine : Program 4)
    (state stack frame tail tag value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack z)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest (suc z) tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) z state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have ht := andLeft (andRight (andRight (currentFields state stack z frame tail tag value hs hc hp)))
  apply liveInner guard leaf combine state stack z frame tail z hs hc
  apply zeroBranchIntro _ _ _ z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z xs hz ht (constantZeroValue xs))
  apply successorBranchIntro _ _ _ z z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      (suc z) tag (suc z) xs h1 ht (InternalLessThanSupportProof.oneConstantValue xs))
  exact zeroBranchIntro _ _ _ z xs (andRight (liveStateFields state stack z hs)) (constantZeroValue xs)

/-- Finish underflow with exactly one result is an actual zero transition. -/
theorem singletonResultsFailure (guard leaf : Program 1) (combine : Program 4)
    (state stack results frame tail tag value argument : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument z)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest (suc z) tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) z state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have ht := andLeft (andRight (andRight (currentFields state stack results frame tail tag value hs hc hp)))
  have hres := andRight (liveStateFields state stack results hs)
  have hd := InternalListCodecSupportProof.consDestruction results argument z hr
  apply liveInner guard leaf combine state stack results frame tail z hs hc
  apply zeroBranchIntro _ _ _ z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z xs hz ht (constantZeroValue xs))
  apply successorBranchIntro _ _ _ z z xs
    (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      (suc z) tag (suc z) xs h1 ht (InternalLessThanSupportProof.oneConstantValue xs))
  apply nonzeroBranchIntro _ _ _ z results xs hres
    (by simpa only [equalEqn] using andRight (andRight hd))
  exact zeroBranchIntro _ _ _ z xs
    (unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results z results xs
      (andLeft (andRight hd)) hres) (constantZeroValue xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameSupportProof
