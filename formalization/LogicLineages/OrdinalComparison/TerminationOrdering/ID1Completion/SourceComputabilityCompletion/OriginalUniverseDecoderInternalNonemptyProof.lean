module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSwitchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalNonemptyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalTypedDecoder (ifSame headOf tailOf)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalListProof
open OriginalTypedDecoderInternalBranchProof
open OriginalUniverseDecoderInternalSyntaxProof OriginalUniverseDecoderInternalGuardProof
open OriginalUniverseDecoderInternalDecisionProof OriginalUniverseDecoderInternalSwitchProof
open OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal subtrees of the frozen universe transition. -/
def stateInput : Program 2 := .projection 0
def stateStatus : Program 2 := leftOf stateInput
def stateWork : Program 2 := rightOf stateInput
def stateHead : Program 2 := headOf stateWork
def stateTail : Program 2 := tailOf stateWork
def guardTest (M W : Program 2) : Program 2 :=
  .composition (OriginalUniverseDecoder.guard M W) ![stateHead,.projection 1]
def oldStep (H : Program 1) : Program 2 :=
  .composition (OriginalTypedDecoder.transition H) ![.projection 0]
def guardedStep (H : Program 1) (M W : Program 2) : Program 2 :=
  ifSame (guardTest M W) (constant 2 1) (oldStep H) (constant 2 0)

theorem guardTestEquivalence (M W : Program 2) (input c r : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 stateHead r input c))) :
    Nonempty (Derivation body Delta
      ((graph2 (guardTest M W) (numeral 1) input c).iff (guardSpec M W (numeral 1) r c))) := by
  let xs : Fin 2 → OTerm alpha := ![input,c]
  let P := graph2 (guardTest M W) (numeral 1) input c
  let Q := guardSpec M W (numeral 1) r c
  have hf := guardForward M W (numeral 1) r c
    (binaryRecover (OriginalUniverseDecoder.guard M W) stateHead (.projection 1) (numeral 1) r c xs
      (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hr P) (projectionValue 1 xs))
  have hb := binaryValue (OriginalUniverseDecoder.guard M W) stateHead (.projection 1) (numeral 1) r c xs
    (guardBackward M W (numeral 1) r c
      (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩))
    (withHyp hr Q) (projectionValue 1 xs)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem oldForward (H : Program 1) (out input c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 (oldStep H) out input c))) :
    Nonempty (Derivation body Delta (OriginalTypedDecoderStepSpecification.stepSpec H out input)) := by
  apply OriginalTypedDecoderInternalProof.fullForward H out input
  apply compositionRecover (OriginalTypedDecoder.transition H) ![.projection 0] out
    (![input,c] : Fin 2 → OTerm alpha) (Fin.cons input Fin.elim0) ho
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![input,c]

theorem oldBackward (H : Program 1) (out input c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (OriginalTypedDecoderStepSpecification.stepSpec H out input))) :
    Nonempty (Derivation body Delta (graph2 (oldStep H) out input c)) := by
  apply compositionValue (OriginalTypedDecoder.transition H) ![.projection 0] out
    (![input,c] : Fin 2 → OTerm alpha) (Fin.cons input Fin.elim0)
    (OriginalTypedDecoderInternalProof.fullBackward H out input ho)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![input,c]

/-- Nonempty work supplies its actual original request and suffix. The guard
is decided internally and the original typed step is invoked at the SAME state. -/
theorem nonemptyForward (H : Program 1) (M W : Program 2) (out input w c : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 stateWork w input c)))
    (hn : Nonempty (Derivation body Delta (equal w (numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (graph2 (guardedStep H M W) out input c))) :
    Nonempty (Derivation body Delta (nonemptySpec H M W out input w c)) := by
  apply queryCases (![stateHead,stateTail] : Fin 2 → Program 2) (![input,c] : Fin 2 → OTerm alpha) _
  intro beta j ys Theta hj hq
  rw [nonemptyRename]
  have hw' := renameInto hw j Theta hj
  have hn' := renameInto hn j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph2Rename] at hw' ho'
  have hnz : Nonempty (Derivation body Theta (equal (w.relabel j) (numeral 0)).not) := by
    simpa using hn'
  simp only [Matrix.vecCons,Matrix.vecEmpty,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := ![input.relabel j,c.relabel j]
  have hcons := consFields (w.relabel j) (ys 0) (ys 1) hnz
    (arrowFields stateWork (w.relabel j) (ys 0) (ys 1) xx hw' (hq 0) (hq 1))
  have hi := guardTestEquivalence M W (input.relabel j) (c.relabel j) (ys 0) (hq 0)
  apply nonemptyIntro H M W _ _ _ _ ys
  apply andIntro hcons
  let C := guardSpec M W (numeral 1) (ys 0) (c.relabel j)
  apply formulaCases C _
  · have hc : Nonempty (Derivation body (C :: Theta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg := impApply (withHyp (andRight hi) C) hc
    have ht := exactOneYesElim (guardTest M W) (oldStep H) (constant 2 0) (out.relabel j) xx hg (withHyp ho' C)
    obtain ⟨hgood⟩ := andIntro hc (oldForward H (out.relabel j) (input.relabel j) (c.relabel j) ht)
    exact ⟨orLeft hgood⟩
  · have hc : Nonempty (Derivation body (C.not :: Theta) C.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg := contrapose (withHyp (andLeft hi) C.not) hc
    have hz := exactOneNoElim (guardTest M W) (oldStep H) (constant 2 0) (out.relabel j) xx hg (withHyp ho' C.not)
    obtain ⟨hbad⟩ := andIntro hc (constantForward 0 (out.relabel j) xx hz)
    exact ⟨orRight hbad⟩

theorem nonemptyBackward (H : Program 1) (M W : Program 2) (out input w c : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 stateWork w input c)))
    (ho : Nonempty (Derivation body Delta (nonemptySpec H M W out input w c))) :
    Nonempty (Derivation body Delta (graph2 (guardedStep H M W) out input c)) := by
  apply nonemptyCases H M W out input w c _ ho
  intro beta j Theta ys hj hq
  rw [graph2Rename]
  have hw' := renameInto hw j Theta hj
  rw [graph2Rename] at hw'
  let xx : Fin 2 → OTerm beta := ![input.relabel j,c.relabel j]
  have hr := headValue stateWork (w.relabel j) (ys 0) (ys 1) xx hw'
    (consArrowFields (w.relabel j) (ys 0) (ys 1) (andLeft hq))
  have hi := guardTestEquivalence M W (input.relabel j) (c.relabel j) (ys 0) hr
  let C := guardSpec M W (numeral 1) (ys 0) (c.relabel j)
  let T := OriginalTypedDecoderStepSpecification.stepSpec H (out.relabel j) (input.relabel j)
  apply orCases (andRight hq)
  · have hgood : Nonempty (Derivation body ((C ⊓ T) :: Theta) (C ⊓ T)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact exactOneYesIntro (guardTest M W) (oldStep H) (constant 2 0) (out.relabel j) xx
      (impApply (withHyp (andRight hi) _) (andLeft hgood))
      (oldBackward H (out.relabel j) (input.relabel j) (c.relabel j) (andRight hgood))
  · have hbad : Nonempty (Derivation body ((C.not ⊓ equal (out.relabel j) (numeral 0)) :: Theta)
        (C.not ⊓ equal (out.relabel j) (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact exactOneNoIntro (guardTest M W) (oldStep H) (constant 2 0) (out.relabel j) xx
      (contrapose (withHyp (andLeft hi) _) (andLeft hbad))
      (constantBackward 0 (out.relabel j) xx (andRight hbad))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalNonemptyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalNonemptyProof
