module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace

/-- Acceptance of the closed recognizer's finish transfers at the SAME actual
state. No native decoding or final-tuple identification is assumed. -/
def FinishFactor : Prop := ∀ (source : Program 2) (H G : Program 1)
 (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (out : OTerm alpha),
 Nonempty (Derivation body Delta (graph1
  (finish source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) (suc z) out)) →
 Nonempty (Derivation body Delta (graph1
  (finish source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))

/-- A nonrejecting selected step retains its exact successor. In particular,
lambda-first priority must be respected in the application branch. This is
not unconditional equality of the two transition Programs. -/
def AcceptedStep : Prop := ∀ (source : Program 2) (H G : Program 1)
 (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (state next : OTerm alpha),
 Nonempty (Derivation body Delta (graph1
  (transition source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) next state)) →
 Nonempty (Derivation body Delta (eqn next z).not) →
 Nonempty (Derivation body Delta (graph1
  (transition source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) next state))

/-- An accepting original-path run transfers with the SAME path, initial
state and final state. The entire smaller-path induction is internal. -/
def AcceptingRun : Prop := ∀ (source : Program 2) (H G : Program 1)
 (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (out path state : OTerm alpha),
 Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) out path state)) →
 Nonempty (Derivation body Delta (graph1
  (finish source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) (suc z) out)) →
 Nonempty (Derivation body Delta
  (InternalRawListRepeat.repeatGraph
   (transition source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out path state ⊓
   graph1 (finish source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))

/-- The actual closed checker implies recognition by its actual underlying
leaf at identical source, target, certificate and runtime parameter. No
recognition supplier or unrestricted-source closure is an added premise. -/
def RecognizesFactor : Prop := ∀ (source : Program 2) (H G : Program 1)
 (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph4
  (recognizes source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) (suc z) s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4
  (recognizes source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionTargets
