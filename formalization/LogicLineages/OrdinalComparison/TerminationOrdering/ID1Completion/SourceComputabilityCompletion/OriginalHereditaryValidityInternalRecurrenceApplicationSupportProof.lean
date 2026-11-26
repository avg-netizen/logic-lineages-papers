module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalSourceInversionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalExtensionProof
open OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem applicationSuccessorCases (s t m : Program 2)
    (state workCode frame raw parameter : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (fn arg next nextWork suffix fnFrame argFrame : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 currentFunction fn (state.relabel j))) →
      Nonempty (Derivation body Delta (graph1 currentArgument arg (state.relabel j))) →
      Nonempty (Derivation body Delta
        (OriginalHereditaryValidityInternalPushSyntaxProof.appFields next fn arg
          (parameter.relabel j) z nextWork suffix fnFrame argFrame)) →
      Nonempty (Derivation body Delta (graph1 (transition s t m) next (state.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let ff := pairOf currentFunction currentParameter
  let af := pairOf currentArgument currentParameter
  let suffixProgram := consOf af rest
  let workProgram := consOf ff suffixProgram
  let qs : Fin 7 → Program 1 :=
    ![currentFunction,currentArgument,ff,af,suffixProgram,workProgram,applicationExpanded]
  apply queryCases qs (Fin.cons state Fin.elim0) psi
  intro beta j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  simp only [stateFrameRename,zRelabel] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [graph1Rename,oneRename] at hn'
  have ht' := renameInto ht j Delta hj
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at ht'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hparameter := frameParameter _ _ _ _ _ _ hs'
  have hf := binaryRecover InternalPairing.pairing currentFunction currentParameter
    (ys 2) (ys 0) (parameter.relabel j) xx (hq 2) (hq 0) hparameter
  have ha := binaryRecover InternalPairing.pairing currentArgument currentParameter
    (ys 3) (ys 1) (parameter.relabel j) xx (hq 3) (hq 1) hparameter
  have hsuffix := binaryRecover InternalListCodec.consCode af rest
    (ys 4) (ys 3) z xx (hq 4) (hq 3) (frameRest _ _ _ _ _ _ hs')
  have hw := binaryRecover InternalListCodec.consCode ff suffixProgram
    (ys 5) (ys 2) (ys 4) xx (hq 5) (hq 2) (hq 4)
  have hstate := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) workProgram
    (ys 6) (numeral 1) (ys 5) xx (hq 6) (InternalLessThanSupportProof.oneConstantValue xx) (hq 5)
  have htransition := acceptingVisitIntro s t m (state.relabel j) (workCode.relabel j)
    (frame.relabel j) (raw.relabel j) (parameter.relabel j) z (ys 6) hs' hn'
    (applicationIntro (state.relabel j) (ys 6) (frameTag _ _ _ _ _ _ (numeral 2) hs' ht') (hq 6))
  exact step beta j Delta (ys 0) (ys 1) (ys 6) (ys 5) (ys 4) (ys 2) (ys 3) hj
    (hq 0) (hq 1) (andIntro hstate (andIntro hw (andIntro hf (andIntro hsuffix ha)))) htransition

theorem rootApplicationAt (s t m : Program 2)
    (raw parameter state fn arg : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter)))
    (hf : Nonempty (Derivation body Gamma (graph1 currentFunction fn state)))
    (ha : Nonempty (Derivation body Gamma (graph1 currentArgument arg state)))
    (hc : Nonempty (Derivation body Gamma (RootApplicationChildren s t m raw parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) fn parameter ⊓
        graph2 (validator s t m) (numeral 1) arg parameter)) := by
  apply rootApplicationCases s t m raw parameter _ hc
  intro beta j Delta actualState actualFn actualArg hj fields
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) fn parameter).relabel j) ⊓
      ((graph2 (validator s t m) (numeral 1) arg parameter).relabel j)))
  simp only [graph2Rename,oneRename]
  have hi' := renameInto hi j Delta hj
  rw [graph2Rename] at hi'
  have hf' := renameInto hf j Delta hj
  rw [graph1Rename] at hf'
  have ha' := renameInto ha j Delta hj
  rw [graph1Rename] at ha'
  have heState := valueUnique initial actualState (state.relabel j)
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andLeft fields) hi'
  have hactualFn := headTransport currentFunction actualFn actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andRight fields))
  have hactualArg := headTransport currentArgument actualArg actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andLeft (andRight (andRight fields))))
  have heFn := valueUnique currentFunction actualFn (fn.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualFn hf'
  have heArg := valueUnique currentArgument actualArg (arg.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualArg ha'
  exact andIntro
    (headTransport (validator s t m) (numeral 1) actualFn (fn.relabel j)
      (Fin.cons (parameter.relabel j) Fin.elim0) heFn (andRight (andLeft (andRight (andRight fields)))))
    (headTransport (validator s t m) (numeral 1) actualArg (arg.relabel j)
      (Fin.cons (parameter.relabel j) Fin.elim0) heArg (andRight (andRight (andRight fields))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
