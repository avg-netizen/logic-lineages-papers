module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalSourceInversionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalExtensionProof
open OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Construct the actual lambda successor and its singleton child frame in
one internal query. The body and extended parameter are the real selectors. -/
theorem lambdaSuccessorCases (s t m : Program 2)
    (state workCode frame raw parameter : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (child childParameterCode next nextWork nextFrame : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 currentBody child (state.relabel j))) →
      Nonempty (Derivation body Delta (graph1 childParameter childParameterCode (state.relabel j))) →
      Nonempty (Derivation body Delta
        (ExtendedParameter (raw.relabel j) (parameter.relabel j) childParameterCode)) →
      Nonempty (Derivation body Delta (StateFrame next nextWork nextFrame child childParameterCode z)) →
      Nonempty (Derivation body Delta (graph1 (transition s t m) next (state.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let frameProgram := pairOf currentBody childParameter
  let workProgram := consOf frameProgram rest
  let qs : Fin 5 → Program 1 := ![currentBody,childParameter,frameProgram,workProgram,lambdaExpanded]
  apply queryCases qs (Fin.cons state Fin.elim0) psi
  intro beta j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  simp only [stateFrameRename,zRelabel] at hs'
  have hn' := renameInto hn j Delta hj
  simp only [graph1Rename,oneRename] at hn'
  have ht' := renameInto ht j Delta hj
  simp only [graph1Rename,oneRename] at ht'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hf := binaryRecover InternalPairing.pairing currentBody childParameter
    (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
  have hw := binaryRecover InternalListCodec.consCode frameProgram rest
    (ys 3) (ys 2) z xx (hq 3) (hq 2)
    (frameRest (state.relabel j) (workCode.relabel j) (frame.relabel j)
      (raw.relabel j) (parameter.relabel j) z hs')
  have hstate := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) workProgram
    (ys 4) (numeral 1) (ys 3) xx (hq 4) (InternalLessThanSupportProof.oneConstantValue xx) (hq 3)
  have he := childParameterExtension (state.relabel j) (raw.relabel j) (parameter.relabel j) (ys 1)
    (frameRaw _ _ _ _ _ _ hs') (frameParameter _ _ _ _ _ _ hs') (hq 1)
  have htransition := acceptingVisitIntro s t m (state.relabel j) (workCode.relabel j)
    (frame.relabel j) (raw.relabel j) (parameter.relabel j) z (ys 4) hs' hn'
    (lambdaIntro (state.relabel j) (ys 4) (frameTag _ _ _ _ _ _ (numeral 1) hs' ht') (hq 4))
  exact step beta j Delta (ys 0) (ys 1) (ys 4) (ys 3) (ys 2) hj (hq 0) (hq 1) he
    (andIntro hstate (andIntro hw hf)) htransition

/-- Existential root witnesses cannot choose a different body or parameter:
original initial/selector functionality identifies them at the requested
same initial state and transports the identical validator graph. -/
theorem rootLambdaAt (s t m : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter)))
    (hc : Nonempty (Derivation body Gamma (graph1 currentBody child state)))
    (hp : Nonempty (Derivation body Gamma (graph1 childParameter childParameterCode state)))
    (hl : Nonempty (Derivation body Gamma (RootLambdaChild s t m raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) (numeral 1) child childParameterCode)) := by
  apply rootLambdaCases s t m raw parameter _ hl
  intro beta j Delta actualState actualChild actualParameter hj fields
  simp only [graph2Rename,oneRename]
  have hi' := renameInto hi j Delta hj
  rw [graph2Rename] at hi'
  have hc' := renameInto hc j Delta hj
  rw [graph1Rename] at hc'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  have heState := valueUnique initial actualState (state.relabel j)
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andLeft fields) hi'
  have hactualChild := headTransport currentBody actualChild actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andLeft (andRight fields)))
  have hactualParameter := headTransport childParameter actualParameter actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andRight (andRight fields)))
  have heChild := valueUnique currentBody actualChild (child.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualChild hc'
  have heParameter := valueUnique childParameter actualParameter (childParameterCode.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualParameter hp'
  apply graphInputTransport body beta 2 Delta (OrdinaryArithmetic.graphFormula (validator s t m))
    (numeral 1) (Fin.cons actualChild (Fin.cons actualParameter Fin.elim0))
    (Fin.cons (child.relabel j) (Fin.cons (childParameterCode.relabel j) Fin.elim0)) _
    (andRight (andRight (andRight fields)))
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact heChild
  · rw [onEquality]; exact heParameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
