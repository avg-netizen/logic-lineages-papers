module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedFinalErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.RecognizerCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.RecognizedErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumClassSelectionProof
public meta import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.FinalErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open OriginalTransparentLambdaFinalLogicProof (iffSelf orIff)
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness WitnessMatrix Certificate)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessRename witnessIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open GraphCongruenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

/-- Both actual source and leaf graphs may be changed only through proved
internal equivalence. Every original recognizer guard, failure, selected state,
path recursion and terminal test is transported by the proven PR congruence. -/
theorem recognizesCongruence (source otherSource : Program 2) (leaf otherLeaf : Program 4)
    (hs : ProgramGraphEquivalent source otherSource)
    (hl : ProgramGraphEquivalent leaf otherLeaf) :
    ProgramGraphEquivalent (OriginalMixedDirectBottomTrace.recognizes source leaf)
      (OriginalMixedDirectBottomTrace.recognizes otherSource otherLeaf) := by
  exact RecognizerCongruenceProof.recognizes hs hl

theorem finalSource (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    ProgramGraphEquivalent
      (InternalOriginalUniformDescentSelection.validity (preparedKernelFinalData p H G W P))
      (OriginalTransparentMixedDirectBottom.source H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W) := by
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let seed := OriginalTransparentMinimum.minimumInputs H G Q q
  let guarded := OriginalRankGuardedRepresentative.guardedInputs H G W seed
  intro body alpha Delta out xs
  have hx : ![xs 0,xs 1] = xs := by
    funext i
    fin_cases i <;> rfl
  rw [← hx]
  exact OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse
    guarded H G W body alpha Delta out (xs 0) (xs 1)

/-- Reuse the original existential certificate binder. Only its actual leaf
graph is transported, at identical source/target/certificate/parameter inputs. -/
theorem witnessForward (leaf otherLeaf : Program 4) (he : ProgramGraphEquivalent leaf otherLeaf)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (Witness leaf s t parameter))) :
    Nonempty (Derivation body Delta (Witness otherLeaf s t parameter)) := by
  obtain ⟨hw⟩ := hw
  apply Nonempty.intro
  apply Derivation.existentialElimination hw
  change Derivation body (WitnessMatrix leaf s t parameter :: Delta.map weaken)
    ((Witness otherLeaf s t parameter).relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  rw [witnessRename]
  let Theta := WitnessMatrix leaf s t parameter :: Delta.map weaken
  have hc : Nonempty (Derivation body Theta
      (Certificate leaf (s.relabel Sum.inl) (t.relabel Sum.inl)
        (parameter.relabel Sum.inl) (.var (.inr 0)))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (witnessIntro otherLeaf (s.relabel Sum.inl) (t.relabel Sum.inl)
    (parameter.relabel Sum.inl) (.var (.inr 0))
    (iffForward (he body (alpha ⊕ Fin 1) Theta (numeral 1)
      ![s.relabel Sum.inl,t.relabel Sum.inl,.var (.inr 0),parameter.relabel Sum.inl]) hc))

theorem witnessEquivalent (leaf otherLeaf : Program 4) (he : ProgramGraphEquivalent leaf otherLeaf)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter : OTerm alpha) :
    Nonempty (Derivation body Delta ((Witness leaf s t parameter).iff (Witness otherLeaf s t parameter))) := by
  let A := Witness leaf s t parameter
  let B := Witness otherLeaf s t parameter
  obtain ⟨hf⟩ := witnessForward leaf otherLeaf he body alpha (A :: Delta) s t parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := witnessForward otherLeaf leaf (equivalentReverse he) body alpha (B :: Delta) s t parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem resultForward (leaf otherLeaf : Program 4) (he : ProgramGraphEquivalent leaf otherLeaf)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter oldS oldT : OTerm alpha)
    (hr : Nonempty (Derivation body Delta
      (OriginalExistentialRankResultDefinitions.Result leaf s t parameter oldS oldT))) :
    Nonempty (Derivation body Delta
      (OriginalExistentialRankResultDefinitions.Result otherLeaf s t parameter oldS oldT)) :=
  iffForward (orIff (iffSelf _)
    (witnessEquivalent leaf otherLeaf he body alpha Delta s t parameter)) hr

theorem actualPreparedKernelFinalErasure : ActualPreparedKernelFinalErasure := by
  intro p H G W P
  dsimp only [FinalRecognizedErasure]
  intro body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  let D := preparedKernelFinalData p H G W P
  let leaf := (preparedKernelFinalInputs p H G W P).oldStep
  let source := InternalOriginalUniformDescentSelection.validity D
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  let literalSource := OriginalTransparentMixedDirectBottom.source H G M W
  let checker := OriginalMixedClosedTraceDefinitions.checker H G M W p.oldStep p.window
  let A := graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf)
      (numeral 1) s t cert oldParam ⊓
    (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing oldParam c extended ⊓
    (graph2 InternalPairing.pairing newParam c gamma ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
      graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))
  have ha : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := finalSource p H G W P
  have hl := ClosedTransportProof.actualPreparedKernelClosedChecker p H G W P
  have hrec := iffForward
    (recognizesCongruence source literalSource leaf checker hs hl
      body alpha (A :: Delta) (numeral 1) ![s,t,cert,oldParam]) (andLeft ha)
  obtain ⟨law⟩ := Erasure.RecognizedErasureProof.closedRecognizedErasure
    H G M W p.oldStep p.window body alpha (A :: Delta)
    s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  obtain ⟨hin⟩ := andIntro hrec (andRight ha)
  have result : Nonempty (Derivation body (A :: Delta)
      (graph2 literalSource (numeral 1) erasedS newParam ⊓
        OriginalExistentialRankResultDefinitions.Result checker erasedS erasedT newParam s t)) :=
    ⟨Derivation.implicationElimination law hin⟩
  obtain ⟨hout⟩ := andIntro
    (iffBackward (hs body alpha (A :: Delta) (numeral 1) ![erasedS,newParam]) (andLeft result))
    (resultForward checker leaf (equivalentReverse hl) body alpha (A :: Delta)
      erasedS erasedT newParam s t (andRight result))
  exact ⟨Derivation.implicationIntroduction hout⟩

theorem actualPreparedKernelFinalSelection : ActualPreparedKernelFinalSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ :=
    OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,OriginalMixedPreparedProof.actualRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP,
    actualPreparedKernelFinalErasure p H G W P⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.FinalErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.FinalErasureProof
