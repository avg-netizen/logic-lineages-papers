module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryStatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineFinishProof OriginalStructuralNodeSizeInternalMachineBinaryExpansionProof
open OriginalStructuralNodeSizeInternalMachineBinaryFinishProof
open OriginalLambdaTraversalInternalConstructorStateProof (liveOfRecover returnValue)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Inputs [erased type, cutoff, original raw, first, second, work, stack, first output, second output]. -/
def frameQ : Program 9 := .composition finishFrame (fun _ : Fin 1 => .projection 2)
def firstFrameQ : Program 9 := .composition visitFrame ![.projection 0,.projection 1,.projection 3]
def secondFrameQ : Program 9 := .composition visitFrame ![.projection 0,.projection 1,.projection 4]
def workRetQ : Program 9 := consOf frameQ (.projection 5)
def workSecondQ : Program 9 := consOf secondFrameQ workRetQ
def workFirstQ : Program 9 := consOf firstFrameQ workSecondQ
def resultFirstQ : Program 9 := consOf (.projection 7) (.projection 6)
def resultSecondQ : Program 9 := consOf (.projection 8) resultFirstQ
def stateOneQ : Program 9 := liveOf workFirstQ (.projection 6)
def stateTwoQ : Program 9 := liveOf workSecondQ resultFirstQ
def stateThreeQ : Program 9 := liveOf workRetQ resultSecondQ
def queries : Fin 11 → Program 9 :=
  ![frameQ,firstFrameQ,secondFrameQ,workRetQ,workSecondQ,workFirstQ,resultFirstQ,resultSecondQ,stateOneQ,stateTwoQ,stateThreeQ]

def Steps
    (initial final d k first second stack firstOut secondOut workRet workSecond resultFirst s1 s2 s3 : OTerm alpha) : Formula alpha :=
  graph1 (OriginalStructuralNodeSize.transition) s1 initial ⊓
    (graph5 visitState s1 d k first workSecond stack ⊓
      (graph3 returnState s2 firstOut workSecond stack ⊓
        (graph5 visitState s2 d k second workRet resultFirst ⊓
          (graph3 returnState s3 secondOut workRet resultFirst ⊓ graph1 (OriginalStructuralNodeSize.transition) final s3))))

theorem atQueries
    (initial final d k raw first second firstOut secondOut produced work stack : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw firstOut secondOut)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState initial d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (ys : Fin 11 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation positive Delta
      (programGraph (queries i) (ys i) ![d,k,raw,first,second,work,stack,firstOut,secondOut]))) :
    Nonempty (Derivation positive Delta
      (Steps initial final d k first second stack firstOut secondOut
        (ys 3) (ys 4) (ys 6) (ys 8) (ys 9) (ys 10))) := by
  let xs : Fin 9 → OTerm alpha := ![d,k,raw,first,second,work,stack,firstOut,secondOut]
  have hframe := unaryRecover finishFrame (.projection 2) (ys 0) raw xs (hq 0) (projectionValue 2 xs)
  have hff := compositionRecover visitFrame ![.projection 0,.projection 1,.projection 3]
    (ys 1) xs ![d,k,first] (hq 1) (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 3 xs) (fun a => Fin.elim0 a))) i)
  have hsf := compositionRecover visitFrame ![.projection 0,.projection 1,.projection 4]
    (ys 2) xs ![d,k,second] (hq 2) (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 4 xs) (fun a => Fin.elim0 a))) i)
  have hwr := binaryRecover InternalListCodec.consCode frameQ (.projection 5) (ys 3) (ys 0) work xs
    (hq 3) (hq 0) (projectionValue 5 xs)
  have hws := binaryRecover InternalListCodec.consCode secondFrameQ workRetQ (ys 4) (ys 2) (ys 3) xs
    (hq 4) (hq 2) (hq 3)
  have hwf := binaryRecover InternalListCodec.consCode firstFrameQ workSecondQ (ys 5) (ys 1) (ys 4) xs
    (hq 5) (hq 1) (hq 4)
  have hrf := binaryRecover InternalListCodec.consCode (.projection 7) (.projection 6) (ys 6) firstOut stack xs
    (hq 6) (projectionValue 7 xs) (projectionValue 6 xs)
  have hrs := binaryRecover InternalListCodec.consCode (.projection 8) resultFirstQ (ys 7) secondOut (ys 6) xs
    (hq 7) (projectionValue 8 xs) (hq 6)
  have hs1 := liveOfRecover workFirstQ (.projection 6) (ys 8) (ys 5) stack xs
    (hq 8) (hq 5) (projectionValue 6 xs)
  have hs2 := liveOfRecover workSecondQ resultFirstQ (ys 9) (ys 4) (ys 6) xs (hq 9) (hq 4) (hq 6)
  have hs3 := liveOfRecover workRetQ resultSecondQ (ys 10) (ys 3) (ys 7) xs (hq 10) (hq 3) (hq 7)
  have hstart := binaryExpand initial d k raw work stack (ys 8) first second
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hi hf hframe hff hsf hwr hws hwf hs1
  have hfinish := binaryReturn (ys 10) raw work (ys 7) (ys 3) firstOut secondOut (ys 6) stack produced final
    (openedFinish (ys 10) raw work (ys 7) (ys 0) (ys 3) hframe hwr hs3) (andLeft hf) hrs hrf hp ho
  exact andIntro hstart
    (andIntro (visitValue (ys 8) d k first (ys 4) stack (ys 1) (ys 5) hff hwf hs1)
      (andIntro (returnValue (ys 9) firstOut (ys 4) stack (ys 6) hrf hs2)
        (andIntro (visitValue (ys 9) d k second (ys 3) (ys 6) (ys 2) (ys 4) hsf hws hs2)
          (andIntro (returnValue (ys 10) secondOut (ys 3) (ys 6) (ys 7) hrs hs3) hfinish))))

theorem cases
    (initial final d k raw first second firstOut secondOut produced work stack : OTerm alpha)
    (psi : Formula alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw firstOut secondOut)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState initial d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (cont : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (workRet workSecond resultFirst s1 s2 s3 : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (Steps (initial.relabel j) (final.relabel j)
        (d.relabel j) (k.relabel j) (first.relabel j) (second.relabel j) (stack.relabel j)
        (firstOut.relabel j) (secondOut.relabel j) workRet workSecond resultFirst s1 s2 s3)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) :
    Nonempty (Derivation positive Delta psi) := by
  apply queryCases queries (Fin.cons d (Fin.cons k (Fin.cons raw (Fin.cons first
    (Fin.cons second (Fin.cons work (Fin.cons stack (Fin.cons firstOut (Fin.cons secondOut Fin.elim0))))))))) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [binaryFieldsRename] at hf'
  rw [graph3Rename] at hp' ho'
  rw [graph5Rename] at hi'
  exact cont beta j Theta (ys 3) (ys 4) (ys 6) (ys 8) (ys 9) (ys 10) hj
    (atQueries (initial.relabel j) (final.relabel j) (d.relabel j) (k.relabel j)
      (raw.relabel j) (first.relabel j) (second.relabel j) (firstOut.relabel j) (secondOut.relabel j)
      (produced.relabel j) (work.relabel j) (stack.relabel j) hf' hp' hi' ho' ys hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryStatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryStatesProof
