module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineUnaryStatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineFinishProof
open OriginalLambdaTraversalInternalConstructorStateProof (liveOfRecover returnValue)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Inputs [erased type, child cutoff, original raw, child, work, stack, child output]. -/
def frameQ : Program 7 := .composition finishFrame (fun _ : Fin 1 => .projection 2)
def childFrameQ : Program 7 := .composition visitFrame ![.projection 0,.projection 1,.projection 3]
def workRetQ : Program 7 := consOf frameQ (.projection 4)
def workChildQ : Program 7 := consOf childFrameQ workRetQ
def resultQ : Program 7 := consOf (.projection 6) (.projection 5)
def stateOneQ : Program 7 := liveOf workChildQ (.projection 5)
def stateTwoQ : Program 7 := liveOf workRetQ resultQ
def queries : Fin 7 → Program 7 := ![frameQ,childFrameQ,workRetQ,workChildQ,resultQ,stateOneQ,stateTwoQ]

def Steps
    (initial final d child childK stack childOut workRet s1 s2 : OTerm alpha) : Formula alpha :=
  graph1 (OriginalStructuralNodeSize.transition) s1 initial ⊓
    (graph5 visitState s1 d childK child workRet stack ⊓
      (graph3 returnState s2 childOut workRet stack ⊓ graph1 (OriginalStructuralNodeSize.transition) final s2))

theorem atQueries
    (initial final d k raw child childK childOut produced work stack : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw childOut z)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState initial d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (ys : Fin 7 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation positive Delta
      (programGraph (queries i) (ys i) ![d,childK,raw,child,work,stack,childOut]))) :
    Nonempty (Derivation positive Delta
      (Steps initial final d child childK stack childOut (ys 2) (ys 5) (ys 6))) := by
  let xs : Fin 7 → OTerm alpha := ![d,childK,raw,child,work,stack,childOut]
  have hframe := unaryRecover finishFrame (.projection 2) (ys 0) raw xs (hq 0) (projectionValue 2 xs)
  have hcf := compositionRecover visitFrame ![.projection 0,.projection 1,.projection 3]
    (ys 1) xs ![d,childK,child] (hq 1) (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 3 xs) (fun a => Fin.elim0 a))) i)
  have hwr := binaryRecover InternalListCodec.consCode frameQ (.projection 4) (ys 2) (ys 0) work xs
    (hq 2) (hq 0) (projectionValue 4 xs)
  have hwc := binaryRecover InternalListCodec.consCode childFrameQ workRetQ (ys 3) (ys 1) (ys 2) xs
    (hq 3) (hq 1) (hq 2)
  have hrs := binaryRecover InternalListCodec.consCode (.projection 6) (.projection 5) (ys 4) childOut stack xs
    (hq 4) (projectionValue 6 xs) (projectionValue 5 xs)
  have hs1 := liveOfRecover workChildQ (.projection 5) (ys 5) (ys 3) stack xs
    (hq 5) (hq 3) (projectionValue 5 xs)
  have hs2 := liveOfRecover workRetQ resultQ (ys 6) (ys 2) (ys 4) xs (hq 6) (hq 2) (hq 4)
  have hstart := unaryExpand initial d k raw work stack (ys 5) child childK
    (ys 0) (ys 1) (ys 2) (ys 3) hi hf hframe hcf hwr hwc hs1
  have hfinish := unaryReturn (ys 6) raw work (ys 4) (ys 2) childOut stack produced final
    (openedFinish (ys 6) raw work (ys 4) (ys 0) (ys 2) hframe hwr hs2) (andLeft hf) hrs hp ho
  exact andIntro hstart (andIntro (visitValue (ys 5) d childK child (ys 2) stack (ys 1) (ys 3) hcf hwc hs1)
    (andIntro (returnValue (ys 6) childOut (ys 2) stack (ys 4) hrs hs2) hfinish))

theorem cases
    (initial final d k raw child childK childOut produced work stack : OTerm alpha)
    (psi : Formula alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw childOut z)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState initial d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (cont : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (workRet s1 s2 : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (Steps (initial.relabel j) (final.relabel j)
        (d.relabel j) (child.relabel j) (childK.relabel j) (stack.relabel j) (childOut.relabel j) workRet s1 s2)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) :
    Nonempty (Derivation positive Delta psi) := by
  apply queryCases queries (Fin.cons d (Fin.cons childK (Fin.cons raw (Fin.cons child
    (Fin.cons work (Fin.cons stack (Fin.cons childOut Fin.elim0))))))) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [graph3Rename,zRelabel] at hp' ho'
  rw [graph5Rename] at hi'
  exact cont beta j Theta (ys 2) (ys 5) (ys 6) hj
    (atQueries (initial.relabel j) (final.relabel j) (d.relabel j) (k.relabel j)
      (raw.relabel j) (child.relabel j) (childK.relabel j) (childOut.relabel j)
      (produced.relabel j) (work.relabel j) (stack.relabel j) hf' hp' hi' ho' ys hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineUnaryStatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineUnaryStatesProof
