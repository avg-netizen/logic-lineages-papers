module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalConstructorStateProof
open InternalApplicationResultStackComposition (liveState)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Inputs [domain,codomain,function,argument,parameter,work,results,function output,argument output]. -/
def frameQ : Program 9 := .composition applicationFrame ![.projection 0,.projection 1]
def fnFrameQ : Program 9 := .composition visitFrame ![.projection 2,.projection 4]
def argFrameQ : Program 9 := .composition visitFrame ![.projection 3,.projection 4]
def workRetQ : Program 9 := consOf frameQ (.projection 5)
def workArgQ : Program 9 := consOf argFrameQ workRetQ
def workFnQ : Program 9 := consOf fnFrameQ workArgQ
def fnStackQ : Program 9 := consOf (.projection 7) (.projection 6)
def argStackQ : Program 9 := consOf (.projection 8) fnStackQ
def stateOneQ : Program 9 := liveOf workFnQ (.projection 6)
def stateTwoQ : Program 9 := liveOf workArgQ fnStackQ
def stateThreeQ : Program 9 := liveOf workRetQ argStackQ
def queries : Fin 11 → Program 9 :=
  ![frameQ,fnFrameQ,argFrameQ,workRetQ,workArgQ,workFnQ,fnStackQ,argStackQ,stateOneQ,stateTwoQ,stateThreeQ]

/-- Graphs for the two child calls and the surrounding actual transitions. -/
def Steps (leaf : Program 2)
    (initial final fn arg parameter stack fOut aOut workRet workArg resultFn s1 s2 s3 : OTerm alpha) : Formula alpha :=
  graph1 (transition leaf) s1 initial ⊓
    (graph4 visitState s1 fn parameter workArg stack ⊓
      (graph3 returnState s2 fOut workArg stack ⊓
        (graph4 visitState s2 arg parameter workRet resultFn ⊓
          (graph3 returnState s3 aOut workRet resultFn ⊓ graph1 (transition leaf) final s3))))

theorem atQueries (leaf : Program 2)
    (initial final value produced d e fn arg parameter work stack fOut aOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph4 application produced d e fOut aOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState initial value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (ys : Fin 11 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation positive Delta
      (programGraph (queries i) (ys i) ![d,e,fn,arg,parameter,work,stack,fOut,aOut]))) :
    Nonempty (Derivation positive Delta (Steps leaf initial final fn arg parameter stack fOut aOut
      (ys 3) (ys 4) (ys 6) (ys 8) (ys 9) (ys 10))) := by
  let xs : Fin 9 → OTerm alpha := ![d,e,fn,arg,parameter,work,stack,fOut,aOut]
  have hframe := binaryRecover applicationFrame (.projection 0) (.projection 1) (ys 0) d e xs
    (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hff := binaryRecover visitFrame (.projection 2) (.projection 4) (ys 1) fn parameter xs
    (hq 1) (projectionValue 2 xs) (projectionValue 4 xs)
  have haf := binaryRecover visitFrame (.projection 3) (.projection 4) (ys 2) arg parameter xs
    (hq 2) (projectionValue 3 xs) (projectionValue 4 xs)
  have hwr := binaryRecover InternalListCodec.consCode frameQ (.projection 5) (ys 3) (ys 0) work xs
    (hq 3) (hq 0) (projectionValue 5 xs)
  have hwa := binaryRecover InternalListCodec.consCode argFrameQ workRetQ (ys 4) (ys 2) (ys 3) xs
    (hq 4) (hq 2) (hq 3)
  have hwf := binaryRecover InternalListCodec.consCode fnFrameQ workArgQ (ys 5) (ys 1) (ys 4) xs
    (hq 5) (hq 1) (hq 4)
  have hrs := binaryRecover InternalListCodec.consCode (.projection 7) (.projection 6) (ys 6) fOut stack xs
    (hq 6) (projectionValue 7 xs) (projectionValue 6 xs)
  have has := binaryRecover InternalListCodec.consCode (.projection 8) fnStackQ (ys 7) aOut (ys 6) xs
    (hq 7) (projectionValue 8 xs) (hq 6)
  have hs1 := liveOfRecover workFnQ (.projection 6) (ys 8) (ys 5) stack xs
    (hq 8) (hq 5) (projectionValue 6 xs)
  have hs2 := liveOfRecover workArgQ fnStackQ (ys 9) (ys 4) (ys 6) xs (hq 9) (hq 4) (hq 6)
  have hs3 := liveOfRecover workRetQ argStackQ (ys 10) (ys 3) (ys 7) xs (hq 10) (hq 3) (hq 7)
  have expanded := applicationExpandedValue (ys 8) value parameter work stack d e fn arg
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hf hframe hff haf hwr hwa hwf hs1
  have hstart := OriginalLambdaTraversalInternalVisitsProof.applicationBackward leaf initial value parameter work stack
    (ys 8) hi (andLeft hf) expanded
  have hfinishState := applicationReturnValue (ys 10) d e work aOut fOut stack
    (ys 0) (ys 3) (ys 6) (ys 7) hframe hwr hrs has hs3
  have hfinish := OriginalLambdaTraversalInternalReturnProof.applicationBackward leaf d e work aOut fOut stack
    (ys 10) produced final hfinishState hp ho
  exact andIntro hstart (andIntro (visitValue (ys 8) fn parameter (ys 4) stack (ys 1) (ys 5) hff hwf hs1)
    (andIntro (returnValue (ys 9) fOut (ys 4) stack (ys 6) hrs hs2)
      (andIntro (visitValue (ys 9) arg parameter (ys 3) (ys 6) (ys 2) (ys 4) haf hwa hs2)
        (andIntro (returnValue (ys 10) aOut (ys 3) (ys 6) (ys 7) has hs3) hfinish))))

theorem cases (leaf : Program 2)
    (initial final value produced d e fn arg parameter work stack fOut aOut : OTerm alpha)
    (psi : Formula alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph4 application produced d e fOut aOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState initial value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (workRet workArg resultFn s1 s2 s3 : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (Steps leaf (initial.relabel j) (final.relabel j)
        (fn.relabel j) (arg.relabel j) (parameter.relabel j) (stack.relabel j)
        (fOut.relabel j) (aOut.relabel j) workRet workArg resultFn s1 s2 s3)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) :
    Nonempty (Derivation positive Delta psi) := by
  apply queryCases queries (Fin.cons d (Fin.cons e (Fin.cons fn (Fin.cons arg (Fin.cons parameter (Fin.cons work (Fin.cons stack (Fin.cons fOut (Fin.cons aOut Fin.elim0))))))))) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [ApplicationFields,conjunctionRename,graph1Rename,
    SourceComputabilityFormulaSupportProof.numeral,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at hf'
  simp only [graph4Rename] at hp' hi'
  simp only [graph3Rename] at ho'
  exact k beta j Theta (ys 3) (ys 4) (ys 6) (ys 8) (ys 9) (ys 10) hj
    (atQueries leaf (initial.relabel j) (final.relabel j) (value.relabel j) (produced.relabel j)
      (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) (parameter.relabel j)
      (work.relabel j) (stack.relabel j) (fOut.relabel j) (aOut.relabel j) hf' hp' hi' ho' ys hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorApplicationProof
