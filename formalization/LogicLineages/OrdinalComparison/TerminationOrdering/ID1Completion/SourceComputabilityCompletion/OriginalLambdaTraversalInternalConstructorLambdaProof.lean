module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorLambdaProof
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

/-- Inputs [domain,codomain,body,body parameter,work,results,body output]. -/
def frameQ : Program 7 := .composition lambdaFrame ![.projection 0,.projection 1]
def bodyFrameQ : Program 7 := .composition visitFrame ![.projection 2,.projection 3]
def workRetQ : Program 7 := consOf frameQ (.projection 4)
def workBodyQ : Program 7 := consOf bodyFrameQ workRetQ
def resultQ : Program 7 := consOf (.projection 6) (.projection 5)
def stateOneQ : Program 7 := liveOf workBodyQ (.projection 5)
def stateTwoQ : Program 7 := liveOf workRetQ resultQ
def queries : Fin 7 → Program 7 :=
  ![frameQ,bodyFrameQ,workRetQ,workBodyQ,resultQ,stateOneQ,stateTwoQ]

/-- Graphs for the body call and the surrounding actual transitions. -/
def Steps (leaf : Program 2)
    (initial final body bodyParameter stack bodyOut workRet s1 s2 : OTerm alpha) : Formula alpha :=
  graph1 (transition leaf) s1 initial ⊓
    (graph4 visitState s1 body bodyParameter workRet stack ⊓
      (graph3 returnState s2 bodyOut workRet stack ⊓ graph1 (transition leaf) final s2))

theorem atQueries (leaf : Program 2)
    (initial final value produced d e body parameter bodyParameter work stack bodyOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor produced d e bodyOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState initial value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (ys : Fin 7 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation positive Delta
      (programGraph (queries i) (ys i) ![d,e,body,bodyParameter,work,stack,bodyOut]))) :
    Nonempty (Derivation positive Delta (Steps leaf initial final body bodyParameter stack bodyOut
      (ys 2) (ys 5) (ys 6))) := by
  let xs : Fin 7 → OTerm alpha := ![d,e,body,bodyParameter,work,stack,bodyOut]
  have hframe := binaryRecover lambdaFrame (.projection 0) (.projection 1) (ys 0) d e xs
    (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hbf := binaryRecover visitFrame (.projection 2) (.projection 3) (ys 1) body bodyParameter xs
    (hq 1) (projectionValue 2 xs) (projectionValue 3 xs)
  have hwr := binaryRecover InternalListCodec.consCode frameQ (.projection 4) (ys 2) (ys 0) work xs
    (hq 2) (hq 0) (projectionValue 4 xs)
  have hwb := binaryRecover InternalListCodec.consCode bodyFrameQ workRetQ (ys 3) (ys 1) (ys 2) xs
    (hq 3) (hq 1) (hq 2)
  have hrs := binaryRecover InternalListCodec.consCode (.projection 6) (.projection 5) (ys 4) bodyOut stack xs
    (hq 4) (projectionValue 6 xs) (projectionValue 5 xs)
  have hs1 := liveOfRecover workBodyQ (.projection 5) (ys 5) (ys 3) stack xs
    (hq 5) (hq 3) (projectionValue 5 xs)
  have hs2 := liveOfRecover workRetQ resultQ (ys 6) (ys 2) (ys 4) xs (hq 6) (hq 2) (hq 4)
  have expanded := lambdaExpandedValue (ys 5) value parameter work stack d e body bodyParameter
    (ys 0) (ys 1) (ys 2) (ys 3) hf hframe hbf hwr hwb hs1
  have hstart := OriginalLambdaTraversalInternalVisitsProof.lambdaBackward leaf initial value parameter work stack
    (ys 5) hi (andLeft hf) expanded
  have hfinishState := lambdaReturnValue (ys 6) d e work bodyOut stack
    (ys 0) (ys 2) (ys 4) hframe hwr hrs hs2
  have hfinish := OriginalLambdaTraversalInternalReturnProof.lambdaBackward leaf d e work bodyOut stack
    (ys 6) produced final hfinishState hp ho
  exact andIntro hstart (andIntro (visitValue (ys 5) body bodyParameter (ys 2) stack (ys 1) (ys 3) hbf hwb hs1)
    (andIntro (returnValue (ys 6) bodyOut (ys 2) stack (ys 4) hrs hs2) hfinish))

theorem cases (leaf : Program 2)
    (initial final value produced d e body parameter bodyParameter work stack bodyOut : OTerm alpha)
    (psi : Formula alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor produced d e bodyOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState initial value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState final produced work stack)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (workRet s1 s2 : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (Steps leaf (initial.relabel j) (final.relabel j)
        (body.relabel j) (bodyParameter.relabel j) (stack.relabel j)
        (bodyOut.relabel j) workRet s1 s2)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) :
    Nonempty (Derivation positive Delta psi) := by
  apply queryCases queries (Fin.cons d (Fin.cons e (Fin.cons body (Fin.cons bodyParameter (Fin.cons work (Fin.cons stack (Fin.cons bodyOut Fin.elim0))))))) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [LambdaFields,conjunctionRename,graph1Rename,graph2Rename,
    InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at hf'
  simp only [graph3Rename] at hp' ho'
  simp only [graph4Rename] at hi'
  exact k beta j Theta (ys 2) (ys 5) (ys 6) hj
    (atQueries leaf (initial.relabel j) (final.relabel j) (value.relabel j) (produced.relabel j)
      (d.relabel j) (e.relabel j) (body.relabel j) (parameter.relabel j) (bodyParameter.relabel j)
      (work.relabel j) (stack.relabel j) (bodyOut.relabel j) hf' hp' hi' ho' ys hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorLambdaProof
