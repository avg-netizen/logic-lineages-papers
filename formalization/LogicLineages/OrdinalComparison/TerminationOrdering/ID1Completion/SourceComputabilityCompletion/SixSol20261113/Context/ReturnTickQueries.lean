module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReturnTickQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem withTick (R : Program 2) (frame produced value : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (work input stack output root tail returned deletionRow : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode work (frame.relabel j) z)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing input work (produced.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing output z stack)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode stack (value.relabel j) z)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (value.relabel j) root tail)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing tail returned deletionRow)) →
      Nonempty (Derivation body Theta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc z) input)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let zeroP : Program 3 := OriginalRawSyntaxTransport.constant 3 0
  let workP : Program 3 := consOf (.projection 0) zeroP
  let inputP : Program 3 := pairOf workP (.projection 1)
  let stackP : Program 3 := consOf (.projection 2) zeroP
  let outputP : Program 3 := pairOf zeroP stackP
  let rootP : Program 3 := leftOf (.projection 2)
  let tailP : Program 3 := rightOf (.projection 2)
  let returnedP : Program 3 := leftOf tailP
  let deletionP : Program 3 := rightOf tailP
  let qs : Fin 8 → Program 3 := ![workP,inputP,stackP,outputP,rootP,tailP,returnedP,deletionP]
  let xs : Fin 3 → OTerm alpha := ![frame,produced,value]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
  intro beta j ys Theta hi hq
  let xx : Fin 3 → OTerm beta := ![frame.relabel j,produced.relabel j,value.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hx] at hq
  have hz : Nonempty (Derivation body Theta (programGraph zeroP z xx)) :=
    OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
  have hw := binaryRecover InternalListCodec.consCode (.projection 0) zeroP
    (ys 0) (frame.relabel j) z xx (hq 0) (projectionValue 0 xx) hz
  have hin := binaryRecover InternalPairing.pairing workP (.projection 1)
    (ys 1) (ys 0) (produced.relabel j) xx (hq 1) (hq 0) (projectionValue 1 xx)
  have hs := binaryRecover InternalListCodec.consCode (.projection 2) zeroP
    (ys 2) (value.relabel j) z xx (hq 2) (projectionValue 2 xx) hz
  have ho := binaryRecover InternalPairing.pairing zeroP stackP
    (ys 3) z (ys 2) xx (hq 3) hz (hq 2)
  have hroot := unaryRecover InternalUnpair.left (.projection 2) (ys 4) (value.relabel j) xx (hq 4) (projectionValue 2 xx)
  have htail := unaryRecover InternalUnpair.right (.projection 2) (ys 5) (value.relabel j) xx (hq 5) (projectionValue 2 xx)
  have hreturned := unaryRecover InternalUnpair.left tailP (ys 6) (ys 5) xx (hq 6) (hq 5)
  have hdeletion := unaryRecover InternalUnpair.right tailP (ys 7) (ys 5) xx (hq 7) (hq 5)
  have hpv := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (value.relabel j) (ys 4) (ys 5)) (andIntro hroot htail)
  have hpt := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (ys 5) (ys 6) (ys 7)) (andIntro hreturned hdeletion)
  have hf' := renameInto hf j Theta hi
  rw [UniformReturnSyntax.frameRename] at hf'
  have ha := SixSol20261112.Context.AppendIdentityProof.actualRightZero body beta Theta (produced.relabel j)
  have hrun := UniformReturnSyntax.frameApply R (frame.relabel j) (produced.relabel j) (value.relabel j)
    z z (ys 0) (produced.relabel j) (ys 1) (ys 2) (ys 3) hf'
    (andIntro hw (andIntro ha (andIntro hin (andIntro hs ho))))
  exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)
    hi hw hin ho hs hpv hpt hrun
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReturnTickQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReturnTickQueries
