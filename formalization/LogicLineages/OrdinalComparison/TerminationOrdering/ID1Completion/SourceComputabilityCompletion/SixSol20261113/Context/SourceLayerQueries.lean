module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sourceCases (H G : Program 1) (M W : Program 2) (packed parameter : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ raw c gamma rawJob typed job B weight : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (packed.relabel j) typ raw)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) c gamma)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing rawJob raw (parameter.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typed typ rawJob)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing job (numeral 0) typed)) →
      Nonempty (Derivation body Theta (graph1 OriginalHereditaryFuelProgram.weight weight job)) →
      Nonempty (Derivation body Theta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)) →
      Nonempty (Derivation body Theta (OriginalInternalJobAdmissible.Admissible H M W (numeral 0) typ raw gamma c)) →
      Nonempty (Derivation body Theta (OriginalHereditaryInternalAgenda.Job H M W c B job)) →
      Nonempty (Derivation body Theta (graph2 OriginalHereditaryEvaluatorDefinitions.job job (packed.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
 let typP : Program 2 := leftOf (.projection 0)
 let rawP : Program 2 := rightOf (.projection 0)
 let cP : Program 2 := leftOf (.projection 1)
 let gammaP : Program 2 := rightOf (.projection 1)
 let rawJobP : Program 2 := pairOf rawP (.projection 1)
 let typedP : Program 2 := pairOf typP rawJobP
 let jobP : Program 2 := OriginalHereditaryEvaluatorDefinitions.job
 let branchP : Program 2 := .composition OriginalHereditaryFuelProgram.branching (fun _ : Fin 1 => jobP)
 let weightP : Program 2 := .composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => jobP)
 let zeroP : Program 2 := OriginalRawSyntaxTransport.constant 2 0
 let qs : Fin 9 → Program 2 := ![typP,rawP,cP,gammaP,rawJobP,typedP,jobP,branchP,weightP]
 let xs : Fin 2 → OTerm alpha := ![packed,parameter]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hinc hg
 let xx : Fin 2 → OTerm beta := ![packed.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 have hs' := renameInto hs j Theta hinc
 simp only [graph2Rename,numeralRename] at hs'
 have htyp := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (packed.relabel j) xx (hg 0) (projectionValue 0 xx)
 have hraw := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (packed.relabel j) xx (hg 1) (projectionValue 0 xx)
 have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 2) (parameter.relabel j) xx (hg 2) (projectionValue 1 xx)
 have hgamma := unaryRecover InternalUnpair.right (.projection 1) (ys 3) (parameter.relabel j) xx (hg 3) (projectionValue 1 xx)
 have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) htyp hraw
 have hparameter := reconstructPair (parameter.relabel j) (ys 2) (ys 3) hc hgamma
 have hrawJob := binaryRecover InternalPairing.pairing rawP (.projection 1) (ys 4) (ys 1) (parameter.relabel j)
   xx (hg 4) (hg 1) (projectionValue 1 xx)
 have htyped := binaryRecover InternalPairing.pairing typP rawJobP (ys 5) (ys 0) (ys 4) xx (hg 5) (hg 0) (hg 4)
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hjob := binaryRecover InternalPairing.pairing zeroP typedP (ys 6) (numeral 0) (ys 5) xx (hg 6) hz (hg 5)
 have hbranch := unaryRecover OriginalHereditaryFuelProgram.branching jobP (ys 7) (ys 6) xx (hg 7) (hg 6)
 have hweight := unaryRecover OriginalHereditaryFuelProgram.weight jobP (ys 8) (ys 6) xx (hg 8) (hg 6)
 have hadm := OriginalHereditaryInitialBranchProof.actualJob body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 3) (ys 2) (ys 4) (ys 5) (ys 6) (ys 8) (ys 7)
   hp hparameter hrawJob htyped hjob hs' hweight hbranch
 have hinit := OriginalInternalJobAdmissibleInitializationProof.initialization body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 3) (ys 2) (ys 4) (ys 5) (ys 6)
   hp hparameter hrawJob htyped hjob hs'
 have haccepted := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim H G M W
   (packed.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hp hparameter hs'
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8)
   hinc hp hparameter hrawJob htyped hjob hweight (andRight haccepted) (andRight (andRight hinit)) (andRight hadm) (andLeft hadm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerQueries
