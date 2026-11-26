module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem leafCases (tag : Nat) (input : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral tag) input)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (typ raw field : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (input.relabel j) typ raw)) →
   Nonempty (Derivation body Theta
     (graph1 (pairOf (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)) raw field)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qs : Fin 3 → Program 1 := ![leftOf (.projection 0),rightOf (.projection 0),rightOf (rightOf (.projection 0))]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (![input]) psi
 intro beta j ys Theta hj hq
 let xs : Fin 1 → OTerm beta := ![input.relabel j]
 have hx : (fun a : Fin 1 => (![input] a).relabel j) = xs := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (input.relabel j) xs (hq 0) (projectionValue 0 xs)
 have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (input.relabel j) xs (hq 1) (projectionValue 0 xs)
 have hp := unaryRecover InternalUnpair.right (rightOf (.projection 0)) (ys 2) (ys 1) xs (hq 2) (hq 1)
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at ht'
 have htag := unaryRecover InternalUnpair.left (rightOf (.projection 0)) (numeral tag) (ys 1) xs ht' (hq 1)
 have hraw := reconstructPair (ys 1) (numeral tag) (ys 2) htag hp
 have hc := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)
   (ys 1) (numeral tag) (ys 2) (![ys 2]) hraw
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue tag (![ys 2])) (projectionValue 0 (![ys 2]))
 exact next beta j Theta (ys 0) (ys 1) (ys 2) hj (reconstructPair (input.relabel j) (ys 0) (ys 1) hl hr) hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
