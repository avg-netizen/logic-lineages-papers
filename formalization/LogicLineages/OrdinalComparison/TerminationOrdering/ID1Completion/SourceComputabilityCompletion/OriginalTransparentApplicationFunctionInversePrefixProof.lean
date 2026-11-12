module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInversePrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeel
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalBetaTotalityProof (addHyp)
open OriginalTransparentApplicationFunctionInverseSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pathNonzero (state path : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 rawPath path state)))
 (ha : Nonempty (Derivation body Delta (graph1 nonemptyPath (suc z) state))) :
 Nonempty (Derivation body Delta (eqn path z).not) := by
 let P := eqn path z
 obtain ⟨hp⟩ := hp
 obtain ⟨ha⟩ := ha
 have hz : Nonempty (Derivation body (P :: Delta) (graph1 rawPath z state)) :=
   outputTransport rawPath path z (Fin.cons state Fin.elim0)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hp P⟩
 have hbad := zeroBranchElim rawPath (InternalAcceptance.constantZero 1) (InternalLessThan.constantOne 1)
   (suc z) (Fin.cons state Fin.elim0) hz ⟨addHyp ha P⟩
 obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 1) (suc z) z (Fin.cons state Fin.elim0)
   hbad (InternalAcceptanceConjunctionProof.constantZeroValue _)
 exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem recoverPrefix (state cert childCert : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph1 structuralGuard (suc z) state)))
 (hk : Nonempty (Derivation body Delta (graph1 step cert state)))
 (hc : Nonempty (Derivation body Delta (graph1 peeledStep childCert state))) :
 Nonempty (Derivation body Delta (graph1 stepLift cert childCert)) := by
 let qs : Fin 3 → Program 1 := ![rawPath,rightOf step,pathTail]
 apply queryCases qs (Fin.cons state Fin.elim0) _
 intro beta j ys Theta hj hq
 rw [graph1Rename]
 simp only [consTermRename,emptyRename] at hq
 have hs' := renameInto hs j Theta hj
 have hk' := renameInto hk j Theta hj
 have hc' := renameInto hc j Theta hj
 simp only [graph1Rename,sucRelabel,zRelabel] at hs' hk' hc'
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
 have hp := guardParts (state.relabel j) hs'
 have hn := pathNonzero (state.relabel j) (ys 0) (hq 0) (andLeft hp)
 have hh := sameLeft pathHead (two 1) positionTerm xs (andLeft (andRight hp)) (twoValue xs)
 have hhead := unaryRecover InternalListCodec.headCode rawPath positionTerm (ys 0) xs hh (hq 0)
 have htail := unaryRecover InternalListCodec.tailCode rawPath (ys 2) (ys 0) xs (hq 2) (hq 0)
 have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero (ys 0) positionTerm (ys 2) hn hhead htail
 have hleft := unaryRecover InternalUnpair.left step (ys 0) (cert.relabel j) xs (hq 0) hk'
 have hright := unaryRecover InternalUnpair.right step (ys 1) (cert.relabel j) xs (hq 1) hk'
 have hcert := reconstructPair (cert.relabel j) (ys 0) (ys 1) hleft hright
 have hchild := binaryRecover InternalPairing.pairing pathTail (rightOf step)
   (childCert.relabel j) (ys 2) (ys 1) xs hc' (hq 2) (hq 1)
 exact stepBackward (childCert.relabel j) (ys 2) (ys 1) (ys 0) (cert.relabel j) hchild hcons hcert
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInversePrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInversePrefixProof
