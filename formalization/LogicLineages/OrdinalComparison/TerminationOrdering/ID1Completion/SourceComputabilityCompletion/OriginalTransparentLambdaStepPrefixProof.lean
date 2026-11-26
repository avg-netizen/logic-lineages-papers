module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalControlGraphProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalHereditaryLambda
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover original parent pair from prefix constructor and actual child
selectors. Certificate payload is copied, not reconstructed semantically. -/
theorem parentPair (cert child code tail payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 prefixCertificate cert child)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail child)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload child)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing cert code payload)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
  have hcons := binaryValue InternalListCodec.consCode (InternalAcceptance.constantZero 1)
    InternalUnpair.left code z tail xs hc (constantZeroValue xs) hl
  exact binaryRecover InternalPairing.pairing
    (consOf (InternalAcceptance.constantZero 1) InternalUnpair.left) InternalUnpair.right
    cert code payload xs hp hcons hr

theorem stripPrefix (cert child code tail payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 prefixCertificate cert child)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail child)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload child)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaGuardLeaf.stripCertificate child cert)) := by
  have hpair := parentPair cert child code tail payload hp hl hr hc
  have hchild := reconstructPair child tail payload hl hr
  have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction code z tail hc))
  let xs : Fin 1 → OTerm alpha := Fin.cons cert Fin.elim0
  have htailAt := unaryValue InternalListCodec.tailCode InternalUnpair.left tail code xs htail
    (pairLeft cert code payload hpair)
  exact binaryValue InternalPairing.pairing
    (.composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left))
    InternalUnpair.right child tail payload xs hchild htailAt (pairRight cert code payload hpair)

/-- An actual cons-zero path pays both independent original path tests. -/
theorem lambdaPath (xs : Fin 4 → OTerm alpha) (code tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail))) :
    Nonempty (Derivation body Delta (programGraph lamPath (suc z) xs)) := by
  have hd := InternalListCodecSupportProof.consDestruction code z tail hc
  have hh := unaryValue InternalListCodec.headCode path z code xs (andLeft hd) hp
  have hhead := sameAccept (.composition InternalListCodec.headCode (fun _ : Fin 1 => path))
    (InternalAcceptance.constantZero 4) z xs hh (constantZeroValue xs)
  let nilAt : Program 4 := .composition InternalListCodec.nilTest (fun _ : Fin 1 => path)
  have hz := unaryValue InternalListCodec.nilTest path z code xs
    (zeroTestAtNonzero code (andRight (andRight hd))) hp
  let P := programGraph nilAt (suc z) xs
  have hn : Nonempty (Derivation body Delta P.not) := by
    have ha : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique nilAt (suc z) z xs ha
      (InternalApplicationValidityStackAppendInductionCoreProof.withHyp hz P)
    exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply he)⟩
  have hnonempty : Nonempty (Derivation body Delta (programGraph pathNonempty (suc z) xs)) := zeroBranchIntro _ _ _ (suc z) xs (normalizeReject nilAt xs hn)
    (InternalLessThanSupportProof.oneConstantValue xs)
  exact conjunctionAccept pathNonempty pathHeadLambda xs hnonempty hhead
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepPrefixProof
