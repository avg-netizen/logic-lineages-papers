module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryLambda
open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalControlGraphProof
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Nil cannot satisfy the explicit nonempty branch, even though its total
head selector also returns zero. This is an original-calculus contradiction. -/
theorem acceptedPathNonzero (xs : Fin 4 → OTerm alpha) (p : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path p xs)))
    (ha : Nonempty (Derivation body Delta (programGraph pathNonempty (suc z) xs))) :
    Nonempty (Derivation body Delta (eqn p z).not) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨ha⟩ := ha
  let P := eqn p z
  have hn : Nonempty (Derivation body (P :: Delta)
      (programGraph (.composition InternalListCodec.nilTest (fun _ : Fin 1 => path)) (suc z) xs)) :=
    unaryValue InternalListCodec.nilTest path (suc z) p xs
      (zeroTestAtZero p ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp hp P⟩
  have hz := successorBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      (.composition InternalListCodec.nilTest (fun _ : Fin 1 => path)))
    (InternalLessThan.constantOne 4) (InternalAcceptance.constantZero 4) (suc z) z xs
    (normalizeAccept (.composition InternalListCodec.nilTest (fun _ : Fin 1 => path)) xs hn)
    ⟨addHyp ha P⟩
  obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 4) (suc z) z xs hz
    (constantZeroValue xs)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

/-- The equality checker pays the original head-zero equation, rather than
assuming a decoded lambda-position constructor. -/
theorem acceptedPathHeadZero (xs : Fin 4 → OTerm alpha) (p h : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path p xs)))
    (hh : Nonempty (Derivation body Delta
      (programGraph (.composition InternalListCodec.headCode (fun _ : Fin 1 => path)) h xs)))
    (ha : Nonempty (Derivation body Delta (programGraph pathHeadLambda (suc z) xs))) :
    Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode z p)) := by
  have heq := binaryRecover InternalEqualityTest.equalityTest
    (.composition InternalListCodec.headCode (fun _ : Fin 1 => path))
    (InternalAcceptance.constantZero 4) (suc z) h z xs ha hh (constantZeroValue xs)
  have he := InternalEqualityTestProof.equalityOfAcceptance h z heq
  exact outputTransport InternalListCodec.headCode h z (Fin.cons p Fin.elim0) he
    (unaryRecover InternalListCodec.headCode path h p xs hh hp)

/-- Stripping retains the exact payload, which contains both replacement and
root certificate. Neither coordinate is reconstructed from native data. -/
theorem stripAtFields (certificate child p payload tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate p payload)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail p)))
    (hs : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaGuardLeaf.stripCertificate child certificate))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child tail payload)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons certificate Fin.elim0
  exact binaryRecover InternalPairing.pairing
    (.composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left))
    InternalUnpair.right child tail payload xs hs
    (unaryValue InternalListCodec.tailCode InternalUnpair.left tail p xs ht
      (pairLeft certificate p payload hc))
    (pairRight certificate p payload hc)

/-- Prefixing the actual child pair with the recovered original head restores
exactly the original certificate, including its unchanged payload. -/
theorem prefixAtFields (certificate child p payload tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate p payload)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child tail payload)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode p z tail))) :
    Nonempty (Derivation body Delta (graph1 prefixCertificate certificate child)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
  exact binaryValue InternalPairing.pairing
    (consOf (InternalAcceptance.constantZero 1) InternalUnpair.left) InternalUnpair.right
    certificate p payload xs hc
    (binaryValue InternalListCodec.consCode (InternalAcceptance.constantZero 1) InternalUnpair.left
      p z tail xs hp (constantZeroValue xs) (pairLeft child tail payload hs))
    (pairRight child tail payload hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
