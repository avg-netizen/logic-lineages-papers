module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalAcceptanceBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant sameOf)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem basicFactor (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Delta (graph1 basicPayload (numeral 1) raw)) ↔
    Nonempty (Derivation body Delta (eqn payload (numeral 0))) := by
  constructor
  · intro h
    exact InternalEqualityTestProof.equalityOfAcceptance payload (numeral 0)
      (binaryRecover InternalEqualityTest.equalityTest InternalUnpair.right (constant 1 0)
        (numeral 1) payload (numeral 0) ![raw] h hp (constantValue 0 ![raw]))
  · intro h
    exact binaryValue InternalEqualityTest.equalityTest InternalUnpair.right (constant 1 0)
      (numeral 1) payload (numeral 0) ![raw]
      (InternalEqualityTestCompositionProof.equalityOfEqual payload (numeral 0) h) hp (constantValue 0 ![raw])

theorem rankedFactor (n : Nat) (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Delta (graph1 (rankedPayload n) (numeral 1) raw)) ↔
    Nonempty (Derivation body Delta (InternalLessThan.strictLess payload (numeral n))) := by
  constructor
  · intro h
    exact InternalLessThanProof.lessOfAcceptance payload (numeral n)
      (binaryRecover InternalLessThan.ltTest InternalUnpair.right (constant 1 n)
        (numeral 1) payload (numeral n) ![raw] h hp (constantValue n ![raw]))
  · intro h
    exact binaryValue InternalLessThan.ltTest InternalUnpair.right (constant 1 n)
      (numeral 1) payload (numeral n) ![raw]
      (InternalLessThanSupportProof.acceptOfLess payload (numeral n) h) hp (constantValue n ![raw])

def branchProgram (n k : Nat) : Program 1 :=
  if k = 0 then basicPayload else if k = 1 then basicPayload
  else if k = 5 then rankedPayload n else constant 1 1

theorem tagFactor (n : Nat) (k : Fin 6) (raw tag payload out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k.val)))) :
    Nonempty (Derivation body Delta (graph1 (check n) out raw)) ↔
    Nonempty (Derivation body Delta (graph1 (branchProgram n k.val) out raw)) := by
  have hpair := headTransport InternalPairing.pairing raw tag (numeral k.val) (Fin.cons payload Fin.elim0) he hp
  have ht := pairLeft raw (numeral k.val) payload hpair
  fin_cases k <;> simp [check,branchProgram,OriginalHeadClass.InternalProof.chooseFactor _ raw out ht]

theorem chooseFalse (k : Nat) (yes no : Program 1) (raw tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral k)).not))
    (h : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.choose k yes no) out raw))) :
    Nonempty (Derivation body Delta (graph1 no out raw)) := by
  have hz := sameReject InternalUnpair.left (constant 1 k) tag (numeral k) ![raw] ht
    (constantValue k ![raw]) (by simpa only [equalEqn] using hn)
  exact zeroBranchElim (sameOf InternalUnpair.left (constant 1 k)) no yes out ![raw] hz h

theorem zeroReject (raw : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (graph1 (constant 1 0) (numeral 1) raw))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := valueUnique (constant 1 0) (numeral 1) (numeral 0) ![raw] h (constantValue 0 ![raw])
  exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
