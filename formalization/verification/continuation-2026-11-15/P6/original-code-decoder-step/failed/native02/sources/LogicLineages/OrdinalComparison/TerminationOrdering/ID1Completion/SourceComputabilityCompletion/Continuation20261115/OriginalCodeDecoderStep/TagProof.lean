module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.TagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant sameOf)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject branchNumeralIntro branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilFactor (table code tagValue payloadValue : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue))) :
    Nonempty (Derivation body Delta (graph2 (sameOf payload (constant 2 0)) (numeral 1) table code)) ↔
    Nonempty (Derivation body Delta (eqn payloadValue (numeral 0))) := by
  have hright : Nonempty (Derivation body Delta (graph2 payload payloadValue table code)) :=
    unaryValue InternalUnpair.right raw payloadValue code ![table,code]
      (pairRight code tagValue payloadValue hp) (projectionValue 1 ![table,code])
  constructor
  · intro h
    exact InternalEqualityTestProof.equalityOfAcceptance payloadValue (numeral 0)
      (binaryRecover InternalEqualityTest.equalityTest payload (constant 2 0)
        (numeral 1) payloadValue (numeral 0) ![table,code] h hright (constantValue 0 ![table,code]))
  · intro h
    exact binaryValue InternalEqualityTest.equalityTest payload (constant 2 0)
      (numeral 1) payloadValue (numeral 0) ![table,code]
      (InternalEqualityTestCompositionProof.equalityOfEqual payloadValue (numeral 0) h) hright (constantValue 0 ![table,code])

def branchProgram (n k : Nat) : Program 2 :=
  if k = 0 then constant 2 1 else if k = 1 then firstAccepted
  else if k = 2 then bothChildren else if k = 3 then constant 2 1
  else if k = 4 then ordinary n else if k = 5 then numbered n
  else if k = 6 then sameOf payload (constant 2 0) else bothChildren

theorem chooseFactor (actual k : Nat) (yes no : Program 2) (table code out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 tag (numeral actual) table code))) :
    Nonempty (Derivation body Delta (graph2 (choose k yes no) out table code)) ↔
    Nonempty (Derivation body Delta (graph2 (if actual = k then yes else no) out table code)) :=
  ⟨branchNumeralElim actual k tag no yes out ![table,code] ht,
    branchNumeralIntro actual k tag no yes out ![table,code] ht⟩

theorem tagFactor (n : Nat) (k : Fin 8) (table code tagValue payloadValue out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (he : Nonempty (Derivation body Delta (eqn tagValue (numeral k.val)))) :
    Nonempty (Derivation body Delta (graph2 (step n) out table code)) ↔
    Nonempty (Derivation body Delta (graph2 (branchProgram n k.val) out table code)) := by
  have hpair := headTransport InternalPairing.pairing code tagValue (numeral k.val) (Fin.cons payloadValue Fin.elim0) he hp
  have ht : Nonempty (Derivation body Delta (graph2 tag (numeral k.val) table code)) :=
    unaryValue InternalUnpair.left raw (numeral k.val) code ![table,code]
      (pairLeft code (numeral k.val) payloadValue hpair) (projectionValue 1 ![table,code])
  fin_cases k <;> simp [step,branchProgram,chooseFactor _ _ _ _ table code out ht]

theorem chooseFalse (k : Nat) (yes no : Program 2) (table code tagValue out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 tag tagValue table code)))
    (hn : Nonempty (Derivation body Delta (eqn tagValue (numeral k)).not))
    (h : Nonempty (Derivation body Delta (graph2 (choose k yes no) out table code))) :
    Nonempty (Derivation body Delta (graph2 no out table code)) := by
  have hz := sameReject tag (constant 2 k) tagValue (numeral k) ![table,code] ht
    (constantValue k ![table,code]) (by simpa only [equalEqn] using hn)
  exact zeroBranchElim (sameOf tag (constant 2 k)) no yes out ![table,code] hz h

theorem zeroReject (table code : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (graph2 (constant 2 0) (numeral 1) table code))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := valueUnique (constant 2 0) (numeral 1) (numeral 0) ![table,code] h (constantValue 0 ![table,code])
  exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.TagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.TagProof
