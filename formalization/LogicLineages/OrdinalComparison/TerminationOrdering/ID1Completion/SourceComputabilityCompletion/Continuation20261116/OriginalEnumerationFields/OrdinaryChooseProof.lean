module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryChooseProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem mappedAt (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param mapped : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hm : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3)))) :
    Nonempty (Derivation body Delta (graph3 (.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads]) mapped key answers param)) :=
  LayerGuardProof.unaryVectorValue _ heads mapped (xs 3) ![key,answers,param] hm (HeadInputProof.headsAt xs key answers param hp)

theorem memberAt (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head child mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hm : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head))) :
    Nonempty (Derivation body Delta (graph3 (headMember n (leftOf payload)) (suc z) key answers param)) := by
  have hhead := ordinaryHead raw (xs 0) head child ![key,answers,param] (rawAt xs key answers param hk) hc
  exact binaryValue contains (.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads])
    (leftOf payload) (suc z) mapped head ![key,answers,param]
    (HeadAllowedProof.introduce n (xs 3) mapped head hmap hm) (mappedAt n xs key answers param mapped hp hmap) hhead

theorem acceptedMember (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head child mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)) := by
  have hr := rawAt xs key answers param hk
  have ht := ordinaryTag raw (xs 0) head child ![key,answers,param] hr hc
  have hh := ordinaryHead raw (xs 0) head child ![key,answers,param] hr hc
  have hb := ChooseInternalProof.tag4Elim n ![key,answers,param] (suc z) ht hv
  have hm := BothAcceptanceProof.leftOne (headMember n (leftOf payload)) firstAnswer ![key,answers,param]
    (Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.compositionRange contains _
      Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.containsRange) hb
  have hcontains := binaryRecover contains (.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads])
    (leftOf payload) (suc z) mapped head ![key,answers,param] hm (mappedAt n xs key answers param mapped hp hmap) hh
  exact HeadAllowedProof.recover n (xs 3) mapped head hmap hcontains

theorem introValue (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head child mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hm : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)))
    (hv : Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have ht := ordinaryTag raw (xs 0) head child ![key,answers,param] (rawAt xs key answers param hk) hc
  apply ChooseInternalProof.tag4Intro n ![key,answers,param] (suc z) ht
  exact successorBranchIntro (headMember n (leftOf payload)) (OriginalRawSyntaxTransport.constant 3 0)
    firstAnswer (suc z) z ![key,answers,param] (memberAt n xs key answers param head child mapped hk hp hc hmap hm) hv

theorem elimValue (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head child mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hm : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param)) := by
  have ht := ordinaryTag raw (xs 0) head child ![key,answers,param] (rawAt xs key answers param hk) hc
  have hb := ChooseInternalProof.tag4Elim n ![key,answers,param] (suc z) ht hv
  exact successorBranchElim (headMember n (leftOf payload)) (OriginalRawSyntaxTransport.constant 3 0)
    firstAnswer (suc z) z ![key,answers,param] (memberAt n xs key answers param head child mapped hk hp hc hmap hm) hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryChooseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryChooseProof
