module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.BackwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.BackwardProof
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
open SupportProof TagProof
open OriginalHeadDecoderValidity.BackwardProof (orCases)

theorem clause0 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (eqn tagValue (numeral 0) ⊔ eqn tagValue (numeral 3)))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  apply orCases ha
  · exact (tagFactor n 0 table code tagValue payloadValue (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (constantValue 1 ![table,code])
  · exact (tagFactor n 3 table code tagValue payloadValue (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (constantValue 1 ![table,code])

theorem clause1 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (eqn tagValue (numeral 1) ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  exact (tagFactor n 1 table code tagValue payloadValue (numeral 1) hp (andLeft ha)).mpr
    ((childFactor firstField table code first hf).mpr (andRight ha))

theorem clause2 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta ((eqn tagValue (numeral 2) ⊔ eqn tagValue (numeral 7)) ⊓ (graph2 InternalRawListRecursion.lookup (numeral 1) first table ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) second table)))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  have hb := (bothFactor table code first second hf hs).mpr (andRight ha)
  apply orCases (andLeft ha)
  · exact (tagFactor n 2 table code tagValue payloadValue (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (withHyp hb _)
  · exact (tagFactor n 7 table code tagValue payloadValue (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (withHyp hb _)

theorem clause3 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (eqn tagValue (numeral 4) ⊓ (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table)))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  exact (tagFactor n 4 table code tagValue payloadValue (numeral 1) hp (andLeft ha)).mpr
    ((ordinaryFactor n table code first head hf hh).mpr (andRight ha))

theorem clause4 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (eqn tagValue (numeral 5) ⊓ ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table) ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) second table)))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  exact (tagFactor n 5 table code tagValue payloadValue (numeral 1) hp (andLeft ha)).mpr
    ((numberedFactor n table code first second head hf hs hh).mpr (andRight ha))

theorem clause5 (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (eqn tagValue (numeral 6) ⊓ eqn payloadValue (numeral 0)))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  exact (tagFactor n 6 table code tagValue payloadValue (numeral 1) hp (andLeft ha)).mpr
    ((nilFactor table code tagValue payloadValue hp).mpr (andRight ha))

theorem backward (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (ha : Nonempty (Derivation body Delta (Targets.allowed n table tagValue payloadValue first second head))) :
    Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)) := by
  let C0 : Formula alpha := (eqn tagValue (numeral 0) ⊔ eqn tagValue (numeral 3))
  let C1 : Formula alpha := (eqn tagValue (numeral 1) ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table)
  let C2 : Formula alpha := ((eqn tagValue (numeral 2) ⊔ eqn tagValue (numeral 7)) ⊓ (graph2 InternalRawListRecursion.lookup (numeral 1) first table ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) second table))
  let C3 : Formula alpha := (eqn tagValue (numeral 4) ⊓ (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table))
  let C4 : Formula alpha := (eqn tagValue (numeral 5) ⊓ ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table) ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) second table))
  let C5 : Formula alpha := (eqn tagValue (numeral 6) ⊓ eqn payloadValue (numeral 0))
  let R5 : Formula alpha := C5
  let R4 : Formula alpha := C4 ⊔ R5
  let R3 : Formula alpha := C3 ⊔ R4
  let R2 : Formula alpha := C2 ⊔ R3
  let R1 : Formula alpha := C1 ⊔ R2
  let R0 : Formula alpha := C0 ⊔ R1
  change Nonempty (Derivation body Delta R0) at ha
  apply orCases ha
  · exact clause0 n table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hp := withHyp hp R1
    have hf := withHyp hf R1
    have hs := withHyp hs R1
    have hh := withHyp hh R1
    have hr : Nonempty (Derivation body (R1 :: Delta) R1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases hr
    · exact clause1 n table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    · have hp := withHyp hp R2
      have hf := withHyp hf R2
      have hs := withHyp hs R2
      have hh := withHyp hh R2
      have hr : Nonempty (Derivation body (R2 :: R1 :: Delta) R2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases hr
      · exact clause2 n table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
          ⟨Derivation.hypothesis List.mem_cons_self⟩
      · have hp := withHyp hp R3
        have hf := withHyp hf R3
        have hs := withHyp hs R3
        have hh := withHyp hh R3
        have hr : Nonempty (Derivation body (R3 :: R2 :: R1 :: Delta) R3) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply orCases hr
        · exact clause3 n table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
            ⟨Derivation.hypothesis List.mem_cons_self⟩
        · have hp := withHyp hp R4
          have hf := withHyp hf R4
          have hs := withHyp hs R4
          have hh := withHyp hh R4
          have hr : Nonempty (Derivation body (R4 :: R3 :: R2 :: R1 :: Delta) R4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          apply orCases hr
          · exact clause4 n table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
              ⟨Derivation.hypothesis List.mem_cons_self⟩
          · have hp := withHyp hp R5
            have hf := withHyp hf R5
            have hs := withHyp hs R5
            have hh := withHyp hh R5
            have hr : Nonempty (Derivation body (R5 :: R4 :: R3 :: R2 :: R1 :: Delta) R5) := ⟨Derivation.hypothesis List.mem_cons_self⟩
            exact clause5 n table code tagValue payloadValue first second head hp hf hs hh hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.BackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.BackwardProof
