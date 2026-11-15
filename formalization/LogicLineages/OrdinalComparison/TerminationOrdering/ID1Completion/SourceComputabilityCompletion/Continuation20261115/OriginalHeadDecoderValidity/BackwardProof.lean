module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.BackwardProof
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
open SupportProof

theorem orCases {P Q C : Formula alpha}
    (h : Nonempty (Derivation body Delta (P ⊔ Q)))
    (hp : Nonempty (Derivation body (P :: Delta) C))
    (hq : Nonempty (Derivation body (Q :: Delta) C)) :
    Nonempty (Derivation body Delta C) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨InternalBetaTotalityProof.disjunctionElimination h
    (Derivation.implicationIntroduction hp) (Derivation.implicationIntroduction hq)⟩

theorem basicAccept (n : Nat) (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta ((eqn tag (numeral 0) ⊔ eqn tag (numeral 1)) ⊓ eqn payload (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw)) := by
  have hb := (basicFactor raw payload (pairRight raw tag payload hp)).mpr (andRight he)
  apply orCases (andLeft he)
  · exact (tagFactor n 0 raw tag payload (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (withHyp hb _)
  · exact (tagFactor n 1 raw tag payload (numeral 1) (withHyp hp _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (withHyp hb _)

theorem backward (n : Nat) (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (ha : Nonempty (Derivation body Delta (Targets.allowed n tag payload))) :
    Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw)) := by
  apply orCases ha
  · exact basicAccept n raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hp := withHyp hp (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔
      (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))))
    have h : Nonempty (Derivation body ((eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))) :: Delta) (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔
      (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases h
    · exact (tagFactor n 2 raw tag payload (numeral 1) (withHyp hp _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (constantValue 1 ![raw])
    · have hp := withHyp hp (eqn tag (numeral 3) ⊔
        (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))
      have h : Nonempty (Derivation body ((eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))) :: (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))) :: Delta) (eqn tag (numeral 3) ⊔
        (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply orCases h
      · exact (tagFactor n 3 raw tag payload (numeral 1) (withHyp hp _)
          ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (constantValue 1 ![raw])
      · have hp := withHyp hp (eqn tag (numeral 4) ⊔
          (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))
        have h : Nonempty (Derivation body ((eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))) :: (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))) :: (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))) :: Delta) (eqn tag (numeral 4) ⊔
          (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))) :=
          ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply orCases h
        · exact (tagFactor n 4 raw tag payload (numeral 1) (withHyp hp _)
            ⟨Derivation.hypothesis List.mem_cons_self⟩).mpr (constantValue 1 ![raw])
        · have hp := withHyp hp (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))
          have h : Nonempty (Derivation body ((eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)) :: (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))) :: (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n)))) :: (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔ (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))) :: Delta) (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))) :=
            ⟨Derivation.hypothesis List.mem_cons_self⟩
          exact (tagFactor n 5 raw tag payload (numeral 1) hp (andLeft h)).mpr
            ((rankedFactor n raw payload (pairRight raw tag payload hp)).mpr (andRight h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.BackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.BackwardProof
