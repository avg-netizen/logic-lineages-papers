module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.ForwardProof
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
open InternalQuotientComparisonProof (orLeft orRight)
open SupportProof

theorem forwardAtTag (n : Nat) (k : Fin 6) (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k.val))))
    (hv : Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw))) :
    Nonempty (Derivation body Delta (Targets.allowed n tag payload)) := by
  have hbranch := (tagFactor n k raw tag payload (numeral 1) hp he).mp hv
  have hright := pairRight raw tag payload hp
  fin_cases k
  · have hb := (basicFactor raw payload hright).mp hbranch
    obtain ⟨he⟩ := he
    obtain ⟨hb⟩ := hb
    exact ⟨orLeft (Derivation.conjunctionIntroduction (orLeft he) hb)⟩
  · have hb := (basicFactor raw payload hright).mp hbranch
    obtain ⟨he⟩ := he
    obtain ⟨hb⟩ := hb
    exact ⟨orLeft (Derivation.conjunctionIntroduction (orRight he) hb)⟩
  · obtain ⟨he⟩ := he
    exact ⟨orRight (orLeft he)⟩
  · obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orLeft he))⟩
  · obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orRight (orLeft he)))⟩
  · have hb := (rankedFactor n raw payload hright).mp hbranch
    obtain ⟨he⟩ := he
    obtain ⟨hb⟩ := hb
    exact ⟨orRight (orRight (orRight (orRight (Derivation.conjunctionIntroduction he hb))))⟩

theorem unknownReject (n : Nat) (raw tag payload : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hv : Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw)))
    (hn0 : Nonempty (Derivation body Delta (eqn tag (numeral 0)).not))
    (hn1 : Nonempty (Derivation body Delta (eqn tag (numeral 1)).not))
    (hn2 : Nonempty (Derivation body Delta (eqn tag (numeral 2)).not))
    (hn3 : Nonempty (Derivation body Delta (eqn tag (numeral 3)).not))
    (hn4 : Nonempty (Derivation body Delta (eqn tag (numeral 4)).not))
    (hn5 : Nonempty (Derivation body Delta (eqn tag (numeral 5)).not))
    : Nonempty (Derivation body Delta psi) := by
  have ht := pairLeft raw tag payload hp
  have h0 := chooseFalse 0 basicPayload _ raw tag (numeral 1) ht hn0 hv
  have h1 := chooseFalse 1 basicPayload _ raw tag (numeral 1) ht hn1 h0
  have h2 := chooseFalse 2 (constant 1 1) _ raw tag (numeral 1) ht hn2 h1
  have h3 := chooseFalse 3 (constant 1 1) _ raw tag (numeral 1) ht hn3 h2
  have h4 := chooseFalse 4 (constant 1 1) _ raw tag (numeral 1) ht hn4 h3
  have h5 := chooseFalse 5 (rankedPayload n) _ raw tag (numeral 1) ht hn5 h4
  exact zeroReject raw psi h5

theorem forward (n : Nat) (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hv : Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw))) :
    Nonempty (Derivation body Delta (Targets.allowed n tag payload)) := by
  apply formulaCases (eqn tag (numeral 0))
  · exact forwardAtTag n 0 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
  · have hp := withHyp hp (eqn tag (numeral 0)).not
    have hv := withHyp hv (eqn tag (numeral 0)).not
    have hn0 : Nonempty (Derivation body ((eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply formulaCases (eqn tag (numeral 1))
    · exact forwardAtTag n 1 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    · have hp := withHyp hp (eqn tag (numeral 1)).not
      have hv := withHyp hv (eqn tag (numeral 1)).not
      have hn0 := withHyp hn0 (eqn tag (numeral 1)).not
      have hn1 : Nonempty (Derivation body ((eqn tag (numeral 1)).not :: (eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 1)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply formulaCases (eqn tag (numeral 2))
      · exact forwardAtTag n 2 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
      · have hp := withHyp hp (eqn tag (numeral 2)).not
        have hv := withHyp hv (eqn tag (numeral 2)).not
        have hn0 := withHyp hn0 (eqn tag (numeral 2)).not
        have hn1 := withHyp hn1 (eqn tag (numeral 2)).not
        have hn2 : Nonempty (Derivation body ((eqn tag (numeral 2)).not :: (eqn tag (numeral 1)).not :: (eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 2)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply formulaCases (eqn tag (numeral 3))
        · exact forwardAtTag n 3 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
        · have hp := withHyp hp (eqn tag (numeral 3)).not
          have hv := withHyp hv (eqn tag (numeral 3)).not
          have hn0 := withHyp hn0 (eqn tag (numeral 3)).not
          have hn1 := withHyp hn1 (eqn tag (numeral 3)).not
          have hn2 := withHyp hn2 (eqn tag (numeral 3)).not
          have hn3 : Nonempty (Derivation body ((eqn tag (numeral 3)).not :: (eqn tag (numeral 2)).not :: (eqn tag (numeral 1)).not :: (eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 3)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          apply formulaCases (eqn tag (numeral 4))
          · exact forwardAtTag n 4 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
          · have hp := withHyp hp (eqn tag (numeral 4)).not
            have hv := withHyp hv (eqn tag (numeral 4)).not
            have hn0 := withHyp hn0 (eqn tag (numeral 4)).not
            have hn1 := withHyp hn1 (eqn tag (numeral 4)).not
            have hn2 := withHyp hn2 (eqn tag (numeral 4)).not
            have hn3 := withHyp hn3 (eqn tag (numeral 4)).not
            have hn4 : Nonempty (Derivation body ((eqn tag (numeral 4)).not :: (eqn tag (numeral 3)).not :: (eqn tag (numeral 2)).not :: (eqn tag (numeral 1)).not :: (eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 4)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
            apply formulaCases (eqn tag (numeral 5))
            · exact forwardAtTag n 5 raw tag payload (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
            · have hp := withHyp hp (eqn tag (numeral 5)).not
              have hv := withHyp hv (eqn tag (numeral 5)).not
              have hn0 := withHyp hn0 (eqn tag (numeral 5)).not
              have hn1 := withHyp hn1 (eqn tag (numeral 5)).not
              have hn2 := withHyp hn2 (eqn tag (numeral 5)).not
              have hn3 := withHyp hn3 (eqn tag (numeral 5)).not
              have hn4 := withHyp hn4 (eqn tag (numeral 5)).not
              have hn5 : Nonempty (Derivation body ((eqn tag (numeral 5)).not :: (eqn tag (numeral 4)).not :: (eqn tag (numeral 3)).not :: (eqn tag (numeral 2)).not :: (eqn tag (numeral 1)).not :: (eqn tag (numeral 0)).not :: Delta) (eqn tag (numeral 5)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
              exact unknownReject n raw tag payload _ hp hv hn0 hn1 hn2 hn3 hn4 hn5

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.ForwardProof
