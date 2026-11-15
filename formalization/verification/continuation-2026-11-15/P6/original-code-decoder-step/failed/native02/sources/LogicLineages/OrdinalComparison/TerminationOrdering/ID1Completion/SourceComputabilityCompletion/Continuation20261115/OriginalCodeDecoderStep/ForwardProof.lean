module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.TagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.ForwardProof
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
open InternalQuotientComparisonProof (orLeft orRight)
open SupportProof TagProof

theorem forwardAtTag (n : Nat) (k : Fin 8) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (he : Nonempty (Derivation body Delta (eqn tagValue (numeral k.val))))
    (hv : Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code))) :
    Nonempty (Derivation body Delta (Targets.allowed n table tagValue payloadValue first second head)) := by
  have hb := (tagFactor n k table code tagValue payloadValue (numeral 1) hp he).mp hv
  fin_cases k
  · obtain ⟨he⟩ := he
    exact ⟨orLeft (orLeft he)⟩
  · obtain ⟨h⟩ := (childFactor firstField table code first hf).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction he h))⟩
  · obtain ⟨h⟩ := (bothFactor table code first second hf hs).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orLeft (Derivation.conjunctionIntroduction (orLeft he) h)))⟩
  · obtain ⟨he⟩ := he
    exact ⟨orLeft (orRight he)⟩
  · obtain ⟨h⟩ := (ordinaryFactor n table code first head hf hh).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orRight (orLeft (Derivation.conjunctionIntroduction he h))))⟩
  · obtain ⟨h⟩ := (numberedFactor n table code first second head hf hs hh).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orRight (orRight (orLeft (Derivation.conjunctionIntroduction he h)))))⟩
  · obtain ⟨h⟩ := (nilFactor table code tagValue payloadValue hp).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orRight (orRight (orRight (Derivation.conjunctionIntroduction he h)))))⟩
  · obtain ⟨h⟩ := (bothFactor table code first second hf hs).mp hb
    obtain ⟨he⟩ := he
    exact ⟨orRight (orRight (orLeft (Derivation.conjunctionIntroduction (orRight he) h)))⟩

theorem unknownReject (n : Nat) (table code tagValue payloadValue : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hv : Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code)))
    (hn0 : Nonempty (Derivation body Delta (eqn tagValue (numeral 0)).not))
    (hn1 : Nonempty (Derivation body Delta (eqn tagValue (numeral 1)).not))
    (hn2 : Nonempty (Derivation body Delta (eqn tagValue (numeral 2)).not))
    (hn3 : Nonempty (Derivation body Delta (eqn tagValue (numeral 3)).not))
    (hn4 : Nonempty (Derivation body Delta (eqn tagValue (numeral 4)).not))
    (hn5 : Nonempty (Derivation body Delta (eqn tagValue (numeral 5)).not))
    (hn6 : Nonempty (Derivation body Delta (eqn tagValue (numeral 6)).not))
    (hn7 : Nonempty (Derivation body Delta (eqn tagValue (numeral 7)).not))
    : Nonempty (Derivation body Delta psi) := by
  have ht : Nonempty (Derivation body Delta (graph2 tag tagValue table code)) :=
    unaryValue InternalUnpair.left raw tagValue code ![table,code]
      (pairLeft code tagValue payloadValue hp) (projectionValue 1 ![table,code])
  have h0 := chooseFalse 0 (constant 2 1) _ table code tagValue (numeral 1) ht hn0 hv
  have h1 := chooseFalse 1 firstAccepted _ table code tagValue (numeral 1) ht hn1 h0
  have h2 := chooseFalse 2 bothChildren _ table code tagValue (numeral 1) ht hn2 h1
  have h3 := chooseFalse 3 (constant 2 1) _ table code tagValue (numeral 1) ht hn3 h2
  have h4 := chooseFalse 4 (ordinary n) _ table code tagValue (numeral 1) ht hn4 h3
  have h5 := chooseFalse 5 (numbered n) _ table code tagValue (numeral 1) ht hn5 h4
  have h6 := chooseFalse 6 (sameOf payload (constant 2 0)) _ table code tagValue (numeral 1) ht hn6 h5
  have h7 := chooseFalse 7 bothChildren _ table code tagValue (numeral 1) ht hn7 h6
  exact zeroReject table code psi h7

theorem forward (n : Nat) (table code tagValue payloadValue first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code tagValue payloadValue)))
    (hf : Nonempty (Derivation body Delta (graph2 firstField first table code)))
    (hs : Nonempty (Derivation body Delta (graph2 secondField second table code)))
    (hh : Nonempty (Derivation body Delta (graph2 headField head table code)))
    (hv : Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table code))) :
    Nonempty (Derivation body Delta (Targets.allowed n table tagValue payloadValue first second head)) := by
  apply formulaCases (eqn tagValue (numeral 0))
  · exact forwardAtTag n 0 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
  · have hp := withHyp hp (eqn tagValue (numeral 0)).not
    have hf := withHyp hf (eqn tagValue (numeral 0)).not
    have hs := withHyp hs (eqn tagValue (numeral 0)).not
    have hh := withHyp hh (eqn tagValue (numeral 0)).not
    have hv := withHyp hv (eqn tagValue (numeral 0)).not
    have hn0 : Nonempty (Derivation body ((eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply formulaCases (eqn tagValue (numeral 1))
    · exact forwardAtTag n 1 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    · have hp := withHyp hp (eqn tagValue (numeral 1)).not
      have hf := withHyp hf (eqn tagValue (numeral 1)).not
      have hs := withHyp hs (eqn tagValue (numeral 1)).not
      have hh := withHyp hh (eqn tagValue (numeral 1)).not
      have hv := withHyp hv (eqn tagValue (numeral 1)).not
      have hn0 := withHyp hn0 (eqn tagValue (numeral 1)).not
      have hn1 : Nonempty (Derivation body ((eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 1)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply formulaCases (eqn tagValue (numeral 2))
      · exact forwardAtTag n 2 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
          ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
      · have hp := withHyp hp (eqn tagValue (numeral 2)).not
        have hf := withHyp hf (eqn tagValue (numeral 2)).not
        have hs := withHyp hs (eqn tagValue (numeral 2)).not
        have hh := withHyp hh (eqn tagValue (numeral 2)).not
        have hv := withHyp hv (eqn tagValue (numeral 2)).not
        have hn0 := withHyp hn0 (eqn tagValue (numeral 2)).not
        have hn1 := withHyp hn1 (eqn tagValue (numeral 2)).not
        have hn2 : Nonempty (Derivation body ((eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 2)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply formulaCases (eqn tagValue (numeral 3))
        · exact forwardAtTag n 3 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
            ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
        · have hp := withHyp hp (eqn tagValue (numeral 3)).not
          have hf := withHyp hf (eqn tagValue (numeral 3)).not
          have hs := withHyp hs (eqn tagValue (numeral 3)).not
          have hh := withHyp hh (eqn tagValue (numeral 3)).not
          have hv := withHyp hv (eqn tagValue (numeral 3)).not
          have hn0 := withHyp hn0 (eqn tagValue (numeral 3)).not
          have hn1 := withHyp hn1 (eqn tagValue (numeral 3)).not
          have hn2 := withHyp hn2 (eqn tagValue (numeral 3)).not
          have hn3 : Nonempty (Derivation body ((eqn tagValue (numeral 3)).not :: (eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 3)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          apply formulaCases (eqn tagValue (numeral 4))
          · exact forwardAtTag n 4 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
              ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
          · have hp := withHyp hp (eqn tagValue (numeral 4)).not
            have hf := withHyp hf (eqn tagValue (numeral 4)).not
            have hs := withHyp hs (eqn tagValue (numeral 4)).not
            have hh := withHyp hh (eqn tagValue (numeral 4)).not
            have hv := withHyp hv (eqn tagValue (numeral 4)).not
            have hn0 := withHyp hn0 (eqn tagValue (numeral 4)).not
            have hn1 := withHyp hn1 (eqn tagValue (numeral 4)).not
            have hn2 := withHyp hn2 (eqn tagValue (numeral 4)).not
            have hn3 := withHyp hn3 (eqn tagValue (numeral 4)).not
            have hn4 : Nonempty (Derivation body ((eqn tagValue (numeral 4)).not :: (eqn tagValue (numeral 3)).not :: (eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 4)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
            apply formulaCases (eqn tagValue (numeral 5))
            · exact forwardAtTag n 5 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
                ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
            · have hp := withHyp hp (eqn tagValue (numeral 5)).not
              have hf := withHyp hf (eqn tagValue (numeral 5)).not
              have hs := withHyp hs (eqn tagValue (numeral 5)).not
              have hh := withHyp hh (eqn tagValue (numeral 5)).not
              have hv := withHyp hv (eqn tagValue (numeral 5)).not
              have hn0 := withHyp hn0 (eqn tagValue (numeral 5)).not
              have hn1 := withHyp hn1 (eqn tagValue (numeral 5)).not
              have hn2 := withHyp hn2 (eqn tagValue (numeral 5)).not
              have hn3 := withHyp hn3 (eqn tagValue (numeral 5)).not
              have hn4 := withHyp hn4 (eqn tagValue (numeral 5)).not
              have hn5 : Nonempty (Derivation body ((eqn tagValue (numeral 5)).not :: (eqn tagValue (numeral 4)).not :: (eqn tagValue (numeral 3)).not :: (eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 5)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
              apply formulaCases (eqn tagValue (numeral 6))
              · exact forwardAtTag n 6 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
                  ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
              · have hp := withHyp hp (eqn tagValue (numeral 6)).not
                have hf := withHyp hf (eqn tagValue (numeral 6)).not
                have hs := withHyp hs (eqn tagValue (numeral 6)).not
                have hh := withHyp hh (eqn tagValue (numeral 6)).not
                have hv := withHyp hv (eqn tagValue (numeral 6)).not
                have hn0 := withHyp hn0 (eqn tagValue (numeral 6)).not
                have hn1 := withHyp hn1 (eqn tagValue (numeral 6)).not
                have hn2 := withHyp hn2 (eqn tagValue (numeral 6)).not
                have hn3 := withHyp hn3 (eqn tagValue (numeral 6)).not
                have hn4 := withHyp hn4 (eqn tagValue (numeral 6)).not
                have hn5 := withHyp hn5 (eqn tagValue (numeral 6)).not
                have hn6 : Nonempty (Derivation body ((eqn tagValue (numeral 6)).not :: (eqn tagValue (numeral 5)).not :: (eqn tagValue (numeral 4)).not :: (eqn tagValue (numeral 3)).not :: (eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 6)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
                apply formulaCases (eqn tagValue (numeral 7))
                · exact forwardAtTag n 7 table code tagValue payloadValue first second head (withHyp hp _) (withHyp hf _) (withHyp hs _) (withHyp hh _)
                    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
                · have hp := withHyp hp (eqn tagValue (numeral 7)).not
                  have hf := withHyp hf (eqn tagValue (numeral 7)).not
                  have hs := withHyp hs (eqn tagValue (numeral 7)).not
                  have hh := withHyp hh (eqn tagValue (numeral 7)).not
                  have hv := withHyp hv (eqn tagValue (numeral 7)).not
                  have hn0 := withHyp hn0 (eqn tagValue (numeral 7)).not
                  have hn1 := withHyp hn1 (eqn tagValue (numeral 7)).not
                  have hn2 := withHyp hn2 (eqn tagValue (numeral 7)).not
                  have hn3 := withHyp hn3 (eqn tagValue (numeral 7)).not
                  have hn4 := withHyp hn4 (eqn tagValue (numeral 7)).not
                  have hn5 := withHyp hn5 (eqn tagValue (numeral 7)).not
                  have hn6 := withHyp hn6 (eqn tagValue (numeral 7)).not
                  have hn7 : Nonempty (Derivation body ((eqn tagValue (numeral 7)).not :: (eqn tagValue (numeral 6)).not :: (eqn tagValue (numeral 5)).not :: (eqn tagValue (numeral 4)).not :: (eqn tagValue (numeral 3)).not :: (eqn tagValue (numeral 2)).not :: (eqn tagValue (numeral 1)).not :: (eqn tagValue (numeral 0)).not :: Delta) (eqn tagValue (numeral 7)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
                  exact unknownReject n table code tagValue payloadValue _ hp hv hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.ForwardProof
