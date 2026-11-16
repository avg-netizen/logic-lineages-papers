module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSyntaxProof (suc)
theorem forward (n : Nat) (labels heads types tupleBound prior code range tuples k encoded raw t base tuple extra len : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc labels))))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples tupleBound types)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len tuple)))
    (hf : Nonempty (Derivation body Delta (OriginalEncodedNumberedEnumerationBranch.Targets.fields n range heads types prior tuples prior code k encoded raw t base tuple extra))) :
    Nonempty (Derivation body Delta (NumberedSyntaxProof.fields n labels heads types tupleBound prior code k encoded raw t base tuple extra len)) := by
  have h0 := (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))
  have h1 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))
  have h2 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))
  have h3 := (andRight (andLeft (andLeft (andLeft (andLeft hf)))))
  have h4 := (andRight (andLeft (andLeft (andLeft hf))))
  have h5 := (andRight (andLeft (andLeft hf)))
  have h6 := (andRight (andLeft hf))
  have h7 := (andRight hf)
  have hb := (OriginalAscendingRange.StatementChecks.exactMembership body alpha Delta (suc labels) range k hr).mp h0
  have htuple := (OriginalTypeListsMembership.StatementChecks.exactMembership body alpha Delta tupleBound types tuples tuple len ht hl).mp h4
  exact (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro hb h1) h6) h2) h3) hl) (andLeft htuple)) (andRight htuple)) h5) h7)

theorem backward (n : Nat) (labels heads types tupleBound prior code range tuples k encoded raw t base tuple extra len : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc labels))))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples tupleBound types)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len tuple)))
    (hf : Nonempty (Derivation body Delta (NumberedSyntaxProof.fields n labels heads types tupleBound prior code k encoded raw t base tuple extra len))) :
    Nonempty (Derivation body Delta (OriginalEncodedNumberedEnumerationBranch.Targets.fields n range heads types prior tuples prior code k encoded raw t base tuple extra)) := by
  have h0 := (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))))
  have h1 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))))
  have h2 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))))
  have h3 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))
  have h4 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))
  have h5 := (andRight (andLeft (andLeft (andLeft (andLeft hf)))))
  have h6 := (andRight (andLeft (andLeft (andLeft hf))))
  have h7 := (andRight (andLeft (andLeft hf)))
  have h8 := (andRight (andLeft hf))
  have h9 := (andRight hf)
  have hb := (OriginalAscendingRange.StatementChecks.exactMembership body alpha Delta (suc labels) range k hr).mpr h0
  have htuple := (OriginalTypeListsMembership.StatementChecks.exactMembership body alpha Delta tupleBound types tuples tuple len ht hl).mpr (andIntro h6 h7)
  exact (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro hb h1) h3) h4) htuple) h8) h2) h9)

theorem encodedCases (n : Nat) (labels heads types prior tuples code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (InternalFiniteBlocks.block
      (OriginalEncodedNumberedEnumerationBranch.Targets.witnessMatrix n labels heads types prior tuples prior code))))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 7 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (OriginalEncodedNumberedEnumerationBranch.Targets.fields n
        (labels.relabel j) (heads.relabel j) (types.relabel j) (prior.relabel j) (tuples.relabel j) (prior.relabel j) (code.relabel j)
        (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 7 Delta
    (OriginalEncodedNumberedEnumerationBranch.Targets.witnessMatrix n labels heads types prior tuples prior code) psi hf
  let j : alpha → alpha ⊕ Fin 7 := Sum.inl
  let Theta := OriginalEncodedNumberedEnumerationBranch.Targets.witnessMatrix n labels heads types prior tuples prior code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 7) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
