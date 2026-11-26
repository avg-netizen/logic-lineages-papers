module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalVariableLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Direct derivation for the actual selected branch. No native calibration,
semantic truth, decoder correctness or transport principle is used. -/
theorem successorBranchAt {body : Positive (Fin 1)} {alpha : Type}
    {Delta : List (Formula alpha)} {n : Nat} (control no yes : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control (suc z) xs))) :
    Nonempty (Derivation body Delta
      ((programGraph (InternalAcceptance.branch control no yes) out xs).iff
        (programGraph yes out xs))) := by
  let A := programGraph (InternalAcceptance.branch control no yes) out xs
  let B := programGraph yes out xs
  obtain ⟨hc⟩ := hc
  obtain ⟨hf⟩ := successorBranchElim control no yes out z xs
    ⟨InternalBetaTotalityProof.addHyp hc A⟩
    (show Nonempty (Derivation body (A :: Delta) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := successorBranchIntro control no yes out z xs
    ⟨InternalBetaTotalityProof.addHyp hc B⟩
    (show Nonempty (Derivation body (B :: Delta) B) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalVariableLeavesInternalBranches :
    OriginalVariableLeavesTargets.ActualOriginalVariableLeavesInternalBranches := by
  intro guard data body alpha Delta out raw parameter
  let C := graph2 variableTag InternalOriginalStepGuard.one raw parameter
  have hc : Nonempty (Derivation body (C :: Delta) C) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  obtain ⟨hs⟩ := successorBranchAt variableTag data.oldSource (sourceVariable data.member) out xs hc
  obtain ⟨ht⟩ := successorBranchAt variableTag data.oldTarget (targetVariable guard) out xs hc
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hs ht)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
