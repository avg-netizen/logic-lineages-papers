module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalPathCheckerSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- A proved nonzero control selects the original other branch. -/
theorem nonzeroBranchIntro {n : Nat} (control a b : Program n)
    (out c : OTerm α) (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hn : Nonempty (Derivation body Gamma (eqn c z).not))
    (hb : Nonempty (Derivation body Gamma (programGraph b out xs))) :
    Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs)) := by
  apply programCases a xs _
  intro β j Delta value hj hv
  rw [programRename]
  have hc' := renameInto hc j Delta hj
  have hn' := renameInto hn j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [programRename] at hc' hb'
  change Nonempty (Derivation body Delta ((eqn c z).relabel j).not) at hn'
  simp only [eqnRelabel,zRelabel] at hn'
  exact branchValue control a b (out.relabel j) (c.relabel j) value (out.relabel j)
    (fun i => (xs i).relabel j) hc' hv hb'
    (conditionalAtNonzero (c.relabel j) value (out.relabel j) hn')

theorem nonzeroBranchElim {n : Nat} (control a b : Program n)
    (out c : OTerm α) (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hn : Nonempty (Derivation body Gamma (eqn c z).not))
    (hw : Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs))) :
    Nonempty (Derivation body Gamma (programGraph b out xs)) := by
  apply programCompositionCases LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs _ hw
  intro β j ys Delta hj ht hg
  rw [programRename]
  have hc' := renameInto hc j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [programRename] at hc'
  change Nonempty (Derivation body Delta ((eqn c z).relabel j).not) at hn'
  simp only [eqnRelabel,zRelabel] at hn'
  obtain ⟨he⟩ := valueUnique control (ys 0) (c.relabel j)
    (fun i => (xs i).relabel j) (hg 0) hc'
  obtain ⟨hn'⟩ := hn'
  have hnys : Derivation body Delta (eqn (ys 0) z).not :=
    Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp hn' _) (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))
  have hs := conditionalAtNonzero (ys 0) (ys 1) (ys 2) ⟨hnys⟩
  rw [threeTuple] at hs
  obtain ⟨heq⟩ := valueUnique
    LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
    (out.relabel j) (ys 2) ys ht hs
  exact outputTransport b (ys 2) (out.relabel j) (fun i => (xs i).relabel j) ⟨symm heq⟩ (hg 2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
