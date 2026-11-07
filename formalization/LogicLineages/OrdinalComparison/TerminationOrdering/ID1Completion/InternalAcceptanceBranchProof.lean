module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalAcceptance InternalAcceptanceSupportProof InternalControlGraphSupportProof InternalControlGraphProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem branchValue {n : Nat} (control a b : Program n) (out c av bv : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (ha : Nonempty (Derivation body Gamma (programGraph a av xs)))
    (hb : Nonempty (Derivation body Gamma (programGraph b bv xs)))
    (ht : Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional out
      (Fin.cons c (Fin.cons av (Fin.cons bv Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs)) := by
  apply compositionValue GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs
    (Fin.cons c (Fin.cons av (Fin.cons bv Fin.elim0))) ht
  intro i
  exact Fin.cases hc (Fin.cases ha (Fin.cases hb (fun j => Fin.elim0 j))) i

theorem zeroBranchIntro {n : Nat} (control a b : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control z xs)))
    (ha : Nonempty (Derivation body Gamma (programGraph a out xs))) :
    Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs)) := by
  apply programCases b xs _
  intro β j Delta v hj hv
  simp only [programRename]
  have hc' := renameInto hc j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [programRename,zRelabel] at hc' ha'
  exact branchValue control a b (out.relabel j) z (out.relabel j) v
    (fun i => (xs i).relabel j) hc' ha' hv
    (conditionalAtZero z (out.relabel j) v ⟨refl z⟩)

theorem zeroBranchElim {n : Nat} (control a b : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control z xs)))
    (hw : Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs))) :
    Nonempty (Derivation body Gamma (programGraph a out xs)) := by
  apply programCompositionCases GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs _ hw
  intro β j ys Delta hj ht hg
  simp only [programRename]
  have hc' := renameInto hc j Delta hj
  simp only [programRename,zRelabel] at hc'
  have he := valueUnique control (ys 0) z (fun i => (xs i).relabel j) (hg 0) hc'
  have hs := conditionalAtZero (ys 0) (ys 1) (ys 2) he
  rw [threeTuple] at hs
  obtain ⟨heq⟩ := valueUnique GorbowPRInternalControl.conditional (out.relabel j) (ys 1) ys ht hs
  exact outputTransport a (ys 1) (out.relabel j) (fun i => (xs i).relabel j) ⟨symm heq⟩ (hg 1)

theorem successorBranchIntro {n : Nat} (control a b : Program n) (out k : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control (suc k) xs)))
    (hb : Nonempty (Derivation body Gamma (programGraph b out xs))) :
    Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs)) := by
  apply programCases a xs _
  intro β j Delta v hj hv
  simp only [programRename]
  have hc' := renameInto hc j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [programRename,sucRelabel] at hc' hb'
  exact branchValue control a b (out.relabel j) (suc (k.relabel j)) v (out.relabel j)
    (fun i => (xs i).relabel j) hc' hv hb'
    (conditionalAtNonzero (suc (k.relabel j)) v (out.relabel j) ⟨sucNeZero _⟩)

theorem successorBranchElim {n : Nat} (control a b : Program n) (out k : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control (suc k) xs)))
    (hw : Nonempty (Derivation body Gamma (programGraph (branch control a b) out xs))) :
    Nonempty (Derivation body Gamma (programGraph b out xs)) := by
  apply programCompositionCases GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs _ hw
  intro β j ys Delta hj ht hg
  simp only [programRename]
  have hc' := renameInto hc j Delta hj
  simp only [programRename,sucRelabel] at hc'
  obtain ⟨he⟩ := valueUnique control (ys 0) (suc (k.relabel j))
    (fun i => (xs i).relabel j) (hg 0) hc'
  have hn : Nonempty (Derivation body Delta (eqn (ys 0) z).not) := by
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply
      (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))⟩
  have hs := conditionalAtNonzero (ys 0) (ys 1) (ys 2) hn
  rw [threeTuple] at hs
  obtain ⟨heq⟩ := valueUnique GorbowPRInternalControl.conditional (out.relabel j) (ys 2) ys ht hs
  exact outputTransport b (ys 2) (out.relabel j) (fun i => (xs i).relabel j) ⟨symm heq⟩ (hg 2)

theorem actualOriginalZeroBranch : InternalAcceptanceTargets.ActualOriginalZeroBranch := by
  intro body n control a b α out xs
  let c := programGraph control z xs
  let g := programGraph (branch control a b) out xs
  let s := programGraph a out xs
  obtain ⟨hf⟩ := zeroBranchElim (body := body) (Gamma := [g,c]) control a b out xs
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := zeroBranchIntro (body := body) (Gamma := [s,c]) control a b out xs
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalSuccessorBranch : InternalAcceptanceTargets.ActualOriginalSuccessorBranch := by
  intro body n control a b α out k xs
  let c := programGraph control (suc k) xs
  let g := programGraph (branch control a b) out xs
  let s := programGraph b out xs
  obtain ⟨hf⟩ := successorBranchElim (body := body) (Gamma := [g,c]) control a b out k xs
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := successorBranchIntro (body := body) (Gamma := [s,c]) control a b out k xs
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
