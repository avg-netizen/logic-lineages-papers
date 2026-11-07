module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalSourceInversionSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Acceptance implies the underlying positive acceptance in BOTH original
branches. The control is arbitrary; neither validity nor calibration is used. -/
theorem branchConjunctionRecover {n : Nat} (control p q : Program n)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph (branch control p (conjunction p q)) (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph p (suc z) xs)) := by
  apply programCases control xs _
  intro β j Delta v hj hv
  simp only [programRename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at hp'
  apply zeroSuccessorCases Delta v _
  · obtain ⟨dc⟩ := hv
    obtain ⟨dp⟩ := hp'
    have hc := outputTransport control v z (fun i => (xs i).relabel j)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp dc (eqn v z)⟩
    exact zeroBranchElim control p (conjunction p q) (suc z)
      (fun i => (xs i).relabel j) hc ⟨addHyp dp (eqn v z)⟩
  · intro γ k Theta pred hk he
    simp only [programRename,sucRelabel,zRelabel]
    have hc := renameInto hv k Theta hk
    have hp'' := renameInto hp' k Theta hk
    simp only [programRename,sucRelabel,zRelabel] at hc hp''
    have hs := outputTransport control (v.relabel k) (suc pred)
      (fun i => ((xs i).relabel j).relabel k) he hc
    have hq := successorBranchElim control p (conjunction p q) (suc z) pred
      (fun i => ((xs i).relabel j).relabel k) hs hp''
    obtain ⟨d⟩ := conjunctionRecover p q _ hq
    exact ⟨Derivation.conjunctionLeft d⟩

theorem guardedPositiveRecover (positive : Program 4) (typed : Program 3)
    (tag : Program 2) (window : Program 1) (xs : Fin 4 → OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (programGraph (GuardedSource.guardedPositive positive typed tag window) (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph positive (suc z) xs)) :=
  branchConjunctionRecover (GuardedSource.activation typed tag window) positive
    (conjunction (GuardedSource.targetTyped typed tag) (GuardedSource.sameTag tag)) xs hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceBranchProof
