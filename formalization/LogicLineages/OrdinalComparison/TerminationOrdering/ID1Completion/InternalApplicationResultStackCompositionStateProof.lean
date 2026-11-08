module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem liveStateValue (state packed work results : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing packed work results)))
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) packed))) :
    Nonempty (Derivation body Gamma (graph2 liveState state work results)) := by
  let xs : Fin 2 → OTerm α := Fin.cons work (Fin.cons results Fin.elim0)
  have hi := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    packed work results xs hp (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 2)
    (pairOf (.projection 0) (.projection 1)) state (suc z) packed xs hs
    (InternalLessThanSupportProof.oneConstantValue xs) hi

theorem emptyStateValue (state packed results : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing packed z results)))
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) packed))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results)) := by
  let xs : Fin 1 → OTerm α := Fin.cons results Fin.elim0
  have hi := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1) (.projection 0)
    packed z results xs hp (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1)
    (pairOf (InternalAcceptance.constantZero 1) (.projection 0)) state (suc z) packed xs hs
    (InternalLessThanSupportProof.oneConstantValue xs) hi

theorem liveStateCases (state work results : OTerm α) (psi : Formula α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work results)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (packed : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing packed (work.relabel j) (results.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing (state.relabel j) (suc z) packed)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases InternalPairing.pairing (Fin.cons work (Fin.cons results Fin.elim0)) psi
  intro β j Delta packed hj hp
  simp only [consTermRename,emptyRename] at hp
  have hs' := renameInto hs j Delta hj
  rw [graph2Rename] at hs'
  let xs : Fin 2 → OTerm β := Fin.cons (work.relabel j) (Fin.cons (results.relabel j) Fin.elim0)
  have hi := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    packed (work.relabel j) (results.relabel j) xs hp (projectionValue 0 xs) (projectionValue 1 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2)
    (pairOf (.projection 0) (.projection 1)) (state.relabel j) (suc z) packed xs hs'
    (InternalLessThanSupportProof.oneConstantValue xs) hi
  exact k β j Delta packed hj hp ho

theorem liveOfValue {n : Nat} (p q : Program n) (out work results : OTerm α)
    (xs : Fin n → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState out work results)))
    (hp : Nonempty (Derivation body Gamma (programGraph p work xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q results xs))) :
    Nonempty (Derivation body Gamma (programGraph (InternalApplicationResultStack.liveOf p q) out xs)) := by
  apply liveStateCases out work results _ hs
  intro β j Delta packed hj hi ho
  rw [programRename]
  have hp' := renameInto hp j Delta hj
  have hq' := renameInto hq j Delta hj
  rw [programRename] at hp' hq'
  have hpair := binaryValue InternalPairing.pairing p q packed (work.relabel j) (results.relabel j)
    (fun i => (xs i).relabel j) hi hp' hq'
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne n) (pairOf p q)
    (out.relabel j) (suc z) packed (fun i => (xs i).relabel j) ho
    (InternalLessThanSupportProof.oneConstantValue _) hpair

theorem emptyStateCases (state results : OTerm α) (psi : Formula α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (packed : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing packed z (results.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing (state.relabel j) (suc z) packed)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases InternalPairing.pairing (Fin.cons z (Fin.cons results Fin.elim0)) psi
  intro β j Delta packed hj hp
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  let xs : Fin 1 → OTerm β := Fin.cons (results.relabel j) Fin.elim0
  have hi := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1) (.projection 0)
    packed z (results.relabel j) xs hp (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1)
    (pairOf (InternalAcceptance.constantZero 1) (.projection 0)) (state.relabel j) (suc z) packed xs hs'
    (InternalLessThanSupportProof.oneConstantValue xs) hi
  exact k β j Delta packed hj hp ho

theorem liveStateFields (state work results : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work results))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.work work state ⊓
      graph1 InternalApplicationResultStack.results results state)) := by
  apply liveStateCases state work results _ hs
  intro β j Delta packed _ hp ho
  simp only [conjunctionRename,graph1Rename]
  let xs : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  have hi := pairRight (state.relabel j) (suc z) packed ho
  exact andIntro
    (unaryValue InternalUnpair.left InternalUnpair.right (work.relabel j) packed xs
      (pairLeft packed (work.relabel j) (results.relabel j) hp) hi)
    (unaryValue InternalUnpair.right InternalUnpair.right (results.relabel j) packed xs
      (pairRight packed (work.relabel j) (results.relabel j) hp) hi)

theorem liveStatus (state work results : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work results))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.status (suc z) state)) := by
  apply liveStateCases state work results _ hs
  intro β j Delta packed _ _ ho
  simp only [graph1Rename,sucRelabel,zRelabel]
  exact pairLeft (state.relabel j) (suc z) packed ho

theorem emptyAsLive (state results : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results))) :
    Nonempty (Derivation body Gamma (graph2 liveState state z results)) := by
  apply emptyStateCases state results _ hs
  intro β j Delta packed _ hp ho
  simp only [graph2Rename,zRelabel]
  exact liveStateValue (state.relabel j) packed z (results.relabel j) hp ho

theorem liveAsEmpty (state results : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state z results))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results)) := by
  apply liveStateCases state z results _ hs
  intro β j Delta packed _ hp ho
  simp only [graph1Rename]
  simp only [zRelabel] at hp
  exact emptyStateValue (state.relabel j) packed (results.relabel j) hp ho

/-- The failure state has status zero and remains zero under the actual AST. -/
theorem failureFixed (guard leaf : Program 1) (combine : Program 4) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationResultStack.transition guard leaf combine) (z : OTerm α) z)) := by
  let xs : Fin 1 → OTerm α := Fin.cons z Fin.elim0
  have hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.status (z : OTerm α) z)) :=
    pairLeft z z z InternalApplicationValidityStackAppendTransitionProof.pairZero
  have he := InternalEqualityTestCompositionProof.rejectForwardGap (body := body) (Gamma := Gamma)
    (z : OTerm α) (suc z) z ⟨InternalAdditionLawsProof.leftZero (suc z)⟩
  apply zeroBranchIntro _ _ _ z xs
  · exact binaryValue InternalEqualityTest.equalityTest InternalApplicationResultStack.status
      (InternalLessThan.constantOne 1) z z (suc z) xs he hs
      (InternalLessThanSupportProof.oneConstantValue xs)
  · exact InternalAcceptanceConjunctionProof.constantZeroValue xs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
