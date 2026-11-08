module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalBoundedDescentNormalizer InternalAcceptance InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem conjunctionReject {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph (conjunction p q) (suc z) xs).not)) :
    Nonempty (Derivation body Gamma (programGraph (conjunction p q) z xs)) := by
  obtain ⟨hn⟩ := hn
  let P := programGraph p (suc z) xs
  have hy : Nonempty (Derivation body (P :: Gamma) (programGraph (conjunction p q) z xs)) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hq : Nonempty (Derivation body (P :: Gamma) (programGraph q (suc z) xs).not) := by
      obtain ⟨ha⟩ := conjunctionAccept (body := body)
        (Gamma := programGraph q (suc z) xs :: P :: Gamma) p q xs
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact ⟨Derivation.implicationIntroduction
        (Derivation.implicationElimination (addHyp (addHyp hn P) _) ha)⟩
    exact successorBranchIntro (normalize p) (constantZero n) (normalize q) z z xs
      (normalizeAccept p xs hp) (normalizeReject q xs hq)
  have hn' : Nonempty (Derivation body (P.not :: Gamma) (programGraph (conjunction p q) z xs)) :=
    zeroBranchIntro (normalize p) (constantZero n) (normalize q) z xs
      (normalizeReject p xs ⟨Derivation.hypothesis List.mem_cons_self⟩) (constantZeroValue xs)
  obtain ⟨hy⟩ := hy
  obtain ⟨hn'⟩ := hn'
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn')⟩

theorem chooseSplit (V : Program 1) (out candidate input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out (Fin.cons candidate (Fin.cons input Fin.elim0))))) :
    Nonempty (Derivation body Gamma
      (eqn out input ⊔ programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)))) := by
  obtain ⟨h⟩ := h
  let xs : Fin 2 → OTerm α := Fin.cons candidate (Fin.cons input Fin.elim0)
  let P := programGraph (guard V) (suc z) xs
  let S := eqn out input ⊔ programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0))
  have hy : Nonempty (Derivation body (P :: Gamma) S) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := successorBranchElim (guard V) (.projection (1 : Fin 2)) (.projection (0 : Fin 2))
      out z xs hp ⟨addHyp h P⟩
    obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 2)) out candidate xs ho (projectionValue 0 xs)
    obtain ⟨hg⟩ := headTransport (guard V) (suc z) candidate out (Fin.cons input Fin.elim0)
      ⟨symm he⟩ hp
    exact ⟨orRight hg⟩
  have hn : Nonempty (Derivation body (P.not :: Gamma) S) := by
    have hz := conjunctionReject InternalLessThan.ltTest
      (conjunction (candidateValid V) sameLeft) xs
      (show Nonempty (Derivation body (P.not :: Gamma) P.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho := zeroBranchElim (guard V) (.projection (1 : Fin 2)) (.projection (0 : Fin 2))
      out xs hz ⟨addHyp h P.not⟩
    obtain ⟨he⟩ := valueUnique (.projection (1 : Fin 2)) out input xs ho (projectionValue 1 xs)
    exact ⟨orLeft he⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

@[simp] theorem unaryRename {β : Type} (p : Program 1) (out input : OTerm α) (j : α → β) :
    (unaryGraph p out input).relabel j = unaryGraph p (out.relabel j) (input.relabel j) := by
  simp only [unaryGraph, programRename, consTermRename, emptyRename]

/-- Eliminate the representative value using original graph totality and
recover the exact frozen outer composition. -/
theorem transitionCases (R V : Program 1) (out input : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (candidate : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph (choose V) (out.relabel j)
        (Fin.cons candidate (Fin.cons (input.relabel j) Fin.elim0)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases R (Fin.cons input Fin.elim0) psi
  intro β j Delta candidate hj hc
  have ht := renameInto h j Delta hj
  simp only [transitionGraph, unaryRename] at ht
  have hc' : Nonempty (Derivation body Delta
      (unaryGraph R candidate (input.relabel j))) := by
    simpa only [unaryGraph, consTermRename, emptyRename] using hc
  have ho := compositionRecover (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))
    (out.relabel j) (Fin.cons (input.relabel j) Fin.elim0)
    (Fin.cons candidate (Fin.cons (input.relabel j) Fin.elim0)) ht
    (fun i => Fin.cases hc' (Fin.cases (projectionValue (0 : Fin 1) (Fin.cons (input.relabel j) Fin.elim0)) (fun k => Fin.elim0 k)) i)
  exact k β j Delta candidate hj ho

theorem guardLess (V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0))))) :
    Nonempty (Derivation body Gamma (ltF out input)) := by
  obtain ⟨hc⟩ := conjunctionRecover InternalLessThan.ltTest
    (conjunction (candidateValid V) sameLeft) _ h
  exact InternalLessThanProof.lessOfAcceptance out input ⟨Derivation.conjunctionLeft hc⟩

theorem guardRest (V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0))))) :
    Nonempty (Derivation body Gamma
      (programGraph (candidateValid V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)) ⊓
       programGraph sameLeft (suc z) (Fin.cons out (Fin.cons input Fin.elim0)))) := by
  obtain ⟨hc⟩ := conjunctionRecover InternalLessThan.ltTest
    (conjunction (candidateValid V) sameLeft) _ h
  exact conjunctionRecover (candidateValid V) sameLeft _ ⟨Derivation.conjunctionRight hc⟩

theorem guardValid (V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0))))) :
    Nonempty (Derivation body Gamma (validGraph V out)) := by
  obtain ⟨hc⟩ := guardRest V out input h
  exact compositionRecover V (fun _ : Fin 1 => .projection (0 : Fin 2)) (suc z)
    (Fin.cons out (Fin.cons input Fin.elim0)) (Fin.cons out Fin.elim0)
    ⟨Derivation.conjunctionLeft hc⟩
    (fun i => Fin.cases (projectionValue (0 : Fin 2) (Fin.cons out (Fin.cons input Fin.elim0))) (fun j => Fin.elim0 j) i)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
