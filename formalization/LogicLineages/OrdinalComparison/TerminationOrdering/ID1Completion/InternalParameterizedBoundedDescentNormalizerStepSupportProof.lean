module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalParameterizedBoundedDescentNormalizer InternalAcceptance InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The choice is either the original value or an accepted candidate, with
exactly the same symbolic parameter in both guard occurrences. -/
theorem chooseSplit (V : Program 2) (out candidate input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out
        (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma
      (eqn out input ⊔ programGraph (guard V) (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))))) := by
  obtain ⟨h⟩ := h
  let xs : Fin 3 → OTerm α := Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))
  let P := programGraph (guard V) (suc z) xs
  let S := eqn out input ⊔ programGraph (guard V) (suc z)
    (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0)))
  have hy : Nonempty (Derivation body (P :: Gamma) S) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := successorBranchElim (guard V) (.projection (1 : Fin 3)) (.projection (0 : Fin 3))
      out z xs hp ⟨addHyp h P⟩
    obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 3)) out candidate xs ho (projectionValue 0 xs)
    obtain ⟨hg⟩ := headTransport (guard V) (suc z) candidate out
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨symm he⟩ hp
    exact ⟨orRight hg⟩
  have hn : Nonempty (Derivation body (P.not :: Gamma) S) := by
    have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject candidateLess
      (conjunction (candidateValid V) sameLeft) xs
      (show Nonempty (Derivation body (P.not :: Gamma) P.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho := zeroBranchElim (guard V) (.projection (1 : Fin 3)) (.projection (0 : Fin 3))
      out xs hz ⟨addHyp h P.not⟩
    obtain ⟨he⟩ := valueUnique (.projection (1 : Fin 3)) out input xs ho (projectionValue 1 xs)
    exact ⟨orLeft he⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

@[simp] theorem binaryRename {β : Type} (p : Program 2)
    (out input parameter : OTerm α) (j : α → β) :
    (binaryGraph p out input parameter).relabel j =
      binaryGraph p (out.relabel j) (input.relabel j) (parameter.relabel j) := by
  simp only [binaryGraph, programRename, consTermRename, emptyRename]

@[simp] theorem leftRename {β : Type} (typ input : OTerm α) (j : α → β) :
    (leftGraph typ input).relabel j = leftGraph (typ.relabel j) (input.relabel j) := by
  simp only [leftGraph, programRename, consTermRename, emptyRename]

/-- Eliminate the actual binary representative graph, then recover the
three-input choice at [candidate, value, parameter]. -/
theorem transitionCases (R V : Program 2) (out input parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input parameter)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (candidate : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph (choose V) (out.relabel j)
        (Fin.cons candidate (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases R (Fin.cons input (Fin.cons parameter Fin.elim0)) psi
  intro β j Delta candidate hj hc
  have ht := renameInto h j Delta hj
  simp only [transitionGraph, binaryRename] at ht
  have hc' : Nonempty (Derivation body Delta
      (binaryGraph R candidate (input.relabel j) (parameter.relabel j))) := by
    simpa only [binaryGraph, consTermRename, emptyRename] using hc
  let xs : Fin 2 → OTerm β := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have ho := compositionRecover (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    (out.relabel j) xs
    (Fin.cons candidate (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) ht
    (fun i => Fin.cases hc' (Fin.cases (projectionValue (0 : Fin 2) xs)
      (Fin.cases (projectionValue (1 : Fin 2) xs) (fun k => Fin.elim0 k))) i)
  exact k β j Delta candidate hj ho

/-- The less-than test receives only the candidate and original value.
The carried parameter is not an input to the arithmetic comparison. -/
theorem guardLess (V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (ltF out input)) := by
  let xs : Fin 3 → OTerm α := Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))
  obtain ⟨hc⟩ := conjunctionRecover candidateLess
    (conjunction (candidateValid V) sameLeft) xs h
  have hl := compositionRecover InternalLessThan.ltTest
    (Fin.cons (.projection (0 : Fin 3)) (Fin.cons (.projection (1 : Fin 3)) Fin.elim0))
    (suc z) xs (Fin.cons out (Fin.cons input Fin.elim0))
    ⟨Derivation.conjunctionLeft hc⟩
    (fun i => Fin.cases (projectionValue (0 : Fin 3) xs)
      (Fin.cases (projectionValue (1 : Fin 3) xs) (fun k => Fin.elim0 k)) i)
  exact InternalLessThanProof.lessOfAcceptance out input hl

theorem guardRest (V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma
      (programGraph (candidateValid V) (suc z)
          (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))) ⊓
       programGraph sameLeft (suc z)
          (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))))) := by
  obtain ⟨hc⟩ := conjunctionRecover candidateLess
    (conjunction (candidateValid V) sameLeft) _ h
  exact conjunctionRecover (candidateValid V) sameLeft _ ⟨Derivation.conjunctionRight hc⟩

theorem guardValid (V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (validGraph V out parameter)) := by
  obtain ⟨hc⟩ := guardRest V out input parameter h
  let xs : Fin 3 → OTerm α := Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))
  exact compositionRecover V
    (Fin.cons (.projection (0 : Fin 3)) (Fin.cons (.projection (2 : Fin 3)) Fin.elim0))
    (suc z) xs (Fin.cons out (Fin.cons parameter Fin.elim0))
    ⟨Derivation.conjunctionLeft hc⟩
    (fun i => Fin.cases (projectionValue (0 : Fin 3) xs)
      (Fin.cases (projectionValue (2 : Fin 3) xs) (fun k => Fin.elim0 k)) i)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepSupportProof
