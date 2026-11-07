module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraphSupportProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalQuotientComparisonProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def excludedMiddle (p : Formula α) : Derivation body Gamma (p ⊔ p.not) :=
  Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)

/-- Exact graph description from proved branch values. Functionality removes
all alternative outputs, and original equality transports the converse. -/
theorem choiceEquation {n : Nat} (p : Program n) (out yes no : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α) (condition : Formula α)
    (hy : Nonempty (Derivation body [] (condition.imp (programGraph p yes xs))))
    (hn : Nonempty (Derivation body [] (condition.not.imp (programGraph p no xs)))) :
    let g := programGraph p out xs
    let s := (condition ⊓ eqn out yes) ⊔ (condition.not ⊓ eqn out no)
    Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g))) := by
  let g := programGraph p out xs
  let s := (condition ⊓ eqn out yes) ⊔ (condition.not ⊓ eqn out no)
  have forward : Nonempty (Derivation body [g] s) := by
    have left : Nonempty (Derivation body (condition :: [g]) s) := by
      have dy := closedApply hy (show Nonempty (Derivation body (condition :: [g]) condition) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
      obtain ⟨de⟩ := valueUnique p out yes xs
        (show Nonempty (Derivation body (condition :: [g]) g) from
          ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩) dy
      exact ⟨orLeft (Derivation.conjunctionIntroduction
        (Derivation.hypothesis List.mem_cons_self) de)⟩
    have right : Nonempty (Derivation body (condition.not :: [g]) s) := by
      have dn := closedApply hn (show Nonempty (Derivation body (condition.not :: [g]) condition.not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
      obtain ⟨de⟩ := valueUnique p out no xs
        (show Nonempty (Derivation body (condition.not :: [g]) g) from
          ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩) dn
      exact ⟨orRight (Derivation.conjunctionIntroduction
        (Derivation.hypothesis List.mem_cons_self) de)⟩
    obtain ⟨left⟩ := left
    obtain ⟨right⟩ := right
    exact ⟨disjunctionElimination (excludedMiddle condition)
      (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩
  have backward : Nonempty (Derivation body [s] g) := by
    have left : Nonempty (Derivation body ((condition ⊓ eqn out yes) :: [s]) g) := by
      have dc : Derivation body ((condition ⊓ eqn out yes) :: [s]) condition :=
        Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
      have de : Derivation body ((condition ⊓ eqn out yes) :: [s]) (eqn out yes) :=
        Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
      exact outputTransport p yes out xs ⟨symm de⟩ (closedApply hy ⟨dc⟩)
    have right : Nonempty (Derivation body ((condition.not ⊓ eqn out no) :: [s]) g) := by
      have dc : Derivation body ((condition.not ⊓ eqn out no) :: [s]) condition.not :=
        Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
      have de : Derivation body ((condition.not ⊓ eqn out no) :: [s]) (eqn out no) :=
        Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
      exact outputTransport p no out xs ⟨symm de⟩ (closedApply hn ⟨dc⟩)
    obtain ⟨left⟩ := left
    obtain ⟨right⟩ := right
    exact ⟨disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
