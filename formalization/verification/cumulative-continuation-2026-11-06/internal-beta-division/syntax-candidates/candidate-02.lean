module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalBetaWitness InternalBinderTransportSyntaxProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof

theorem mulRelabel {α β : Type} (s t : OrdinaryArithmetic.Term α) (j : α → β) :
    (OrdinaryArithmetic.mulTerm s t).relabel j =
      OrdinaryArithmetic.mulTerm (s.relabel j) (t.relabel j) := binaryRelabel _ _ _ _

/-- Renaming preserves the original arithmetic modulus term. -/
theorem modulusRename {α β : Type} (b i : OrdinaryArithmetic.Term α) (j : α → β) :
    (modulus b i).relabel j = modulus (b.relabel j) (i.relabel j) := by
  simp only [modulus,OrdinaryArithmetic.mulTerm,sucRelabel,binaryRelabel]

/-- Free renaming commutes with the existing finite existential prefix. -/
theorem exsRename {L : Language} {α β : Type} {k : Nat}
    (phi : L.BoundedFormula α k) (j : α → β) :
    rename j phi.exs = (rename j phi).exs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change rename j phi.ex.exs = _
    rw [ih]
    rfl

/-- This is syntactic renaming of the unchanged original beta formula. -/
theorem originalBetaRename {α β : Type} (a b i r : OrdinaryArithmetic.Term α) (j : α → β) :
    (OrdinaryArithmetic.betaFormula a b i r).relabel j =
      OrdinaryArithmetic.betaFormula (a.relabel j) (b.relabel j) (i.relabel j) (r.relabel j) := by
  rw [formulaRelabel]
  unfold OrdinaryArithmetic.betaFormula
  rw [exsRename]
  congr 1
  unfold OrdinaryArithmetic.betaBody
  simp only [rename,BoundedFormula.inf,BoundedFormula.not,BoundedFormula.mapTermRel,Term.bdEqual,
    OrdinaryArithmetic.addTerm,OrdinaryArithmetic.mulTerm,binaryRelabel,sucRelabel,
    Term.relabel_relabel,Term.relabel]
  rfl

/-- Embedded beta renaming keeps all four original arithmetic arguments literal. -/
theorem betaRename {α β : Type} (a b i r : OrdinaryArithmetic.Term α) (j : α → β) :
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)).relabel j =
      arithmeticEmbedding.onFormula
        (OrdinaryArithmetic.betaFormula (a.relabel j) (b.relabel j) (i.relabel j) (r.relabel j)) := by
  rw [← arithmeticRename,originalBetaRename]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
