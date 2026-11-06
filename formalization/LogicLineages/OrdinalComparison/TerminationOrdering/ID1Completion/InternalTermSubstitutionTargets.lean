module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionTargets
open FirstOrder Language PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open InternalCalculus SourceEndpoint TaggedArithmeticOperators

/-- Exact formula syntax, not equality of standard-model truth values. -/
def ActualFormulaSubstitutionComposition : Prop :=
  ∀ (α β γ : Type) (phi : Formula α) (ts : α → Term β) (us : β → Term γ),
  (phi.subst ts).subst us = phi.subst (fun a => (ts a).subst us)

def ActualUniversalSubstitution : Prop :=
  ∀ (α β : Type) (phi : Formula (α ⊕ Fin 1)) (ts : α → Term β),
  (allOne phi).subst ts = allOne (phi.subst
    (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))))

/-- The EXISTING Positive substitution compiles to literal ordinary formula
substitution, including every binder and arithmetic antecedent. -/
def ActualPositiveSubstitution : Prop :=
  ∀ (α β : Type) (p : Positive α) (ts : α → OrdinaryArithmetic.Term β),
  (substitutePositive ts p).formula = p.formula.subst (fun a => arithmeticEmbedding.onTerm (ts a))

/-- Exact syntax specialization of the ORIGINAL closed source body. -/
def ActualSourceBodyInstantiation : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  instantiate (bodyWithParameters (SourcePresentation.sourceBody data context) α).formula
      (arithmeticEmbedding.onTerm t) =
    (substitutePositive ![numeral context,t]
      (combinedOperator (SourcePresentation.scalarOperator data) (SourcePresentation.multisetOperator data))).formula

/-- A genuine internal proof, rewritten by the exact syntax identity above.
This exposes the original tagged operator, not a replacement by N-truth. -/
def ActualExplicitSourceUnfolding : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate t).formula.iff
      (substitutePositive ![numeral context,t]
        (combinedOperator (SourcePresentation.scalarOperator data) (SourcePresentation.multisetOperator data))).formula))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionTargets
