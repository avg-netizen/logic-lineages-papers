module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
public import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof ID1Completion.InternalSliceInduction
open PositiveArithmeticPredicateSubstitution
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindTerm bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTerms liftTermSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst edgeSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst acceptsSubst)

def inverse {α : Type} (p : Program 3) (a x : OTerm α) : Formula α :=
  allOne ((accepts p (.var (.inr 0)) (a.relabel Sum.inl) (x.relabel Sum.inl)).imp
    (membership false (.var (.inr 0))))

def descendants {α : Type} (d : Data) (p : Program 3) (c : Nat) (a x : OTerm α) : Formula α :=
  allOne ((edge d false c (x.relabel Sum.inl) (.var (.inr 0))).imp
    (inverse p (a.relabel Sum.inl) (.var (.inr 0))))

theorem inverseSubst {α β : Type} (p : Program 3) (a x : OTerm α) (ts : α → OTerm β) :
    (inverse p a x).subst (fun i => emb (ts i)) = inverse p (a.subst ts) (x.subst ts) := by
  simp only [inverse,allEmbeddedSubst,impSubst,acceptsSubst,membershipSubst,liftTermSubst]
  rfl

theorem inverseRename {α β : Type} (p : Program 3) (a x : OTerm α) (j : α → β) :
    (inverse p a x).relabel j = inverse p (a.relabel j) (x.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (inverse p a x).subst (fun i => emb (.var (j i))) = _
  rw [inverseSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem acceptsRename {α β : Type} (p : Program 3) (f a x : OTerm α) (j : α → β) :
    (accepts p f a x).relabel j = accepts p (f.relabel j) (a.relabel j) (x.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (accepts p f a x).subst (fun i => emb (.var (j i))) = _
  rw [acceptsSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem descendantsRename {α β : Type} (d : Data) (p : Program 3) (c : Nat)
    (a x : OTerm α) (j : α → β) :
    (descendants d p c a x).relabel j = descendants d p c (a.relabel j) (x.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (descendants d p c a x).subst (fun i => emb (.var (j i))) = _
  simp only [descendants,allEmbeddedSubst,impSubst,edgeSubst,inverseSubst,liftTermSubst,termRelabelAsSubst a j,termRelabelAsSubst x j]
  rfl

theorem inverseElim {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)} (p : Program 3)
    (a x f : OTerm α) (hi : Nonempty (Derivation body Γ (inverse p a x)))
    (ha : Nonempty (Derivation body Γ (accepts p f a x))) :
    Nonempty (Derivation body Γ (membership false f)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨ha⟩ := ha
  have h := Derivation.universalElimination (emb f) hi
  simp only [instantiate,bindEmbedding,impSubst,acceptsSubst,membershipSubst,liftBind,varBind] at h
  exact ⟨Derivation.implicationElimination h ha⟩

theorem descend {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (d : Data) (p : Program 3) (c : Nat) (a x y : OTerm α)
    (hi : Nonempty (Derivation body Γ (descendants d p c a x)))
    (hr : Nonempty (Derivation body Γ (edge d false c x y))) :
    Nonempty (Derivation body Γ (inverse p a y)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hr⟩ := hr
  have h := Derivation.universalElimination (emb y) hi
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,inverseSubst,liftBind,varBind] at h
  exact ⟨Derivation.implicationElimination h hr⟩

def invariant {α : Type} (p : Program 3) (a : OTerm α) : Formula (α ⊕ Fin 1) :=
  inverse p (a.relabel Sum.inl) (.var (.inr 0))

theorem slice {α : Type} (s : Data) (p : Program 3) (c : Nat) (a : OTerm α) :
    replacedBody (sliceBody s c false) (invariant p a) =
      carrier s false c (.var (.inr 0)) ⊓
      descendants s p c (a.relabel Sum.inl) (.var (.inr 0)) := by
  rw [ID1Completion.InternalSliceInductionSyntaxProof.sliceReplacement]
  simp only [invariant,liftPredicateFormula,inverseRename,Term.relabel_relabel,descendants]
  rfl

theorem atResult {α : Type} (p : Program 3) (a x : OTerm α) :
    instantiate (invariant p a) (emb x) = inverse p a x := by
  rw [invariant,instantiate,bindEmbedding,inverseSubst,liftBind,varBind]

end LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
