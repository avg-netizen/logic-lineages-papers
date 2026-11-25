module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationWitnessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding bindTerm liftBind varBind)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open NumberedWindowInternalNeutralFactsTargets (D directData direct inherited)
open NumberedWindowInternalPullbackTargets (forwardImage)

variable {α : Type} {Γ : List (Formula α)}

private theorem bindOld (q t : OTerm α) : (q.relabel Sum.inl).subst (bindTerm t) = q := by
  rw [termRelabelSubst]
  exact termSubstVar q

/-- An actual direct certificate for the same function and an actual
application at its earlier function introduce the manuscript's
inherited witness, preserving the whole original argument. -/
theorem exact_OpenLiteralInheritedWitness (s : Data) (p h : Program 3) (c : Nat)
    (x u y witness : OTerm α)
    (preceding : D s c Γ (direct s h c x witness))
    (matchApp : D s c Γ (accepts p witness u y)) :
    D s c Γ (inherited s p h c x u y) := by
  obtain ⟨one⟩ := preceding
  obtain ⟨two⟩ := matchApp
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := direct s h c (x.relabel Sum.inl) v ⊓ accepts p v (u.relabel Sum.inl) (y.relabel Sum.inl)
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb witness)
  simp only [clause,instantiate,bindEmbedding,conjunctionSubst,direct,edgeSubst,acceptsSubst,
    liftBind,v,varBind]
  exact Derivation.conjunctionIntroduction one two

/-- Finish the positive application image with the actual target
witness. Acceptance and the independently checked positive edge
remain separate premises, with no reflexive edge introduced. -/
theorem exact_OpenLiteralForwardImageWitness (s : Data) (p : Program 3) (c : Nat)
    (g u x witness : OTerm α)
    (matchApp : D s c Γ (accepts p g u witness)) (actual : D s c Γ (edge s false c x witness)) :
    D s c Γ (forwardImage s p c g u x) := by
  obtain ⟨one⟩ := matchApp
  obtain ⟨two⟩ := actual
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := accepts p (g.relabel Sum.inl) (u.relabel Sum.inl) v ⊓ edge s false c (x.relabel Sum.inl) v
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb witness)
  simp only [clause,instantiate,bindEmbedding,conjunctionSubst,edgeSubst,acceptsSubst,liftBind,v,varBind]
  exact Derivation.conjunctionIntroduction one two

#print axioms exact_OpenLiteralInheritedWitness
#print axioms exact_OpenLiteralForwardImageWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationWitnessProof
