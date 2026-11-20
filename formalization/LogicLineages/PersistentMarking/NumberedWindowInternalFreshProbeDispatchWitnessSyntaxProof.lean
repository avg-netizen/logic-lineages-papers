module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (programSubst numeralSubst liftTermSubst existsEmbeddedSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding bindTerm liftBind varBind)
open NumberedWindowInternalProbeTargets (OTerm typeCode freshAt typedAt witnesses)
open NumberedWindowInternalFreshProbeSyntaxProof (freshRename freshSubst)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem binaryRename {α β : Type} (s t : OTerm α) (j : α → β) :
    (fun i : Fin 2 => (![s,t] i).relabel j) = ![s.relabel j,t.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)) i

private theorem ternaryRename {α β : Type} (s t u : OTerm α) (j : α → β) :
    (fun i : Fin 3 => (![s,t,u] i).relabel j) = ![s.relabel j,t.relabel j,u.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))) i

private theorem binarySubst {α β : Type} (s t : OTerm α) (f : α → OTerm β) :
    (fun i : Fin 2 => (![s,t] i).subst f) = ![s.subst f,t.subst f] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)) i

theorem typedRename {α β : Type} (h : Program 2) (τ : ProbeTy) (q : OTerm α) (j : α → β) :
    (typedAt h τ q).relabel j = typedAt h τ (q.relabel j) := by
  simp only [typedAt,programRename,binaryRename,numeralRename]

private theorem typedSubst {α β : Type} (h : Program 2) (τ : ProbeTy) (q : OTerm α)
    (f : α → OTerm β) :
    (typedAt h τ q).subst (fun a => emb (f a)) = typedAt h τ (q.subst f) := by
  simp only [typedAt,programSubst,binarySubst,numeralSubst]

private theorem acceptsRename {α β : Type} (p : Program 3) (q u v : OTerm α) (j : α → β) :
    (accepts p q u v).relabel j = accepts p (q.relabel j) (u.relabel j) (v.relabel j) := by
  change (programGraph p (numeral 1) ![q,u,v]).relabel j =
    programGraph p (numeral 1) ![q.relabel j,u.relabel j,v.relabel j]
  simp only [programRename,ternaryRename,numeralRename]

theorem witnessesRename {α β : Type} (p : Program 3) (h : Program 2) (a : Program 1)
    (τ : ProbeTy) (q : OTerm α) (j : α → β) :
    (witnesses p h a τ q).relabel j = witnesses p h a τ (q.relabel j) := by
  simp only [witnesses,existsRename,conjunctionRename,freshRename,acceptsRename,typedRename,
    Term.relabel_relabel] <;> rfl

private def factors {α : Type} (p : Program 3) (h : Program 2) (a : Program 1)
    (τ : ProbeTy) (q u v : OTerm α) : Formula α :=
  freshAt a q u ⊓ (accepts p q u v ⊓ typedAt h τ v)

private theorem factorsSubst {α β : Type} (p : Program 3) (h : Program 2) (a : Program 1)
    (τ : ProbeTy) (q u v : OTerm α) (s : α → OTerm β) :
    (factors p h a τ q u v).subst (fun i => emb (s i)) =
      factors p h a τ (q.subst s) (u.subst s) (v.subst s) := by
  simp only [factors,conjunctionSubst,freshSubst,acceptsSubst,typedSubst]

/-- Introduce the two literal #611 quantifiers using the actual graphs at
the exact selected q,u,v (outer witness first, then the inner result). -/
theorem witnessesIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 3) (h : Program 2) (a : Program 1) (τ : ProbeTy) (q u v : OTerm α)
    (hf : Nonempty (Derivation body Γ (freshAt a q u)))
    (hp : Nonempty (Derivation body Γ (accepts p q u v)))
    (ht : Nonempty (Derivation body Γ (typedAt h τ v))) :
    Nonempty (Derivation body Γ (witnesses p h a τ q)) := by
  let q' : OTerm (α ⊕ Fin 1) := q.relabel Sum.inl
  let u' : OTerm (α ⊕ Fin 1) := u.relabel Sum.inl
  let A : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    factors p h a τ (q'.relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))
  let B : Formula (α ⊕ Fin 1) := factors p h a τ q' u' (.var (.inr 0))
  have ho : instantiate (existsOne A) (emb u) = existsOne B := by
    simp only [instantiate,bindEmbedding,existsEmbeddedSubst,A,B,factorsSubst,liftTermSubst,liftBind] <;> rfl
  have hi : instantiate B (emb v) = factors p h a τ q u v := by
    simp only [instantiate,bindEmbedding,B,q',u',factorsSubst,liftBind,varBind]
  obtain ⟨df⟩ := hf
  obtain ⟨dp⟩ := hp
  obtain ⟨dt⟩ := ht
  change Nonempty (Derivation body Γ (existsOne (existsOne A)))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb u)
  rw [ho]
  apply Derivation.existentialIntroduction (emb v)
  rw [hi]
  exact Derivation.conjunctionIntroduction df (Derivation.conjunctionIntroduction dp dt)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
