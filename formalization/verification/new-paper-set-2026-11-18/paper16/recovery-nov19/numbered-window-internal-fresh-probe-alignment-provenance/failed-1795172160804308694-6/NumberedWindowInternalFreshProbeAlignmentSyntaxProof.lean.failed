module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source (Ty)
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalGraphCompositionSyntaxProof (embedSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (onTermRelabel)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaSubstRelabel)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalFreshProbeAlignmentTargets

private theorem argsSubst {α β : Type} (t q : OTerm α) (s : α → OTerm β) :
    (fun i : Fin 2 => (![t,q] i).subst s) = ![t.subst s,q.subst s] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem typedSubst {α β : Type} (h : Program 2) (τ : Ty) (q : OTerm α)
    (s : α → OTerm β) :
    (typedAt h τ q).subst (fun x => emb (s x)) = typedAt h τ (q.subst s) := by
  simp only [typedAt,programSubst,argsSubst,numeralSubst]

theorem alignedRename {α β : Type} (p : Program 3) (h : Program 2) (τ : Ty)
    (q u : OTerm α) (j : α → β) :
    (alignedResultAt p h τ q u).relabel j = alignedResultAt p h τ (q.relabel j) (u.relabel j) := by
  simp only [alignedResultAt,existsRename,conjunctionRename,acceptsRename,typedRename,Term.relabel_relabel] <;> rfl

theorem resultIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 3) (h : Program 2) (τ : Ty) (q u v : OTerm α)
    (ha : Nonempty (Derivation body Γ (accepts p q u v)))
    (ht : Nonempty (Derivation body Γ (typedAt h τ v))) :
    Nonempty (Derivation body Γ (alignedResultAt p h τ q u)) := by
  obtain ⟨a⟩ := ha
  obtain ⟨b⟩ := ht
  apply Nonempty.intro
  unfold alignedResultAt
  apply Derivation.existentialIntroduction (emb v)
  simp only [instantiate,bindEmbedding,conjunctionSubst,acceptsSubst,typedSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction a b

/-- Renaming the actual original carrier embeds the same literal
context numeral and changes only the free object term. -/
theorem carrierRename {α β : Type} (data : Data) (odd : Bool) (c : Nat)
    (x : OTerm α) (j : α → β) :
    (carrier data odd c x).relabel j = carrier data odd c (x.relabel j) := by
  unfold carrier
  simp only [embedSubst,formulaSubstRelabel]
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · change (emb (numeral c : OTerm α)).relabel j = emb (numeral c : OTerm β)
    rw [← onTermRelabel,numeralRename]
  · exact (onTermRelabel _ j x).symm

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
