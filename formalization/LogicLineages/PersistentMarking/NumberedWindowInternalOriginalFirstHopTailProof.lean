module

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopTailProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding liftBind varBind eqnSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (existsEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalNeutralFactsTargets (firstHop direct)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt finishedNonempty)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof (toPositive)
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)
open NumberedWindowInternalSparsePositiveFold (finish)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem firstHopRename {α β : Type} (S : Data) (h : Program 3) (c : Nat) (x y : OTerm α) (j : α → β) :
    (firstHop S h c x y).relabel j = firstHop S h c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (firstHop S h c x y).subst (fun a => emb (.var (j a))) = _
  simp only [firstHop,direct,existsEmbeddedSubst,conjunctionSubst,orSubst,edgeSubst,eqnSubst,
    liftTermSubst,termRelabelAsSubst x j,termRelabelAsSubst y j]
  rfl

theorem provideFirstHop (S : Data) (h : Program 3) (c : Nat) (x mid y : OTerm α)
    (single : D B Γ (direct S h c x mid))
    (rest : D B Γ (eqn mid y ⊔ edge S false c mid y)) :
    D B Γ (firstHop S h c x y) := by
  obtain ⟨h₀⟩ := single
  obtain ⟨h₁⟩ := rest
  unfold firstHop
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb mid)
  simp only [instantiate,bindEmbedding,conjunctionSubst,orSubst,direct,edgeSubst,eqnSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction h₀ h₁

theorem restLeft {F G : Formula α} (p : D B Γ F) : D B Γ (F ⊔ G) := by
  obtain ⟨held⟩ := p
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact Derivation.explosion (Derivation.implicationElimination
    (Derivation.hypothesis List.mem_cons_self)
    (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) held))

theorem restRight {F G : Formula α} (p : D B Γ G) : D B Γ (F ⊔ G) := by
  obtain ⟨held⟩ := p
  exact ⟨Derivation.implicationIntroduction
    (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) held)⟩

theorem exact_PositiveHeadNilEndpoint (raw : Program 5) (least : Program 3)
    (c ty mid tail target : OTerm α) (h : D B Γ (finishAt raw least c ty mid tail target))
    (none : D B Γ (eqn tail z)) : D B Γ (eqn (suc mid) (suc target)) := by
  have f : D B Γ (programGraph (finish raw least) (suc target) ![c,ty,suc mid,tail]) := h
  have atNil : D B Γ (programGraph (finish raw least) (suc target) ![c,ty,suc mid,z]) := by
    unfold programGraph at f ⊢
    apply graphInputTransport B α 4 Γ (OrdinaryArithmetic.graphFormula (finish raw least)) (suc target)
      ![c,ty,suc mid,tail] ![c,ty,suc mid,z] _ f
    intro a
    refine Fin.cases ?_ (fun b => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_
      (fun q => Fin.elim0 q) e) d) b) a
    · change D B Γ (equal c c); rw [equalEqn]; exact ⟨refl c⟩
    · change D B Γ (equal ty ty); rw [equalEqn]; exact ⟨refl ty⟩
    · change D B Γ (equal (suc mid) (suc mid)); rw [equalEqn]; exact ⟨refl (suc mid)⟩
    · change D B Γ (equal tail z); rw [equalEqn]; exact none
  exact valueUnique (finish raw least) (suc mid) (suc target) ![c,ty,suc mid,z]
    (finishNil raw least c ty mid) atNil

theorem exact_PositiveHeadContinues (raw : Program 5) (least : Program 3)
    (c ty mid tail target : OTerm α) (h : D B Γ (finishAt raw least c ty mid tail target))
    (some : D B Γ ((eqn tail z).not)) : D B Γ (positiveAt raw least c ty mid tail target) := by
  obtain ⟨nonempty⟩ := some
  obtain ⟨value⟩ := h
  apply toPositive raw least c ty mid tail target
  unfold finishedNonempty
  rw [equalEqn]
  exact ⟨Derivation.conjunctionIntroduction nonempty value⟩

#print axioms provideFirstHop
#print axioms exact_PositiveHeadNilEndpoint
#print axioms exact_PositiveHeadContinues
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopTailProof
