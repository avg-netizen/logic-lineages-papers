module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionSeedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionProof (actualStrongInductionInstance)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax belowRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverArgumentGuardOpenProof (exact_OpenCoverArgumentGuardCases)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
  (argumentExistsRename argumentAtRename argumentMotiveAt argumentMotiveLift)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (transportArgument)
open NumberedWindowInternalCoverArgumentGrammarInductionSeedProof (actualArgumentGrammarSeed)
open NumberedWindowInternalCoverArgumentGrammarInductionConsProof (actualArgumentGrammarFromTail)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem belowRelabel {β : Type} (F G : Program 1) (s : Settings) (q : OTerm α) (j : α → β) :
    (below (argumentMotive F G s) q).relabel j =
      below (argumentMotive F G s) (q.relabel j) := by
  rw [belowRename]
  unfold argumentMotive
  rw [argumentAtRename] <;> rfl

private theorem atTail (F G : Program 1) (s : Settings) (q tail : OTerm α)
    (hyp : Nonempty (Derivation body Γ (below (argumentMotive F G s) q)))
    (earlier : Nonempty (Derivation body Γ (ltF tail q)))
    (valid : Nonempty (Derivation body Γ (unary (argumentReject G) z tail))) :
    Nonempty (Derivation body Γ (argumentExists F s tail)) := by
  obtain ⟨hyp⟩ := hyp
  obtain ⟨earlier⟩ := earlier
  obtain ⟨valid⟩ := valid
  have role := Derivation.universalElimination (emb tail) hyp
  rw [belowElimSyntax,argumentMotiveAt] at role
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination role earlier) valid⟩

private theorem atKey (F G : Program 1) (s : Settings) (q : OTerm α)
    (provider : HeadProvider F G s body)
    (hyp : Nonempty (Derivation body Γ (below (argumentMotive F G s) q)))
    (valid : Nonempty (Derivation body Γ (unary (argumentReject G) z q))) :
    Nonempty (Derivation body Γ (argumentExists F s q)) := by
  apply exact_OpenCoverArgumentGuardCases G body α Γ q (argumentExists F s q) valid
  · intro β j Δ _ eq
    obtain ⟨eq⟩ := eq
    rw [argumentExistsRename]
    exact transportArgument F s z (q.relabel j) ⟨symm eq⟩ (actualArgumentGrammarSeed F s)
  · intro β j Δ h a keep eq small hd tl
    have early := renameInto hyp j Δ keep
    rw [belowRelabel] at early
    have tail := atTail F G s (q.relabel j) a early small tl
    have packed := actualArgumentGrammarFromTail F G s h a provider hd tail
    obtain ⟨eq⟩ := eq
    rw [argumentExistsRename]
    exact transportArgument F s (rawCons h a) (q.relabel j) ⟨symm eq⟩ packed

theorem exact_OpenCoverArgumentGrammarInduction : ExactOpenCoverArgumentGrammarInduction := by
  intro F G s body α Γ raw provider valid
  let theta : Formula (α ⊕ Fin 1) := argumentMotive F G s
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let belowKey : Formula (α ⊕ Fin 1) := below (lift theta) key
  let D : List (Formula (α ⊕ Fin 1)) := belowKey :: Γ.map weaken
  let guard := unary (argumentReject G) z key
  have hyp : Nonempty (Derivation body (guard :: D) (below (argumentMotive F G s) key)) := by
    have h : Derivation body (guard :: D) belowKey :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    change Derivation body (guard :: D) (below (lift (argumentMotive (α := α) F G s)) key) at h
    rw [argumentMotiveLift] at h
    exact ⟨h⟩
  have step : Nonempty (Derivation body D theta) := by
    obtain ⟨yes⟩ := atKey F G s key provider hyp ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction yes⟩
  obtain ⟨family⟩ := actualStrongInductionInstance body α Γ theta raw step
  change Derivation body Γ (instantiate (argumentMotive F G s) (emb raw)) at family
  rw [argumentMotiveAt] at family
  obtain ⟨valid⟩ := valid
  exact ⟨Derivation.implicationElimination family valid⟩

#print axioms exact_OpenCoverArgumentGrammarInduction

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionProof
