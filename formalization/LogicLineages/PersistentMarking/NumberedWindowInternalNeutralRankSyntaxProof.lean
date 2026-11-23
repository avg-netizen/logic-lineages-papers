module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalStrongInduction (lift)
open ID1Completion.InternalStrongInductionSyntaxProof (belowRename)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalGraphCompositionSyntaxProof (embedSubst)
open ID1Completion.InternalTermSubstitutionSyntaxProof (formulaSubstComposition)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst numeralSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalNeutralRankTargets

private theorem evenCarrierSubst {α β : Type} (S : Data) (c : Nat) (x : OTerm α)
    (ts : α → OTerm β) :
    (carrier S false c x).subst (fun a => emb (ts a)) = carrier S false c (x.subst ts) := by
  unfold carrier
  rw [← embedSubst,formulaSubstComposition]
  congr 1
  congr 1
  funext i
  exact Fin.cases (numeralSubst c ts) (Fin.cases rfl (fun q => Fin.elim0 q)) i

private theorem positiveRankSubst {α β : Type} (g : Program 1) (k x : OTerm α)
    (ts : α → OTerm β) :
    (positiveRank g k x).subst (fun a => emb (ts a)) = positiveRank g (k.subst ts) (x.subst ts) := by
  unfold positiveRank
  rw [unarySubst,sucSubst]

theorem positiveRankRename {α β : Type} (g : Program 1) (k x : OTerm α) (ρ : α → β) :
    (positiveRank g k x).relabel ρ = positiveRank g (k.relabel ρ) (x.relabel ρ) := by
  rw [formulaRelabelAsSubst]
  change (positiveRank g k x).subst (fun a => emb (.var (ρ a))) = _
  rw [positiveRankSubst,← termRelabelAsSubst,← termRelabelAsSubst]

private theorem clauseSubst {α β : Type} (S : Data) (g : Program 1) (c : Nat)
    (k x : OTerm α) (ts : α → OTerm β) :
    (rankClause S g c k x).subst (fun a => emb (ts a)) =
      rankClause S g c (k.subst ts) (x.subst ts) := by
  unfold rankClause
  rw [impSubst,conjunctionSubst,evenCarrierSubst,positiveRankSubst,membershipSubst]

private theorem familySubst {α β : Type} (S : Data) (g : Program 1) (c : Nat)
    (k : OTerm α) (ts : α → OTerm β) :
    (rankFamily S g c k).subst (fun a => emb (ts a)) = rankFamily S g c (k.subst ts) := by
  unfold rankFamily rankMatrix
  rw [allEmbeddedSubst,clauseSubst,liftTermSubst] <;> rfl

private theorem familyRename {α β : Type} (S : Data) (g : Program 1) (c : Nat)
    (k : OTerm α) (ρ : α → β) :
    (rankFamily S g c k).relabel ρ = rankFamily S g c (k.relabel ρ) := by
  rw [formulaRelabelAsSubst]
  change (rankFamily S g c k).subst (fun a => emb (.var (ρ a))) = _
  rw [familySubst,← termRelabelAsSubst]

theorem rankMotiveRename {α β : Type} (S : Data) (g : Program 1) (c : Nat) (ρ : α → β) :
    (rankMotive (α := α) S g c).relabel (Sum.map ρ id) = rankMotive (α := β) S g c := by
  unfold rankMotive
  rw [familyRename] <;> rfl

theorem rankMotiveLift {α : Type} (S : Data) (g : Program 1) (c : Nat) :
    lift (rankMotive (α := α) S g c) = rankMotive (α := α ⊕ Fin 1) S g c :=
  rankMotiveRename S g c Sum.inl

theorem lowerRanksRename {α β : Type} (S : Data) (g : Program 1) (c : Nat)
    (k : OTerm α) (ρ : α → β) :
    (lowerRanks S g c k).relabel ρ = lowerRanks S g c (k.relabel ρ) := by
  unfold lowerRanks
  rw [belowRename,rankMotiveRename]

theorem rankMotiveAt {α : Type} (S : Data) (g : Program 1) (c : Nat) (k : OTerm α) :
    instantiate (rankMotive S g c) (emb k) = rankFamily S g c k := by
  unfold rankMotive
  rw [instantiate,bindEmbedding,familySubst,varBind]

theorem rankMatrixAt {α : Type} (S : Data) (g : Program 1) (c : Nat) (k x : OTerm α) :
    instantiate (rankMatrix S g c k) (emb x) = rankClause S g c k x := by
  unfold rankMatrix
  rw [instantiate,bindEmbedding,clauseSubst,liftBind,varBind]

#print axioms positiveRankRename
#print axioms lowerRanksRename
#print axioms rankMotiveAt
#print axioms rankMatrixAt
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankSyntaxProof
