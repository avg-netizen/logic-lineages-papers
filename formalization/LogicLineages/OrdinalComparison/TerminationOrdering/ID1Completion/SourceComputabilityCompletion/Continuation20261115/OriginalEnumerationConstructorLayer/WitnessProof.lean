module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open Targets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem componentsSubst {beta : Type} (n : Nat) (xs : Fin 7 → OTerm alpha)
    (ys : Fin 8 → OTerm alpha) (sub : alpha → OTerm beta) :
    (componentGraphs n xs ys).subst (fun a => emb (sub a)) =
      componentGraphs n (fun i => (xs i).subst sub) (fun i => (ys i).subst sub) := by
  simp only [componentGraphs,conjunctionSubst,InternalComputabilityApplicationSyntaxProof.programSubst]

theorem memberSubst {beta : Type} (ys : Fin 8 → OTerm alpha) (code : OTerm alpha) (sub : alpha → OTerm beta) :
    (branchMember ys code).subst (fun a => emb (sub a)) =
      branchMember (fun i => (ys i).subst sub) (code.subst sub) := by
  simp only [branchMember,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,graph2,
    InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem componentsRename {beta : Type} (n : Nat) (xs : Fin 7 → OTerm alpha)
    (ys : Fin 8 → OTerm alpha) (j : alpha → beta) :
    (componentGraphs n xs ys).relabel j = componentGraphs n (fun i => (xs i).relabel j) (fun i => (ys i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (componentGraphs n xs ys).subst (fun a => emb (.var (j a))) = _
  rw [componentsSubst]
  simp only [← termRelabelAsSubst]

theorem memberRename {beta : Type} (ys : Fin 8 → OTerm alpha) (code : OTerm alpha) (j : alpha → beta) :
    (branchMember ys code).relabel j = branchMember (fun i => (ys i).relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (branchMember ys code).subst (fun a => emb (.var (j a))) = _
  rw [memberSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) (ys : Fin 8 → OTerm alpha) :
    (witnessMatrix n xs code).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      componentGraphs n xs ys ⊓ branchMember ys code := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold witnessMatrix
  rw [he,conjunctionSubst,componentsSubst,memberSubst]
  simp only [InternalRecursionGraphSyntaxProof.witnessLift,Term.subst,Sum.elim_inr]

theorem witnessSubst {beta : Type} (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) (sub : alpha → OTerm beta) :
    (InternalFiniteBlocks.block (witnessMatrix n xs code)).subst (fun a => emb (sub a)) =
      InternalFiniteBlocks.block (witnessMatrix n (fun i => (xs i).subst sub) (code.subst sub)) := by
  unfold witnessMatrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,conjunctionSubst,componentsSubst,memberSubst]
  simp only [InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr]

theorem witnessRename {beta : Type} (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) (j : alpha → beta) :
    (InternalFiniteBlocks.block (witnessMatrix n xs code)).relabel j =
      InternalFiniteBlocks.block (witnessMatrix n (fun i => (xs i).relabel j) (code.relabel j)) := by
  rw [formulaRelabelAsSubst]
  change (InternalFiniteBlocks.block (witnessMatrix n xs code)).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (componentGraphs n xs ys ⊓ branchMember ys code))) :
    Nonempty (Derivation body Delta (InternalFiniteBlocks.block (witnessMatrix n xs code))) := by
  apply InternalFiniteBlocksProof.introduction body alpha 8 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
