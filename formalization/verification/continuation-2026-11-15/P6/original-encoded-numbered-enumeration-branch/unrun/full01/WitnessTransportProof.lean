module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open Targets WitnessProof
attribute [local irreducible] programGraph

theorem witnessSubst {alpha beta : Type} (n : Nat)
    (labels heads types bases tuples extras code : OTerm alpha) (sub : alpha → OTerm beta) :
    (InternalFiniteBlocks.block (witnessMatrix n labels heads types bases tuples extras code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (witnessMatrix n (labels.subst sub) (heads.subst sub) (types.subst sub)
      (bases.subst sub) (tuples.subst sub) (extras.subst sub) (code.subst sub)) := by
  unfold witnessMatrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem witnessRename {alpha beta : Type} (n : Nat)
    (labels heads types bases tuples extras code : OTerm alpha) (j : alpha → beta) :
    (InternalFiniteBlocks.block (witnessMatrix n labels heads types bases tuples extras code)).relabel j =
    InternalFiniteBlocks.block (witnessMatrix n (labels.relabel j) (heads.relabel j) (types.relabel j)
      (bases.relabel j) (tuples.relabel j) (extras.relabel j) (code.relabel j)) := by
  rw [formulaRelabelAsSubst]
  change (InternalFiniteBlocks.block (witnessMatrix n labels heads types bases tuples extras code)).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessTransportProof
