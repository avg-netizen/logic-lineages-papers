module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericListMatrixSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof InternalStrongInductionSyntaxProof
open InternalApplicationResultStackCompositionSyntaxProof (graph1Subst)
open InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Lists
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem allSubst {beta : Type} (n : Nat) (list bound fuel types heads labels tupleBound : OTerm alpha) (ts : alpha → OTerm beta) :
    (Characterizes n list bound fuel types heads labels tupleBound).subst (fun a => emb (ts a)) = Characterizes n (list.subst ts) (bound.subst ts) (fuel.subst ts) (types.subst ts) (heads.subst ts) (labels.subst ts) (tupleBound.subst ts) := by
  apply GenericListMatrixSyntaxProof.allSubst contains list ts
  rw [MeaningSyntaxProof.meaningSubst]
  rw [InternalRecursionGraphSyntaxProof.liftSubst,
    InternalRecursionGraphSyntaxProof.liftSubst, InternalRecursionGraphSyntaxProof.liftSubst,
    InternalRecursionGraphSyntaxProof.liftSubst, InternalRecursionGraphSyntaxProof.liftSubst,
    InternalRecursionGraphSyntaxProof.liftSubst]


theorem allRename {beta : Type} (n : Nat) (list bound fuel types heads labels tupleBound : OTerm alpha) (j : alpha → beta) :
    (Characterizes n list bound fuel types heads labels tupleBound).relabel j = Characterizes n (list.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Characterizes n list bound fuel types heads labels tupleBound).subst (fun a => emb (.var (j a))) = _
  rw [allSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (list bound fuel types heads labels tupleBound raw : OTerm alpha) :
    (matrix n list bound fuel types heads labels tupleBound).subst (Sum.elim Term.var (fun _ : Fin 1 => emb raw)) =
      ((graph2 contains (numeral 1) list raw).imp (Meaning.holds n raw bound fuel types heads labels tupleBound) ⊓
       (Meaning.holds n raw bound fuel types heads labels tupleBound).imp (graph2 contains (numeral 1) list raw)) := by
  apply GenericListMatrixSyntaxProof.witness contains list raw
  rw [MeaningSyntaxProof.meaningSubst]
  rw [InternalRecursionGraphSyntaxProof.witnessLift,
    InternalRecursionGraphSyntaxProof.witnessLift, InternalRecursionGraphSyntaxProof.witnessLift,
    InternalRecursionGraphSyntaxProof.witnessLift, InternalRecursionGraphSyntaxProof.witnessLift,
    InternalRecursionGraphSyntaxProof.witnessLift]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListSyntaxProof
