module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.FieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.AllSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions
open InternalAdditionLawsProof (impSubst)
open OriginalExchangeBoundsPreservation.ExchangeInductionSyntaxProof (graphOneSubst graphTwoSubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalGraphCompositionSyntaxProof InternalRawListRecursionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof
open InternalStrongInduction InternalStrongInductionSyntaxProof
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureSubst closureRename)
open FieldsSyntaxProof
theorem allSubst (C : Program 1) (E : Program 2) (raw : OTerm alpha) {beta : Type} (ts : alpha → OTerm beta) :
    (allSchema C E raw).subst (fun a => emb (ts a)) = allSchema C E (raw.subst ts) := by
  unfold allSchema matrixSchema
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSubst,graphTwoSubst,sucSubst,zSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (AtRaw n arity raw).relabel j = AtRaw n arity (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allSchema _ _ raw).subst (fun a => emb (.var (j a))) = _
  rw [allSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness (C : Program 1) (E : Program 2)
    (source target node rev window symbols types : OTerm alpha) :
    (matrixSchema C E source).subst (Sum.elim Term.var (fun i => emb (![target,node,rev,window,symbols,types] i))) =
      (fieldsSchema C E source target node rev window symbols types).imp (graph2 E (suc z) rev window) := by
  have he : (Sum.elim Term.var (fun i => emb (![target,node,rev,window,symbols,types] i))) =
      (fun a => emb (Sum.elim Term.var ![target,node,rev,window,symbols,types] a)) := by
    funext a; cases a <;> rfl
  unfold matrixSchema
  rw [he]
  simp only [impSubst,fieldsSubst,graphTwoSubst,sucSubst,zSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.AllSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.AllSyntaxProof
