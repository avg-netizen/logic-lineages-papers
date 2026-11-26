module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalStrongInductionSyntaxProof
open Continuation20261114.HeadWindowBooleanRange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PointRange
variable {alpha : Type} {k : Nat}

theorem atSubst {beta : Type} (p : Program k) (xs : Fin k → OTerm alpha) (ts : alpha → OTerm beta) :
    (At p xs).subst (fun a => emb (ts a)) = At p (fun i => (xs i).subst ts) := by
  unfold At PointRange.matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,programSubst,numeral,zSubst,sucSubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem atRename {beta : Type} (p : Program k) (xs : Fin k → OTerm alpha) (j : alpha → beta) :
    (At p xs).relabel j = At p (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (At p xs).subst (fun a => emb (.var (j a))) = _
  rw [atSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (p : Program k) (xs : Fin k → OTerm alpha) (out : OTerm alpha) :
    (PointRange.matrix p xs).subst (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (programGraph p out xs).imp (BooleanValue out) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => out) a)) := by
    funext a
    cases a <;> rfl
  unfold PointRange.matrix
  rw [he]
  simp only [impSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,programSubst,numeral,zSubst,sucSubst,
    witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointSyntaxProof
