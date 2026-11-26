module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open InternalControlGraphSupportProof
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open SourceHeadsFilterAdequacy.InductionSyntaxProof (implicationRename)

theorem closureSubst {beta : Type} (types : OTerm alpha) (ts : alpha → OTerm beta) :
    (ArrowClosed types).subst (fun a => emb (ts a)) = ArrowClosed (types.subst ts) := by
  unfold ArrowClosed closureMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,member,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem closureRename {beta : Type} (types : OTerm alpha) (j : alpha → beta) :
    (ArrowClosed types).relabel j = ArrowClosed (types.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ArrowClosed types).subst (fun a => emb (.var (j a))) = _
  rw [closureSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (types pair left right : OTerm alpha) :
    (closureMatrix types).subst (Sum.elim Term.var (fun i => emb ((![pair,left,right] : Fin 3 → OTerm alpha) i))) =
      (graph2 InternalPairing.pairing pair left right ⊓ member types (suc pair)).imp
        (member types left ⊓ member types right) := by
  have he : (Sum.elim Term.var (fun i => emb ((![pair,left,right] : Fin 3 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![pair,left,right] : Fin 3 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold closureMatrix
  rw [he]
  simp only [impSubst,conjunctionSubst,member,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
