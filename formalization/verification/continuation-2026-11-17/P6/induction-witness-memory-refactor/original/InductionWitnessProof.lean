module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Continuation20261115 Induction
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnSubst eqnRelabel zSubst sucSubst)
open InternalStrongInduction InternalStrongInductionSyntaxProof
open Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof (implicationRename)

theorem matrixWitness (n : Nat) (fuel node param p2 p3 out raw bound types heads labels tupleBound : OTerm alpha) :
    (matrix n fuel).subst (Sum.elim Term.var (fun i => emb ((![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) i))) =
      (graph2 InternalPairing.pairing node bound fuel ⊓
      graph2 InternalPairing.pairing param types p2 ⊓
      graph2 InternalPairing.pairing p2 heads p3 ⊓
      graph2 InternalPairing.pairing p3 labels tupleBound ⊓
      graph2 (OriginalEnumerationRecursion.enumeration n) out node param).imp ((graph2 contains (numeral 1) out raw).imp (Meaning.holds n raw bound fuel types heads labels tupleBound) ⊓ (Meaning.holds n raw bound fuel types heads labels tupleBound).imp (graph2 contains (numeral 1) out raw)) := by
  have he : (Sum.elim Term.var (fun i => emb ((![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,conjunctionSubst,MeaningSyntaxProof.meaningSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionWitnessProof
