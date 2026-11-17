module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.InvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {R : Program 1}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SyntaxProof
theorem fromWitness (E : Program 3) (pool carrier seed reached parameter y : OrdinaryArithmetic.Term alpha)
 (hall : Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed reached)))
 (hback : Nonempty (Derivation body Delta (forwardClosedAt R E pool carrier parameter)))
 (hpool : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool y)))
 (hw : Nonempty (Derivation body Delta (PrimaryExpansionSoundness.sourceWitness E reached y parameter))) :
 Nonempty (Derivation body Delta (acceptedAt R pool carrier seed y)) := by
 apply PrimaryExpansionSoundness.WitnessProof.casesWitness E reached y parameter _ hw
 intro beta j Theta x hj hm he
 rw [acceptedRename]
 have hall' := renameInto hall j Theta hj
 rw [allAcceptedRename] at hall'
 have hback' := renameInto hback j Theta hj
 rw [backClosedRename] at hback'
 have hpool' := renameInto hpool j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hpool'
 have hx := InvariantProof.eliminateAt (pool.relabel j) (carrier.relabel j) (seed.relabel j) (reached.relabel j) x hall' hm
 exact ForwardProof.eliminate E (pool.relabel j) (carrier.relabel j) (parameter.relabel j) x (y.relabel j) hback' hx he

theorem preserved (E : Program 3) (pool carrier seed reached parameter out : OrdinaryArithmetic.Term alpha)
 (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) out pool reached parameter)))
 (hall : Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed reached)))
 (hback : Nonempty (Derivation body Delta (forwardClosedAt R E pool carrier parameter))) :
 Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed out)) := by
 apply InvariantProof.introduce pool carrier seed out
 intro beta j Theta y hj hm
 have he' := renameInto he j Theta hj
 rw [graph3Rename] at he'
 have hall' := renameInto hall j Theta hj
 rw [allAcceptedRename] at hall'
 have hback' := renameInto hback j Theta hj
 rw [backClosedRename] at hback'
 obtain ⟨hd⟩ := PrimaryExpansionSoundness.Proof.expansionSoundness E
   (pool.relabel j) (reached.relabel j) (parameter.relabel j) (out.relabel j) y he' hm
 let A := graph2 contains (numeral 1) (reached.relabel j) y
 let B := graph2 contains (numeral 1) (pool.relabel j) y ⊓ PrimaryExpansionSoundness.sourceWitness E (reached.relabel j) y (parameter.relabel j)
 obtain ⟨ha⟩ := InvariantProof.eliminateAt (pool.relabel j) (carrier.relabel j) (seed.relabel j) (reached.relabel j) y
   (withHyp hall' A) ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hb : Nonempty (Derivation body (B :: Theta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hb'⟩ := fromWitness E (pool.relabel j) (carrier.relabel j) (seed.relabel j) (reached.relabel j) (parameter.relabel j) y
   (withHyp hall' B) (withHyp hback' B) (andLeft hb) (andRight hb)
 exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction ha) (Derivation.implicationIntroduction hb')⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ExpansionProof
