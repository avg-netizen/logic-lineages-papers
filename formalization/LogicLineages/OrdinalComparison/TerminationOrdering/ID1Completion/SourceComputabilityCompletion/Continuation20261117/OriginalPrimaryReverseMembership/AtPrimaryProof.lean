module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.PrimaryRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AtPrimaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn z sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem member (T P : Program 2) (E : Program 3)
 (seed parameter pool out carrier candidate : OTerm alpha)
 (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 P pool seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) out seed parameter)))
 (hseed : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool seed)))
 (hb : Nonempty (Derivation body Delta (backClosed E pool carrier parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)))
 (hcand : Nonempty (Derivation body Delta (graph2 contains (numeral 1) carrier candidate))) :
 Nonempty (Derivation body Delta (graph2 contains (numeral 1) carrier seed)) := by
 apply programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta count hj hc
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hc
 have had' := renameInto had j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at had'
 have hp' := renameInto hp j Theta hj
 rw [graph2Rename] at hp'
 have hl' := renameInto hl j Theta hj
 rw [graph2Rename] at hl'
 have hseed' := renameInto hseed j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hseed'
 have hb' := renameInto hb j Theta hj
 rw [SyntaxProof.backClosedRename] at hb'
 have hm' := renameInto hm j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
 have hcand' := renameInto hcand j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcand'
 have hr := PrimaryRunProof.recover T P E (seed.relabel j) (parameter.relabel j) (pool.relabel j) (out.relabel j) count had' hp' hl' hc
 have hall := RunProof.preserved E count (pool.relabel j) (seed.relabel j) (parameter.relabel j) (out.relabel j) (carrier.relabel j) hr hseed' hb'
 have ha := InvariantProof.eliminate (pool.relabel j) (carrier.relabel j) (seed.relabel j) (out.relabel j) (candidate.relabel j) hall hm'
 obtain ⟨himp⟩ := andRight ha
 obtain ⟨hcand'⟩ := hcand'
 exact ⟨Derivation.implicationElimination himp hcand'⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AtPrimaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AtPrimaryProof
