module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem expansion (T P : Program 2) (E : Program 3)
    (seed parameter sourcePool sourceOut targetPool first : OTerm alpha)
    (had : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 P sourcePool seed parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (LengthAlignedPrimary.primary T P E) sourceOut seed parameter)))
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetPool sourcePool)))
    (hex : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) first targetPool sourceOut parameter))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included first sourceOut)) := by
  apply introduce first sourceOut
  intro beta j Theta probe hj hm
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at had'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hp'
  have hl' := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hl'
  have hi' := renameInto hi j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hi'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] at hex'
  obtain ⟨hd⟩ := (PrimaryExpansionSoundness.Proof.expansionCharacterization E body beta Theta
    (targetPool.relabel j) (sourceOut.relabel j) (parameter.relabel j) (first.relabel j) probe hex').mp hm
  let A := graph2 contains (numeral 1) (sourceOut.relabel j) probe
  let B := graph2 contains (numeral 1) (targetPool.relabel j) probe ⊓
    PrimaryExpansionSoundness.sourceWitness E (sourceOut.relabel j) probe (parameter.relabel j)
  have hb : Nonempty (Derivation body (B :: Theta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := ClosureWitnessProof.member T P E (seed.relabel j) (parameter.relabel j)
    (sourcePool.relabel j) (sourceOut.relabel j) (targetPool.relabel j) probe
    (withHyp had' B) (withHyp hp' B) (withHyp hl' B) (withHyp hi' B) (andLeft hb) (andRight hb)
  have hlft : Derivation body (A :: Theta) A := Derivation.hypothesis List.mem_cons_self
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hlft) (Derivation.implicationIntroduction hr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosureProof
