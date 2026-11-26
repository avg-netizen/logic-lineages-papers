module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppend (append)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
open PrimaryExpansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem expansionSoundness (E : Program 3) (pool reached parameter out candidate : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (expand E) out pool reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached candidate ⊔
      (graph2 contains (numeral 1) pool candidate ⊓ sourceWitness E reached candidate parameter))) := by
  let xs : Fin 3 → OTerm alpha := ![pool,reached,parameter]
  apply programCases (filterReached E) xs _
  intro beta j Theta filtered hj hf
  simp only [AppendSyntaxProof.orRename,conjunctionRename,graph2Rename,numeral,sucRelabel,zRelabel,WitnessProof.witnessRename]
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hm'
  let ys : Fin 3 → OTerm beta := ![pool.relabel j,reached.relabel j,parameter.relabel j]
  have hxs : (fun i => (xs i).relabel j) = ys := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  have hf' : Nonempty (Derivation body Theta (programGraph (filterReached E) filtered ys)) := by
    rw [hxs] at hf
    exact hf
  have ha := binaryRecover append (.projection 1) (filterReached E) (out.relabel j)
    (reached.relabel j) filtered ys he' (projectionValue 1 ys) hf'
  obtain ⟨hd⟩ := AppendProof.appendSoundness body beta Theta (reached.relabel j) filtered
    (out.relabel j) (candidate.relabel j) ha hm'
  let A := graph2 contains (numeral 1) filtered (candidate.relabel j)
  obtain ⟨hfilter⟩ := FilterProof.filterSoundness E body beta (A :: Theta)
    (pool.relabel j) (reached.relabel j) (parameter.relabel j) filtered (candidate.relabel j)
    (withHyp hf' A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hw⟩ := AnyProof.anyWitness E body beta (A :: Theta) (reached.relabel j)
    (candidate.relabel j) (parameter.relabel j) ⟨Derivation.conjunctionRight hfilter⟩
  exact ⟨disjunctionElimination hd
    (Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (orRight
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hfilter) hw)))⟩

theorem newBranch (E : Program 3) (pool reached parameter out candidate : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (expand E) out pool reached parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate)))
    (hw : Nonempty (Derivation body Delta (sourceWitness E reached candidate parameter))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  apply WitnessProof.casesWitness E reached candidate parameter _ hw
  intro beta j Theta source hj hm hedge
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
  exact PrimaryEdgeInclusion.Proof.expansionEdgeInclusion E body beta Theta (pool.relabel j)
    (reached.relabel j) source (candidate.relabel j) (parameter.relabel j) (out.relabel j)
    hm hp' hedge he'

theorem expansionCharacterization : Targets.ExpansionCharacterization := by
  intro E body alpha Delta pool reached parameter out candidate he
  constructor
  · exact expansionSoundness E pool reached parameter out candidate he
  · intro hd
    let A := graph2 contains (numeral 1) reached candidate
    let B := graph2 contains (numeral 1) pool candidate ⊓ sourceWitness E reached candidate parameter
    obtain ⟨hl⟩ := PrimaryExpansion.PreservationProof.internalPreservation E body alpha (A :: Delta)
      pool reached parameter out candidate (withHyp he A) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hh : Derivation body (B :: Delta) B := Derivation.hypothesis List.mem_cons_self
    obtain ⟨hr⟩ := newBranch E pool reached parameter out candidate (withHyp he B)
      ⟨Derivation.conjunctionLeft hh⟩ ⟨Derivation.conjunctionRight hh⟩
    obtain ⟨hd⟩ := hd
    exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
      (Derivation.implicationIntroduction hr)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
