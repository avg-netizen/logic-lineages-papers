module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel z zRelabel suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (seenWitness)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundZero exact_OpenRoundSuccessor)
open NumberedWindowInternalSparseRoundReachChecks (exact_SeedRoundZero)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseFilterCompletenessChecks (exact_ScannedMemberRetention)
open NumberedWindowInternalSparseScanWitnessChecks (exact_OpenScanWitnessEquivalence)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseRoundOriginWitnessProof
open NumberedWindowInternalSparseRoundOriginTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem initialEquality (paid : ExactRetainedPredecessor) (E : Program 4)
    (out vertices ctx ty seed k : OTerm α)
    (run : Nonempty (Derivation body Γ (roundGraph E out z vertices ctx ty seed)))
    (hit : Nonempty (Derivation body Γ (memberGraph out k))) : Nonempty (Derivation body Γ (eqn seed k)) := by
  apply programCases consCode ![seed,z] _
  intro β j Δ singleton keep cell
  rw [eqnRelabel]
  rw [binaryInputsRename,zRelabel] at cell
  have rr := renameInto run j Δ keep
  have kk := renameInto hit j Δ keep
  rw [roundRename,zRelabel] at rr
  rw [graphRename] at kk
  obtain ⟨rule⟩ := exact_OpenRoundZero E body β Δ (out.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) singleton
  obtain ⟨c⟩ := cell
  obtain ⟨rr⟩ := rr
  obtain ⟨kk⟩ := kk
  have pass := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination rule c)) rr
  obtain ⟨prior⟩ := paid (constantZero 4) body β Δ (vertices.relabel j) singleton (ctx.relabel j)
    (ty.relabel j) (out.relabel j) (k.relabel j)
  exact singletonOrigin singleton (seed.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j) ⟨c⟩
    (Derivation.implicationElimination prior (Derivation.conjunctionIntroduction pass kk))

theorem exact_ZeroRoundOrigin : ExactZeroRoundOrigin := by
  intro paid E body α Γ out vertices ctx ty seed k
  let R := roundGraph E out z vertices ctx ty seed
  let B := memberGraph out k
  let A := memberGraph vertices seed ⊓ eqn seed k
  have run : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  have hit : Derivation body (B :: R :: Γ) B := Derivation.hypothesis List.mem_cons_self
  obtain ⟨eq⟩ := initialEquality paid E out vertices ctx ty seed k ⟨addHyp run B⟩ ⟨hit⟩
  obtain ⟨atSeed⟩ := moveMember out k seed (symm eq) hit
  obtain ⟨zero⟩ := exact_SeedRoundZero E body α (R :: Γ) out vertices ctx ty seed
  have both := Derivation.implicationElimination zero run
  have src := Derivation.implicationElimination (addHyp (Derivation.conjunctionRight both) B) atSeed
  have original : Derivation body (A :: R :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have inOut := Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft both) A)
    (Derivation.conjunctionLeft original)
  obtain ⟨result⟩ := moveMember out seed k (Derivation.conjunctionRight original) inOut
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction src eq))
    (Derivation.implicationIntroduction result))⟩

theorem exact_SuccessorRoundOrigin : ExactSuccessorRoundOrigin := by
  intro paid E body α Γ before after fuel vertices ctx ty seed k
  let R := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let B := memberGraph after k
  let A := memberGraph vertices k ⊓ seenWitness E before ctx ty k
  have rr : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  obtain ⟨law⟩ := exact_OpenRoundSuccessor E body α (R :: Γ) after fuel vertices ctx ty seed before
  have pass := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination law (Derivation.conjunctionLeft rr)))
    (Derivation.conjunctionRight rr)
  have hit : Derivation body (B :: R :: Γ) B := Derivation.hypothesis List.mem_cons_self
  have data := Derivation.conjunctionIntroduction (addHyp pass B) hit
  obtain ⟨source⟩ := exact_DirectedPassInclusion E body α (B :: R :: Γ) after vertices before ctx ty k
  obtain ⟨pred⟩ := paid E body α (B :: R :: Γ) vertices before ctx ty after k
  have forward := Derivation.conjunctionIntroduction (Derivation.implicationElimination source data)
    (Derivation.implicationElimination pred data)
  have origin : Derivation body (A :: R :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨tested⟩ := exact_OpenScanWitnessEquivalence E body α (A :: R :: Γ) before ctx ty k
  have sc := Derivation.implicationElimination (Derivation.conjunctionRight tested) (Derivation.conjunctionRight origin)
  obtain ⟨retain⟩ := exact_ScannedMemberRetention E body α (A :: R :: Γ) after vertices before ctx ty k
  have reverse := Derivation.implicationElimination retain (Derivation.conjunctionIntroduction (addHyp pass A)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft origin) sc))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction reverse))⟩

#print axioms exact_ZeroRoundOrigin
#print axioms exact_SuccessorRoundOrigin
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
