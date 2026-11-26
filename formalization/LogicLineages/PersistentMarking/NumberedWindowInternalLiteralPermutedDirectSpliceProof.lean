module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawBoundaryIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectSpliceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser renameUnit)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectBoundaryGuardsTargets
open NumberedWindowInternalDirectBoundaryOpenProof (exact_OpenRawGuards)
open NumberedWindowInternalDirectRawBoundaryIntroProof (exact_OriginalRawBoundaryFromReports)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalConsUnionReportBuildProof (unionReportOfGraphs)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
attribute [local irreducible] programGraph

abbrev sourceOK {α : Type} (a k d : OTerm α) : Formula α :=
  programGraph (rawSourceCheck (observePartition permutation)) (suc z) (sourceTape a k d)

abbrev compare {α : Type} (a b : OTerm α) : Formula α :=
  programGraph permutation (suc z) ![a,b]

private theorem fromDecoded (new old kept removed a b s k d : OTerm α)
    (newParse : D B Γ (unary parser (suc a) new))
    (oldParse : D B Γ (unary parser (suc b) old))
    (same : D B Γ (compare a b))
    (original : ParsedTriplet B Γ old kept removed s k d)
    (count : D B Γ (programGraph (observePartition permutation) (suc z) (sourceTape s k d))) :
    D B Γ (sourceOK new kept removed) := by
  apply exact_OpenSourcePartitionAppend permutation s k d _ count
  intro β j Δ joined keep appended held
  change D B Δ ((programGraph (rawSourceCheck (observePartition permutation)) (suc z)
    (sourceTape new kept removed)).relabel j)
  -- Only the source coordinate is changed; kept and removed reports remain literal.
  have np := renameParser new a newParse j Δ keep
  have op := renameParser old b oldParse j Δ keep
  have os := renameParser old s original.source j Δ keep
  have kp := renameParser kept k original.kept j Δ keep
  have dp := renameParser removed d original.removed j Δ keep
  obtain ⟨eq⟩ := valueUnique parser (suc (s.relabel j)) (suc (b.relabel j)) ![old.relabel j] os op
  have aligned := headTransport permutation (suc z) (s.relabel j) (b.relabel j)
    (Fin.cons joined Fin.elim0) ⟨cancelSuc eq⟩ held
  have carried := renamePair permutation (suc z) a b same j keep
  simp only [sucRelabel,zRelabel] at carried
  have observed := exact_LiteralObserverTransitivity (a.relabel j) (b.relabel j) joined carried aligned
  have newProof := unionReportOfGraphs permutation (kept.relabel j) (removed.relabel j)
    (new.relabel j) (k.relabel j) (d.relabel j) (a.relabel j) joined ⟨np,kp,dp⟩ appended observed
  -- The helper supplies the original raw checker; unfold only its tape relabel.
  simpa only [NumberedWindowInternalCertifiedUnionStepProof.unionGraph,ID1Completion.InternalControlGraphSupportProof.programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,sucRelabel,zRelabel] using newProof

/-- Substitute a correctly parsed, count-equivalent source into the
actual direct checker's source observer. The removed and kept raw
inputs and their decoded ordered append are unchanged. -/
theorem exact_LiteralRawSourceSplice (new old kept removed a b : OTerm α)
    (newParse : D B Γ (unary parser (suc a) new))
    (oldParse : D B Γ (unary parser (suc b) old))
    (same : D B Γ (compare a b)) (held : D B Γ (sourceOK old kept removed)) :
    D B Γ (sourceOK new kept removed) := by
  apply exact_OpenRawSourceDecode (observePartition permutation) B α Γ old kept removed _ held
  intro β j Δ s k d keep parsed count
  have comp := renamePair permutation (suc z) a b same j keep
  simp only [sucRelabel,zRelabel] at comp
  have h := fromDecoded (new.relabel j) (old.relabel j) (kept.relabel j) (removed.relabel j)
    (a.relabel j) (b.relabel j) s k d (renameParser new a newParse j Δ keep)
    (renameParser old b oldParse j Δ keep) comp parsed count
  simpa only [ID1Completion.InternalControlGraphSupportProof.programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,sucRelabel,zRelabel] using h

/-- Replace just the source-side parser and scalar report in the real
boundary; the old accepted target and nonempty removal remain intact. -/
theorem exact_LiteralRawBoundarySplice (i : Program 1) (new old target removed a : OTerm α)
    (newParse : D B Γ (unary parser (suc a) new))
    (newTyped : D B Γ (unary (typedScratch i) (suc z) a))
    (held : D B Γ (programGraph (boundaryRaw i) (suc z) (sourceTape old target removed))) :
    D B Γ (programGraph (boundaryRaw i) (suc z) (sourceTape new target removed)) := by
  apply exact_OpenRawGuards i B α Γ old target removed _ held
  intro β j Δ _ t d head tail keep h
  have moved := renameInto newTyped j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at moved
  have p : BoundaryReports B Δ (new.relabel j) (target.relabel j) (removed.relabel j)
      (a.relabel j) t d head tail i :=
    ⟨⟨renameParser new a newParse j Δ keep,h.parsed.kept,h.parsed.removed⟩,
      moved,h.targetTyped,h.removedCons⟩
  have actual := exact_OriginalRawBoundaryFromReports i (new.relabel j) (target.relabel j)
    (removed.relabel j) (a.relabel j) t d head tail p
  simpa only [ID1Completion.InternalControlGraphSupportProof.programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,sucRelabel,zRelabel] using actual

#print axioms exact_LiteralRawSourceSplice
#print axioms exact_LiteralRawBoundarySplice
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectSpliceProof
