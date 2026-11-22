module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchLeavesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof (exact_OpenSelectedGrammarNamedLeafScratch)
open NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof (exact_OpenSelectedGrammarTypeLeafScratch)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveMemberKey)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem atNamed (P : Programs) (s : Settings) (b : Bool) (raw p vertices ctx result ty i : OTerm α)
    (need : Obligations P s body)
    (row : PackedRow P s body Γ raw (namedTerm b.toNat ty i) p vertices ctx result b.toNat [ty,i]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  apply need.named b α Γ raw p vertices ctx result ty i _ row
  intro β j Δ keep facts
  rw [graphRename]
  obtain ⟨d,width,pair,typedId,bounded⟩ := facts
  have parent := moveParent P.V P.R s j keep row.data.parent
  rw [namedRename] at parent
  have packed := renameInto row.packed j Δ keep
  rw [eqnRelabel,namedRename] at packed
  obtain ⟨packed⟩ := packed
  have hit := exact_OpenSelectedGrammarNamedLeafScratch b P.V (selectedMeasure P.R) s body β Δ
    (p.relabel j) d width (vertices.relabel j) (ty.relabel j) (i.relabel j)
    typedId bounded parent.valid parent.measured pair parent.held
  exact moveMemberKey (vertices.relabel j) (namedTerm b.toNat (ty.relabel j) (i.relabel j))
    (raw.relabel j) (symm packed) hit

theorem atTypeLeaf (P : Programs) (s : Settings) (raw p vertices ctx result ty : OTerm α)
    (need : Obligations P s body)
    (row : PackedRow P s body Γ raw (typeLeafTerm ty) p vertices ctx result 3 [ty]) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  apply need.typeLeaf α Γ raw p vertices ctx result ty _ row
  intro β j Δ keep facts
  rw [graphRename]
  obtain ⟨d,width,pair,hitTy⟩ := facts
  have parent := moveParent P.V P.R s j keep row.data.parent
  rw [termRename] at parent
  have packed := renameInto row.packed j Δ keep
  rw [eqnRelabel,termRename] at packed
  obtain ⟨packed⟩ := packed
  have hit := exact_OpenSelectedGrammarTypeLeafScratch P.V (selectedMeasure P.R) s body β Δ
    (p.relabel j) d width (vertices.relabel j) (ty.relabel j)
    hitTy parent.valid parent.measured pair parent.held
  exact moveMemberKey (vertices.relabel j) (typeLeafTerm (ty.relabel j)) (raw.relabel j) (symm packed) hit

#print axioms atNamed
#print axioms atTypeLeaf

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchLeavesProof
