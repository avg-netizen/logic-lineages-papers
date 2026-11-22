module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoClampProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (moveStoredK)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets (NumberedOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnScratchProof (exact_OpenSelectedGrammarNumberedScratch)
open NumberedWindowInternalCoverNumberedMeasureSelectedCutProof (exact_OpenCoverNumberedMeasureCut)
open NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof (exact_OpenNumberedJoinFromFields)
open NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof (numberedBoundCases)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverNumberedTypeWindowSelectedProof (exact_OpenCoverNumberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets (ArgumentHit)
open NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof (moveArgumentHit)
open NumberedWindowInternalCoverArgumentMemoClampProof (exact_OpenCoverArgumentMemoClamp)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualMeasuredNumberedLists (V TV M F : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (h ty k l r p vertices ctx result ml dl wl ls lt la mr dr wr rs rt ra : OTerm α)
    (row : ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (numberedTerm h ty k l r) p vertices ctx result)
    (left : Nonempty (Derivation body Γ (unary (argumentMeasure F) ml l)))
    (lp : Nonempty (Derivation body Γ (codePair ml dl wl)))
    (leftHit : ArgumentHit s body Γ dl wl ls lt la l)
    (right : Nonempty (Derivation body Γ (unary (argumentMeasure F) mr r)))
    (rp : Nonempty (Derivation body Γ (codePair mr dr wr)))
    (rightHit : ArgumentHit s body Γ dr wr rs rt ra r) :
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r))) := by
  let A := argumentMeasure F
  let P := lexicalFittedPrograms s V TV M A B T
  let L := lambdaLexicalBase s B T
  let Q := memberGraph vertices (numberedTerm h ty k l r)
  have head := exact_OpenCoverHeadFittedWindow true s (numberedTypeBase s L) T
    body α Γ ctx h result [ty,k,l,r] rfl row.typed
  have stored := exact_OpenCoverNumberedTypeWindow s L T body α Γ ctx h ty k l r result row.typed
  have a := exact_OpenCoverArgumentMemoClamp F body α Γ l ml left
  have b := exact_OpenCoverArgumentMemoClamp F body α Γ r mr right
  have cut := exact_OpenCoverNumberedMeasureCut M A body α Γ h ty k l r p row.parent.measured
  have joined := exact_OpenNumberedJoinFromFields A h ty k l r p ml mr cut a b
  apply numberedBoundCases k ml mr dl dr wl wr p Q lp rp joined
  intro β j Δ width keep actual
  have hh := renameInto head j Δ keep
  simp only [graphRename,headsTerm,numeralRename] at hh
  have kt := moveStoredK s j keep ty stored
  have parent := moveParent P.V P.R s j keep row.parent
  rw [numberedRename] at parent
  have f := moveArgumentHit s dl wl ls lt la l j Δ keep leftHit
  have e := moveArgumentHit s dr wr rs rt ra r j Δ keep rightHit
  let depth := add (dl.relabel j) (dr.relabel j)
  let R := selectedMeasure P.R
  have input : NumberedOwnInputs P.V R s body Δ (p.relabel j) depth width
      (dl.relabel j) (wl.relabel j) (ls.relabel j) (lt.relabel j) (la.relabel j)
      (dr.relabel j) (wr.relabel j) (rs.relabel j) (rt.relabel j) (ra.relabel j)
      (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) :=
    ⟨⟨f.scope,f.hit,actual.leftDepth,actual.leftWidth⟩,
     ⟨e.scope,e.hit,actual.rightDepth,actual.rightWidth⟩,
     hh,kt,actual.storedNumeral,parent.valid,parent.measured,actual.parent⟩
  simp only [Q,graphRename,numberedRename]
  exact exact_OpenSelectedGrammarNumberedScratch P.V R s body β Δ (p.relabel j) depth width
    (dl.relabel j) (wl.relabel j) (ls.relabel j) (lt.relabel j) (la.relabel j)
    (dr.relabel j) (wr.relabel j) (rs.relabel j) (rt.relabel j) (ra.relabel j)
    (vertices.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    input parent.held

#print axioms actualMeasuredNumberedLists

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredNumberedListBoundsProof
