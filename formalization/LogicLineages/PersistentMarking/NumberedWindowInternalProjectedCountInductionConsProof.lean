module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOriginFilterConsCasesProof (exact_OpenOriginFilterConsCases)
open NumberedWindowInternalOriginScanInductionSyntaxProof (filterRename)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets
open NumberedWindowInternalProjectedCountInductionSyntaxProof
  (atRowsRename comparedRename matrixReportRename)
open NumberedWindowInternalProjectedCountRowStepTargets (RowStepReports)
open NumberedWindowInternalProjectedCountRowStepProof (exact_OpenProjectedCountRowStep)
open NumberedWindowInternalProjectedCountInductionConsTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem separate {code pool fl fr p pl pr joined : OTerm α}
    (h : D B Γ (reportMatrix code pool fl fr p pl pr joined)) :
    D B Γ (filterGraph true fl code pool) ∧ D B Γ (filterGraph false fr code pool) ∧
      D B Γ (project p code) ∧ D B Γ (project pl fl) ∧ D B Γ (project pr fr) ∧
      D B Γ (NumberedWindowInternalScratchAppendOpenTargets.appendGraph joined pl pr) := by
  obtain ⟨h⟩ := h
  have p1 := Derivation.conjunctionRight h
  have p2 := Derivation.conjunctionRight p1
  have p3 := Derivation.conjunctionRight p2
  have p4 := Derivation.conjunctionRight p3
  exact ⟨⟨Derivation.conjunctionLeft h⟩,⟨Derivation.conjunctionLeft p1⟩,
    ⟨Derivation.conjunctionLeft p2⟩,⟨Derivation.conjunctionLeft p3⟩,
    ⟨Derivation.conjunctionLeft p4⟩,⟨Derivation.conjunctionRight p4⟩⟩

theorem exact_OpenProjectedCountInductionCons : ExactOpenProjectedCountInductionCons := by
  intro left right B α Γ code row tail pool fl fr p pl pr joined cell ih obs
  have fs := separate obs
  apply exact_OpenOriginFilterConsCases true B α Γ code row tail pool fl
    (compared p joined) cell fs.1
  intro β j Δ tl keep preL callL
  rw [comparedRename]
  let n := code.relabel j
  let h := row.relabel j
  let t := tail.relabel j
  let pool' := pool.relabel j
  let l := fl.relabel j
  let r := fr.relabel j
  let map := p.relabel j
  let ml := pl.relabel j
  let mr := pr.relabel j
  let ap := joined.relabel j
  have cell' := renameInto cell j Δ keep
  rw [consGraphRename] at cell'
  have fs' := renameInto obs j Δ keep
  rw [matrixReportRename] at fs'
  have ih' := renameInto ih j Δ keep
  rw [atRowsRename] at ih'
  apply exact_OpenOriginFilterConsCases false B β Δ n h t pool' r
    (compared map ap) cell' (separate fs').2.1
  intro γ k Ω tr keep' preR callR
  rw [comparedRename]
  have cell'' := renameInto cell' k Ω keep'
  rw [consGraphRename] at cell''
  have fs'' := renameInto fs' k Ω keep'
  rw [matrixReportRename] at fs''
  obtain ⟨_,_,rootMap,leftMap,rightMap,append⟩ := separate fs''
  have ih'' := renameInto ih' k Ω keep'
  rw [atRowsRename] at ih''
  have preL' := renameInto preL k Ω keep'
  rw [filterRename] at preL'
  have callL' := renameInto callL k Ω keep'
  simp only [programRename,tripleInputsRename] at callL'
  have inputs : RowStepReports B Ω (n.relabel k) (h.relabel k) (t.relabel k)
      (pool'.relabel k) (tl.relabel k) tr (l.relabel k) (r.relabel k)
      (map.relabel k) (ml.relabel k) (mr.relabel k) (ap.relabel k) :=
    ⟨cell'',preL',preR,callL',callR,rootMap,leftMap,rightMap,append,ih''⟩
  exact exact_OpenProjectedCountRowStep left right B γ Ω (n.relabel k) (h.relabel k)
    (t.relabel k) (pool'.relabel k) (tl.relabel k) tr (l.relabel k) (r.relabel k)
    (map.relabel k) (ml.relabel k) (mr.relabel k) (ap.relabel k) inputs

#print axioms exact_OpenProjectedCountInductionCons

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsProof
