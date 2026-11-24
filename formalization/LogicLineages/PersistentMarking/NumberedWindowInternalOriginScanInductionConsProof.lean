module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanCons)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm Zero)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOriginFilterConsCasesProof (exact_OpenOriginFilterConsCases)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep rowCell)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename exact_OpenOriginScanRoutedHead)
open NumberedWindowInternalOriginScanInductionTargets
open NumberedWindowInternalOriginScanInductionSyntaxProof
  (atRowsRename filterRename goalRename applyAtRows renamePools)
open NumberedWindowInternalOriginScanInductionConsTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem saveCell (code row tail : OTerm α) (d : D B Γ (rowCell code row tail))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (rowCell (code.relabel j) (row.relabel j) (tail.relabel j)) := by
  have h := renameInto d j Δ keep
  rw [show (rowCell code row tail).relabel j =
    rowCell (code.relabel j) (row.relabel j) (tail.relabel j) from consGraphRename code row tail j] at h
  exact h

private theorem saveRow (r : Program 3) (row removed : OTerm α)
    (d : D B Γ (rowAccept r row removed)) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (rowAccept r (row.relabel j) (removed.relabel j)) := by
  simpa only [rowAccept,programRename,binaryInputsRename,oneTerm,NumberedWindowInternalDirectInsertedRowTargets.Zero,sucRelabel,zRelabel]
    using renameInto d j Δ keep

private theorem saveLoop (r : Program 3) (rows removed : OTerm α)
    (d : D B Γ (loopAccept r rows removed)) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (loopAccept r (rows.relabel j) (removed.relabel j)) := by
  simpa only [loopRename] using renameInto d j Δ keep

private theorem saveFilter (side : Bool) (out rows pool : OTerm α)
    (d : D B Γ (filterGraph side out rows pool)) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (filterGraph side (out.relabel j) (rows.relabel j) (pool.relabel j)) := by
  simpa only [filterRename] using renameInto d j Δ keep

private theorem saveStep (side : Bool) (out row rest pool : OTerm α)
    (d : D B Γ (programGraph (rowStep side) out ![row,rest,pool])) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (programGraph (rowStep side) (out.relabel j)
      ![row.relabel j,rest.relabel j,pool.relabel j]) := by
  simpa only [programRename,tripleInputsRename] using renameInto d j Δ keep

private theorem saveLaw (r : Program 3) (rows removed rawL rawR pool : OTerm α)
    (d : D B Γ (atRows r rows removed rawL rawR pool)) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D B Δ (atRows r (rows.relabel j) (removed.relabel j)
      (rawL.relabel j) (rawR.relabel j) (pool.relabel j)) := by
  simpa only [atRowsRename] using renameInto d j Δ keep

/-- A real input cons yields the old head check and old tail scan. Open
the two literal filter graphs on this same cons, instantiate the
inherited object invariant at their genuine tail results, and then
route and rebuild the original check at the two new outputs. -/
theorem exact_OpenOriginScanInductionCons : ExactOpenOriginScanInductionCons := by
  intro r B α Γ rows row tail removed decoded rawL rawR scratchL scratchR joined outL outR
    pool cell inherited original filterL filterR
  obtain ⟨acceptedParts⟩ := exactOpenScanCons r B α Γ rows row tail removed cell original
  have headChecked : D B Γ (rowAccept r row removed) := ⟨Derivation.conjunctionLeft acceptedParts⟩
  have acceptedTail : D B Γ (loopAccept r tail removed) := ⟨Derivation.conjunctionRight acceptedParts⟩
  apply exact_OpenOriginFilterConsCases true B α Γ rows row tail scratchL outL
    (goalAt r rawL rawR outL outR) cell filterL
  intro β j Δ restL keep priorL stepL
  rw [goalRename]
  let n := rows.relabel j
  let h := row.relabel j
  let t := tail.relabel j
  let o := removed.relabel j
  let o' := decoded.relabel j
  let l := rawL.relabel j
  let rr := rawR.relabel j
  let sl := scratchL.relabel j
  let sr := scratchR.relabel j
  let a := joined.relabel j
  let x := outL.relabel j
  let y := outR.relabel j
  have pool' := renamePools pool j keep
  have cell' := saveCell rows row tail cell j keep
  have filterR' := saveFilter false outR rows scratchL filterR j keep
  have head' := saveRow r row removed headChecked j keep
  have tail' := saveLoop r tail removed acceptedTail j keep
  have law' := saveLaw r tail removed rawL rawR scratchL inherited j keep
  apply exact_OpenOriginFilterConsCases false B β Δ n h t sl y (goalAt r l rr x y) cell' filterR'
  intro γ k Ω restR keep' priorR stepR
  rw [goalRename]
  have inherited'' := saveLaw r t o l rr sl law' k keep'
  have originalTail := saveLoop r t o tail' k keep'
  have tailLeft := saveFilter true restL t sl priorL k keep'
  have tails := applyAtRows r (t.relabel k) (o.relabel k) (l.relabel k) (rr.relabel k)
    (sl.relabel k) (restL.relabel k) restR inherited'' originalTail tailLeft priorR
  obtain ⟨tails⟩ := tails
  have head'' := saveRow r h o head' k keep'
  have stepL'' := saveStep true x h restL sl stepL k keep'
  have finalPool := renamePools pool' k keep'
  exact exact_OpenOriginScanRoutedHead r B γ Ω (o.relabel k) (o'.relabel k)
    (h.relabel k) (l.relabel k) (rr.relabel k) (sl.relabel k) (sr.relabel k) (a.relabel k)
    (restL.relabel k) restR (x.relabel k) (y.relabel k)
    head'' finalPool.oldParsed finalPool.leftParsed finalPool.rightParsed finalPool.count finalPool.appended
    ⟨Derivation.conjunctionLeft tails⟩ ⟨Derivation.conjunctionRight tails⟩ stepL'' stepR

#print axioms exact_OpenOriginScanInductionCons

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsProof
