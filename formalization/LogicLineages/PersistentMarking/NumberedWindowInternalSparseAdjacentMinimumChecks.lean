module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumOrderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAdjacentMinimumTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_EdgeMinimumOrder : ExactEdgeMinimumOrder := NumberedWindowInternalSparseAdjacentMinimumOrderProof.order

private theorem unorderedEqual (x y : OTerm α) (left : Derivation body Γ (ltF x y).not)
    (right : Derivation body Γ (ltF y x).not) : Nonempty (Derivation body Γ (eqn x y)) := by
  obtain ⟨comparison⟩ := actualOriginalComparison body α x y
  have split := compareView (weakenClosed comparison Γ)
  let L := ltF x y
  let R := ltF y x
  let M := eqn x y
  have noLeft : Derivation body Γ (L.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp left L) (Derivation.hypothesis List.mem_cons_self)))
  have noRight : Derivation body Γ (R.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp right R) (Derivation.hypothesis List.mem_cons_self)))
  have same : Derivation body Γ (M.imp M) := Derivation.implicationIntroduction
    (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination split noLeft (Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp same (M ⊔ R)) (addHyp noRight (M ⊔ R))))⟩

theorem exact_MutualEdgeMinimumEquality : ExactMutualEdgeMinimumEquality := by
  intro C s baseX W body α Γ ctx ty a b x y
  let X := guardedExchange C s baseX
  let minima := leastGraph C X W s ctx ty a x ⊓ leastGraph C X W s ctx ty b y
  let edges := acceptEdge (edge4 X W) ctx ty a b ⊓ acceptEdge (edge4 X W) ctx ty b a
  let Δ := (minima ⊓ edges) :: Γ
  have h : Derivation body Δ (minima ⊓ edges) := Derivation.hypothesis List.mem_cons_self
  have both := Derivation.conjunctionLeft h
  have arrows := Derivation.conjunctionRight h
  obtain ⟨right⟩ := exact_EdgeMinimumOrder C s baseX W body α Δ ctx ty a b x y
  obtain ⟨left⟩ := exact_EdgeMinimumOrder C s baseX W body α Δ ctx ty b a y x
  have rev := Derivation.conjunctionIntroduction (Derivation.conjunctionRight both) (Derivation.conjunctionLeft both)
  have l := Derivation.implicationElimination left (Derivation.conjunctionIntroduction rev (Derivation.conjunctionRight arrows))
  have r := Derivation.implicationElimination right (Derivation.conjunctionIntroduction both (Derivation.conjunctionLeft arrows))
  obtain ⟨eq⟩ := unorderedEqual x y l r
  exact ⟨Derivation.implicationIntroduction eq⟩

theorem exact_AdjacentInstallation : ExactAdjacentInstallation := by
  obtain ⟨C,cover,tuples⟩ := NumberedWindowInternalSparseCoverInstallationChecks.exact_CoverInstallation
  refine ⟨C,cover,?_⟩
  intro entries s W valid
  obtain ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,hExchange,hCal,typedTuple,precise,chosen,updated,openCover,minEdge,ends,edgeCover⟩ :=
    tuples entries s W valid
  exact ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,windowProg,v,hRoot,hOther,
    hSyntax,hWindow,hBase,hExchange,hCal,typedTuple,precise,chosen,updated,openCover,minEdge,ends,edgeCover,
    exact_EdgeMinimumOrder C s baseX windowProg,exact_MutualEdgeMinimumEquality C s baseX windowProg⟩

#print axioms exact_EdgeMinimumOrder
#print axioms exact_MutualEdgeMinimumEquality
#print axioms exact_AdjacentInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
