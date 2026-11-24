module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSelectedMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedPackedMinimumProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalScratchInclusionThinProof (included eliminate)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open NumberedWindowInternalThinPrefixedRoundsChecks (exact_RoundsInUpper)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalThinPackedSelectedMinimumProof (selected)
open NumberedWindowInternalSparsePackedBoundChecks (exact_OpenPackedLeastLowerBound)

private theorem unorderedEqual {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (x y : OTerm α) (left : Derivation body Γ (ltF x y).not)
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

private theorem intoUpper (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (vertices ctx ty seed upper later fuel pool : OTerm α)
    (seen : Derivation body Γ (memberGraph upper seed))
    (closed : Derivation body Γ (prefixed E vertices ctx ty upper later))
    (tape : Derivation body Γ (roundGraph E pool fuel vertices ctx ty seed)) :
    Nonempty (Derivation body Γ (included pool upper)) := by
  obtain ⟨rule⟩ := exact_RoundsInUpper exact_RetainedPredecessor E body α Γ
    vertices ctx ty seed upper later fuel pool
  exact ⟨Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction seen closed) tape)⟩

/-- Equal packed least values from genuinely pre-fixed original pools,
mutual seed presence and the actual round reports. No length-budget
saturation or assumed equality of the raw representatives. -/
theorem exact_OriginalPackedMinimumFromPrefixed
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty a b va vb pa pb fa fb la lb x y : OTerm α)
    (minA : Derivation B Γ (leastGraph C X W s ctx ty a x))
    (minB : Derivation B Γ (leastGraph C X W s ctx ty b y))
    (packedA : Derivation B Γ (programGraph (membersAtSeed C X W s) pa ![ctx,ty,a]))
    (packedB : Derivation B Γ (programGraph (membersAtSeed C X W s) pb ![ctx,ty,b]))
    (roundA : Derivation B Γ (roundGraph (edge4 X W) pa fa va ctx ty a))
    (roundB : Derivation B Γ (roundGraph (edge4 X W) pb fb vb ctx ty b))
    (aInB : Derivation B Γ (memberGraph pb a))
    (bInA : Derivation B Γ (memberGraph pa b))
    (fixB : Derivation B Γ (prefixed (edge4 X W) va ctx ty pb lb))
    (fixA : Derivation B Γ (prefixed (edge4 X W) vb ctx ty pa la)) :
    Nonempty (Derivation B Γ (eqn x y)) := by
  have inclAB := intoUpper (edge4 X W) B α Γ va ctx ty a pb lb fa pa aInB fixB roundA
  have inclBA := intoUpper (edge4 X W) B α Γ vb ctx ty b pa la fb pb bInA fixA roundB
  obtain ⟨whichA⟩ := selected C X W s B α Γ ctx ty a pa x
  obtain ⟨whichB⟩ := selected C X W s B α Γ ctx ty b pb y
  have xInA := Derivation.implicationElimination whichA (Derivation.conjunctionIntroduction packedA minA)
  have yInB := Derivation.implicationElimination whichB (Derivation.conjunctionIntroduction packedB minB)
  obtain ⟨xInB⟩ := eliminate pa pb x inclAB ⟨xInA⟩
  obtain ⟨yInA⟩ := eliminate pb pa y inclBA ⟨yInB⟩
  obtain ⟨noXY⟩ := exact_OpenPackedLeastLowerBound C X W s B α Γ ctx ty b pb x y
  obtain ⟨noYX⟩ := exact_OpenPackedLeastLowerBound C X W s B α Γ ctx ty a pa y x
  exact unorderedEqual x y
    (Derivation.implicationElimination noXY (Derivation.conjunctionIntroduction minB
      (Derivation.conjunctionIntroduction packedB xInB)))
    (Derivation.implicationElimination noYX (Derivation.conjunctionIntroduction minA
      (Derivation.conjunctionIntroduction packedA yInA)))

#print axioms exact_OriginalPackedMinimumFromPrefixed
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedPackedMinimumProof
