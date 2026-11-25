module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnPrefixedProof
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
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMinimumProof (exact_OpenLeastOnSelected exact_OpenLeastOnLower)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalScratchInclusionThinProof (included eliminate)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open NumberedWindowInternalThinPrefixedRoundsChecks (exact_RoundsInUpper)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)

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
theorem exact_OpenLeastOnPrefixed
    (C : Program 3) (E : Program 4) (s : Settings)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty a b va vb pa pb fa fb la lb x y : OTerm α)
    (minA : Derivation B Γ (leastOnGraph C E s ctx ty a x))
    (minB : Derivation B Γ (leastOnGraph C E s ctx ty b y))
    (packedA : Derivation B Γ (programGraph (membersAtSeedOn C E s) pa ![ctx,ty,a]))
    (packedB : Derivation B Γ (programGraph (membersAtSeedOn C E s) pb ![ctx,ty,b]))
    (roundA : Derivation B Γ (roundGraph E pa fa va ctx ty a))
    (roundB : Derivation B Γ (roundGraph E pb fb vb ctx ty b))
    (aInB : Derivation B Γ (memberGraph pb a))
    (bInA : Derivation B Γ (memberGraph pa b))
    (fixB : Derivation B Γ (prefixed E va ctx ty pb lb))
    (fixA : Derivation B Γ (prefixed E vb ctx ty pa la)) :
    Nonempty (Derivation B Γ (eqn x y)) := by
  have inclAB := intoUpper E B α Γ va ctx ty a pb lb fa pa aInB fixB roundA
  have inclBA := intoUpper E B α Γ vb ctx ty b pa la fb pb bInA fixA roundB
  have xInA := exact_OpenLeastOnSelected C E s ctx ty a pa x ⟨minA⟩ ⟨packedA⟩
  have yInB := exact_OpenLeastOnSelected C E s ctx ty b pb y ⟨minB⟩ ⟨packedB⟩
  have xInB := eliminate pa pb x inclAB xInA
  have yInA := eliminate pb pa y inclBA yInB
  obtain ⟨noXY⟩ := exact_OpenLeastOnLower C E s ctx ty b pb x y ⟨minB⟩ ⟨packedB⟩ xInB
  obtain ⟨noYX⟩ := exact_OpenLeastOnLower C E s ctx ty a pa y x ⟨minA⟩ ⟨packedA⟩ yInA
  exact unorderedEqual x y noXY noYX

#print axioms exact_OpenLeastOnPrefixed
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnPrefixedProof
