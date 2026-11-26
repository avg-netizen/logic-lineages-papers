module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnAtPoolsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnSubsetCanonicalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (D)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMembersProof
open NumberedWindowInternalLiteralLeastOnMinimumProof (exact_OpenLeastOnSeedOrigin exact_OpenLeastOnLower)
open NumberedWindowInternalLiteralLeastOnAtPoolsProof (seedOn)
open NumberedWindowInternalLiteralLeastOnEdgeProof (exact_OpenLeastOnSeedReport)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)

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

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLeastOnNoGreaterThanSeed (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty q k : OTerm α) (least : D B Γ (leastOnGraph C E s ctx ty q k)) :
    D B Γ (ltF q k).not := by
  apply exact_OpenLeastOnSeedReport C E s ctx ty q k _ least
  intro β j Δ vertices pool _ data
  change D B Δ ((ltF q k).relabel j).not
  rw [orderRename]
  obtain ⟨d⟩ := data
  let c := ctx.relabel j
  let t := ty.relabel j
  let a := q.relabel j
  let b := k.relabel j
  let one := Derivation.conjunctionLeft d
  let cover := Derivation.conjunctionLeft (Derivation.conjunctionRight d)
  let chosen := Derivation.conjunctionRight (Derivation.conjunctionRight d)
  have member := exact_OpenLeastOnSeedOrigin C E s c t a vertices pool b ⟨one⟩ ⟨chosen⟩ ⟨cover⟩
  have computed := exact_OpenLeastOnActualMembers C E s c t a vertices pool ⟨cover⟩ ⟨chosen⟩
  have retained := exact_OpenLeastOnSeedRetained E vertices c t a pool member computed
  exact exact_OpenLeastOnLower C E s c t a pool a b ⟨one⟩ ⟨chosen⟩ retained

/-- An old canonical address remains canonical for a successful
refined query at that same address if the actual refined edge keeps
the old least observer. This is not equivalence of the two programs
on arbitrary noncanonical inputs. -/
theorem exact_OpenOldCanonicalRemains (C : Program 3) (original refined : Program 4) (s : Settings)
    (kept : Preserves refined (packedLeastOn C original s))
    (ctx ty k x : OTerm α)
    (old : D B Γ (leastOnGraph C original s ctx ty k k))
    (current : D B Γ (leastOnGraph C refined s ctx ty k x)) :
    D B Γ (leastOnGraph C refined s ctx ty k k) := by
  have still := exact_OpenLiteralSelectedObserverOn C refined s (packedLeastOn C original s) kept
    ctx ty k x (suc k) current old
  obtain ⟨noLeft⟩ := exact_OpenLeastOnNoGreaterThanSeed C original s ctx ty x k still
  obtain ⟨noRight⟩ := exact_OpenLeastOnNoGreaterThanSeed C refined s ctx ty k x current
  obtain ⟨eq⟩ := unorderedEqual x k noLeft noRight
  exact outputTransport (packedLeastOn C refined s) (suc x) (suc k) ![ctx,ty,k] ⟨congSuc eq⟩ current

theorem exact_OpenRefinedOldCanonicalAgreement (C : Program 3) (original refined : Program 4) (s : Settings)
    (kept : Preserves refined (packedLeastOn C original s))
    (ctx ty raw k x : OTerm α)
    (old : D B Γ (leastOnGraph C original s ctx ty raw k))
    (newRun : D B Γ (leastOnGraph C refined s ctx ty raw x))
    (oldCanonical : D B Γ (leastOnGraph C original s ctx ty x x)) :
    D B Γ (eqn k x) := by
  have there := exact_OpenLiteralSelectedObserverOn C refined s (packedLeastOn C original s) kept
    ctx ty raw x (suc k) newRun old
  obtain ⟨same⟩ := valueUnique (packedLeastOn C original s) (suc k) (suc x) ![ctx,ty,x] there oldCanonical
  exact ⟨cancelSuc same⟩

#print axioms exact_OpenLeastOnNoGreaterThanSeed
#print axioms exact_OpenOldCanonicalRemains
#print axioms exact_OpenRefinedOldCanonicalAgreement
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnSubsetCanonicalProof
