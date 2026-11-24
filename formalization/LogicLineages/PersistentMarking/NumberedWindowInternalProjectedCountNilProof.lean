module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc symm trans)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (appendZeroValue)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralEquivalenceReflexive)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep zeroBase)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets targetBase targetStep)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountNilTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem projNil (p : OTerm α)
    (map : D B Γ (unary scratchTargets (suc p) z)) : D B Γ (eqn p z) := by
  have h := nilRecover targetBase targetStep (suc p) Fin.elim0 map
  have expected : D B Γ (programGraph targetBase (suc z) Fin.elim0) :=
    literalGraph 1 Fin.elim0
  obtain ⟨same⟩ := valueUnique targetBase (suc p) (suc z) Fin.elim0 h expected
  exact ⟨cancelSuc same⟩

private theorem filterNil (side : Bool) (p pool : OTerm α)
    (filtered : D B Γ (filterGraph side p z pool)) : D B Γ (eqn p z) := by
  have h := nilRecover zeroBase (rowStep side) p ![pool] filtered
  exact valueUnique zeroBase p z ![pool] h (constantZeroValue ![pool])

private theorem tapeTwo (a b : OTerm α) :
    (![a,b] : Fin 2 → OTerm α) = Fin.cons a (Fin.cons b Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem movePair (p : Program 2) (value a b x y : OTerm α)
    (el : D B Γ (eqn a x)) (er : D B Γ (eqn b y))
    (h : D B Γ (programGraph p value ![a,b])) :
    D B Γ (programGraph p value ![x,y]) := by
  unfold programGraph at h ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula p)
    value ![a,b] ![x,y] _ h
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change D B Γ (equal a x)
    rw [equalEqn]
    exact el
  · obtain rfl := Fin.eq_zero j
    change D B Γ (equal b y)
    rw [equalEqn]
    exact er

theorem exact_OpenProjectedCountNil : ExactOpenProjectedCountNil := by
  intro B α Γ pool outL outR projected projectedL projectedR joined l r allMap lMap rMap app
  have left0 := filterNil true outL pool l
  have right0 := filterNil false outR pool r
  have all0 := projNil projected allMap
  have pl0 := projNil projectedL (headTransport scratchTargets (suc projectedL) outL z Fin.elim0 left0 lMap)
  have pr0 := projNil projectedR (headTransport scratchTargets (suc projectedR) outR z Fin.elim0 right0 rMap)
  have app0 := movePair append joined projectedL projectedR z z pl0 pr0 app
  have zz := appendZeroValue (body := B) (Gamma := Γ) (z : OTerm α)
  have zz' : D B Γ (appendGraph z z z) := by
    simp only [appendGraph,tapeTwo]
    exact zz
  obtain ⟨jc⟩ := valueUnique append joined z ![z,z] app0 zz'
  obtain ⟨pc⟩ := all0
  exact movePair permutation (suc z) z z projected joined ⟨symm pc⟩ ⟨symm jc⟩
    (exact_LiteralEquivalenceReflexive B α Γ z)

#print axioms exact_OpenProjectedCountNil

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilProof
