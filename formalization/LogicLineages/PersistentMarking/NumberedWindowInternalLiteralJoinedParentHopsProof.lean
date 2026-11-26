module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedPathHopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedParentHopsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (ParentTypeEvidence)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenRawWithTargetUnderlying (i cv tv : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph (rawWithTarget i cv tv raw L) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r]) := by
  obtain ⟨row⟩ := conjunctionRecover raw (targetGate i cv tv L) ![ctx,ty,q,w,r] held
  exact ⟨Derivation.conjunctionLeft row⟩

theorem exact_OpenJoinedWindowCoverage (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx ty seed : OTerm α)
    (formed : D B Γ (windowAt (joinedAuxiliaryWindow s base T V TV baseM) ctx ty seed)) :
    D B Γ (coverageReport (measuredStrictCover V TV baseM) s ctx seed) := by
  have strict := ((exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty seed).mp formed).1
  exact ((exact_OpenSealedWindow (measuredStrictCover V TV baseM) s (strictAuxWindow base T) ctx ty seed).1 strict).2

/-- The wrapped successful child has a literal raw parent step and both
raw parent windows. The argument in both raw parents is identical. -/
theorem exact_OpenJoinedParentHops (s : Settings) (base : Program 2) (T V TV baseM i cv tv : Program 1)
    (L : Program 3) (leaf : Nat → Program 3) (other : Program 3)
    (ctx dom cod q w r arg : OTerm α) :
    let W := joinedAuxiliaryWindow s base T V TV baseM
    let raw := selectedJoinedRaw s base T V TV baseM leaf other
    let R := rawWithTarget i cv tv raw L
    let q₀ := auxiliaryTerm dom cod q arg
    let r₀ := auxiliaryTerm dom cod r arg
    ParentTypeEvidence s T TV B Γ dom cod → D B Γ (windowAt W ctx dom arg) →
    D B Γ (programGraph R (suc z) ![ctx,rawCons dom cod,q,w,r]) →
    D B Γ (windowAt W ctx cod q₀) ∧ D B Γ (windowAt W ctx cod r₀) ∧
      D B Γ (programGraph raw (suc z) ![ctx,cod,q₀,functionWitnessTerm w,r₀]) := by
  intro W raw R q₀ r₀ types fixed step
  have arc := exact_OpenRawWithTargetUnderlying i cv tv raw L ctx (rawCons dom cod) q w r step
  obtain ⟨f,g⟩ := exact_OpenSelectedJoinedRawWindows s base T V TV baseM leaf other ctx (rawCons dom cod) q w r arc
  obtain ⟨left,x⟩ := exact_OpenJoinedAuxiliaryParent s base T V TV baseM ctx dom cod q arg types f fixed
  obtain ⟨right,y⟩ := exact_OpenJoinedAuxiliaryParent s base T V TV baseM ctx dom cod r arg types g fixed
  exact ⟨left,right,exact_OpenJoinedRawFunctionLift s base T V TV baseM leaf other ctx dom cod q w r arg
    arc left right x y⟩

#print axioms exact_OpenRawWithTargetUnderlying
#print axioms exact_OpenJoinedWindowCoverage
#print axioms exact_OpenJoinedParentHops
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedParentHopsProof
