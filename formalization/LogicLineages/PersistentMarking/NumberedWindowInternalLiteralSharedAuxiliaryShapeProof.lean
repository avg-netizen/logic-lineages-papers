module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualCertifiedCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSharedAuxiliaryShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports onTape)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof (exact_OpenLiteralAuxProfileShape)
open NumberedWindowInternalLiteralStrictDualCertifiedCasesProof (exact_OpenStrictDualAuxProfileFromStack)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The direct certificate's raw source is an actual auxiliary
application whenever its selected representative is that of an
original accepted application. No assumption about the head. -/
theorem exact_OpenStrictSharedAuxiliaryShape (L₀ : Program 3)
    (ctx ty dom cod fn arg q w r selected : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    D B Γ (programGraph L (suc selected) ![ctx,ty,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc selected) ![ctx,ty,q]) →
    D B Γ (bit sourceIsAux ![q,w,r]) := by
  intro L before actual
  let seed := auxiliaryTerm dom cod fn arg
  have p := exact_OpenStrictDualAuxProfileFromStack L₀ ctx ty seed selected before
  have a := exact_OpenStrictDualAuxProfileFromStack L₀ ctx ty q selected actual
  obtain ⟨shape,_⟩ := termReports (body := B) (Γ := Γ) dom cod fn arg
  have atSelected := (exact_OpenLiteralAuxProfileShape L₀ ctx ty seed selected p).1 shape
  have atRaw := (exact_OpenLiteralAuxProfileShape L₀ ctx ty q selected a).2 atSelected
  exact onTape termShape 0 (suc z) ![q,w,r] atRaw

#print axioms exact_OpenStrictSharedAuxiliaryShape
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSharedAuxiliaryShapeProof
