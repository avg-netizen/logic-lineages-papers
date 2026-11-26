module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDualTypedRawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAtomicCoveredCasesProof (PerTickRaw)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredTypedAuxChildProof (arrowFieldsEq)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRawTransport)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (exact_OpenLiteralRawGuardReturnFromAtoms)
open NumberedWindowInternalLiteralDualTypedRawProof
  (dualTypedRaw exact_OpenDualTypedRawIntro exact_OpenDualTypedRawAtoms)
open NumberedWindowInternalLiteralStrictSealedWindowProof
  (strictSealedWindow exact_OpenStrictSealedAuxChildren exact_OpenStrictSealedAuxReports strictWindowTypeMove
    exact_OpenCoverageFromLeastDomain)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Both original typed endpoint observations are physically installed
in the raw checker. Its original machine and syntax are shared. -/
def strictDualRaw (C : Program 3) (s : Settings) (leaf : Nat → Program 3) (other : Program 3)
    (rawBase base : Program 2) (rawT V T : Program 1) : Program 5 :=
  dualTypedRaw (root (leafAtAuxiliary leaf)) (fallback other) (coveredMemoWindow C s rawBase rawT V)
    (strictSealedWindow C s base T) V

/-- The actual strict window recurs through the contextual child at
both ends. Hence the child's exact dual raw call and the outer raw
atom guard follow, together with the physical child windows needed
for canonical result admission. The guard is not inferred at an
arbitrary term from numeric agreement of the two window programs. -/
theorem exact_OpenStrictDualChild (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (rawBase base : Program 2) (rawT V T : Program 1)
    (ctx ty q w r dom cod fn arg kid dom' cod' dst arg' : OTerm α) :
    let A := coveredMemoWindow C s rawBase rawT V
    let Z := strictSealedWindow C s base T
    let R := strictDualRaw C s leaf other rawBase base rawT V T
    Parts B Γ q w r dom cod fn arg kid dom' cod' dst arg' →
    D B Γ (windowAt Z ctx ty q) → D B Γ (windowAt Z ctx ty r) →
    D B Γ (programGraph (PerTickRaw C s leaf other rawBase rawT V) (suc z) ![ctx,rawCons dom cod,fn,kid,dst]) →
    D B Γ (hasLeast C X A s ctx (rawCons dom cod) fn) →
    D B Γ (hasLeast C X A s ctx (rawCons dom cod) dst) →
    D B Γ (hasLeast C X A s ctx dom arg) →
    D B Γ (programGraph (guardedRaw R) (suc z) ![ctx,rawCons dom cod,fn,kid,dst] ⊓
      (windowAt Z ctx (rawCons dom cod) fn ⊓ (windowAt Z ctx (rawCons dom cod) dst ⊓
        windowAt Z ctx dom arg))) := by
  intro A Z R parts left right old fnD dstD argD
  let U := strictAuxWindow base T
  let P := root (leafAtAuxiliary leaf)
  let F := fallback other
  have before := windowRawTransport Z ctx ty q (auxiliaryTerm dom cod fn arg) parts.source left
  have after := windowRawTransport Z ctx ty r (auxiliaryTerm dom' cod' dst arg') parts.target right
  obtain ⟨_,_,_,fnWindow,argWindow⟩ := exact_OpenStrictSealedAuxChildren C A X s base T ctx ty dom cod fn arg
    before fnD argD
  obtain ⟨_,⟨rt⟩⟩ := exact_OpenStrictSealedAuxReports C s base T ctx ty dom' cod' dst arg' after
  have typed := Derivation.conjunctionLeft (Derivation.conjunctionRight rt)
  obtain ⟨correct⟩ := arrowFieldsEq dom cod dom' cod' parts.domEq parts.codEq
  have same := strictWindowTypeMove U ctx (rawCons dom' cod') (rawCons dom cod) dst ⟨symm correct⟩ ⟨typed⟩
  have dc := exact_OpenCoverageFromLeastDomain C A X s ctx (rawCons dom cod) dst dstD
  have dstWindow := (exact_OpenSealedWindow C s U ctx (rawCons dom cod) dst).2 same dc
  have both := exact_OpenDualTypedRawIntro P F A Z V ctx (rawCons dom cod) fn kid dst old fnWindow dstWindow
  obtain ⟨actual⟩ := exact_OpenLiteralRawGuardReturnFromAtoms R
    (exact_OpenDualTypedRawAtoms P F A Z V) ctx (rawCons dom cod) fn kid dst both
  obtain ⟨lf⟩ := fnWindow
  obtain ⟨rg⟩ := dstWindow
  obtain ⟨aa⟩ := argWindow
  exact ⟨Derivation.conjunctionIntroduction actual
    (Derivation.conjunctionIntroduction lf (Derivation.conjunctionIntroduction rg aa))⟩

#print axioms exact_OpenStrictDualChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualChildProof
