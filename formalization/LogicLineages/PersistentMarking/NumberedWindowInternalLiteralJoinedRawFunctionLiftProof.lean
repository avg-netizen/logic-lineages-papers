module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRawLiftChecks (exact_OpenTypedRaw5FunctionLift)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot atomicFallback)
open NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof (auxiliaryAtomicTypedRaw)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (exact_OpenLiteralAtomicRawUnderlying)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (exact_OpenLiteralRawGuardReturnFromAtoms)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralDualTypedRawProof (dualTypedRaw exact_OpenDualTypedRawAtoms)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev selectedJoinedRaw (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) : Program 5 :=
  guardedRaw (strictDualRaw (measuredStrictCover V TV baseM) s leaf other base base T
    (unitAuxSyntax V TV) T)

/-- Recover both actual window reports from the dual raw checker, never
by equating it with either constituent on numerical fits. -/
theorem exact_OpenSelectedJoinedRawWindows (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (ctx ty q w r : OTerm α)
    (arc : D B Γ (programGraph (selectedJoinedRaw s base T V TV baseM leaf other) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (windowAt (joinedAuxiliaryWindow s base T V TV baseM) ctx ty q) ∧
    D B Γ (windowAt (joinedAuxiliaryWindow s base T V TV baseM) ctx ty r) := by
  let P := root (leafAtAuxiliary leaf)
  let F := fallback other
  let A := selectedBiAuxCoveredWindow s base T V TV baseM
  let Z := selectedBiAuxWindow s base T V TV baseM
  let Va := unitAuxSyntax V TV
  let R := dualTypedRaw P F A Z Va
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  have actual := exact_OpenLiteralAtomicRawUnderlying R xs arc
  obtain ⟨both⟩ := conjunctionRecover (auxiliaryAtomicTypedRaw P F A Va)
    (auxiliaryAtomicTypedRaw P F Z Va) xs actual
  have openAt (W : Program 3) (h : Derivation B Γ (programGraph (auxiliaryAtomicTypedRaw P F W Va) (suc z) xs)) :
      D B Γ (windowAt W ctx ty q) ∧ D B Γ (windowAt W ctx ty r) := by
    obtain ⟨rule⟩ := exact_OpenTypedRaw5 B (atomicRoot P) (auxiliaryFallback (atomicFallback F))
      W Va α Γ ctx ty q w r
    have facts := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft rule) h)
    exact ⟨⟨Derivation.conjunctionLeft facts⟩,⟨Derivation.conjunctionRight facts⟩⟩
  obtain ⟨qa,ra⟩ := openAt A (Derivation.conjunctionLeft both)
  obtain ⟨qz,rz⟩ := openAt Z (Derivation.conjunctionRight both)
  exact ⟨(exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty q).mpr ⟨qz,qa⟩,
    (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty r).mpr ⟨rz,ra⟩⟩

/-- Reuse the same child raw run and both original endpoint guards to
construct the original tag-five contextual *function reduction*.
The argument here is unchanged; its exchange transport is separate. -/
theorem exact_OpenJoinedRawFunctionLift (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (ctx dom cod q w r arg : OTerm α) :
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    let Va := unitAuxSyntax V TV
    let R := selectedJoinedRaw s base T V TV baseM leaf other
    let a := auxiliaryTerm dom cod q arg
    let b := auxiliaryTerm dom cod r arg
    D B Γ (programGraph R (suc z) ![ctx,rawCons dom cod,q,w,r]) →
    D B Γ (windowAt Q ctx cod a) → D B Γ (windowAt Q ctx cod b) →
    D B Γ (unary Va (suc z) a) → D B Γ (unary Va (suc z) b) →
    D B Γ (programGraph R (suc z) ![ctx,cod,a,functionWitnessTerm w,b]) := by
  intro Q Va R a b child lwin rwin hA hB
  let P := root (leafAtAuxiliary leaf)
  let F := fallback other
  let A := selectedBiAuxCoveredWindow s base T V TV baseM
  let Z := selectedBiAuxWindow s base T V TV baseM
  let original := dualTypedRaw P F A Z Va
  let xs : Fin 5 → OTerm α := ![ctx,rawCons dom cod,q,w,r]
  let ys : Fin 5 → OTerm α := ![ctx,cod,a,functionWitnessTerm w,b]
  obtain ⟨parts⟩ := conjunctionRecover (auxiliaryAtomicTypedRaw P F A Va)
    (auxiliaryAtomicTypedRaw P F Z Va) xs (exact_OpenLiteralAtomicRawUnderlying original xs child)
  obtain ⟨lZ,lA⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx cod a).mp lwin
  obtain ⟨rZ,rA⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx cod b).mp rwin
  obtain ⟨ha⟩ := hA
  obtain ⟨hb⟩ := hB
  have lift (W : Program 3) (run : Derivation B Γ (programGraph (auxiliaryAtomicTypedRaw P F W Va) (suc z) xs))
      (f : D B Γ (windowAt W ctx cod a)) (g : D B Γ (windowAt W ctx cod b)) :
      D B Γ (programGraph (auxiliaryAtomicTypedRaw P F W Va) (suc z) ys) := by
    obtain ⟨rule⟩ := exact_OpenTypedRaw5FunctionLift B (atomicRoot P) (auxiliaryFallback (atomicFallback F))
      W Va α Γ ctx dom cod arg q w r
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction run
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction ha hb)
        (Derivation.conjunctionIntroduction f g)))⟩
  have both := conjunctionAccept (auxiliaryAtomicTypedRaw P F A Va) (auxiliaryAtomicTypedRaw P F Z Va)
    ys (lift A (Derivation.conjunctionLeft parts) lA rA) (lift Z (Derivation.conjunctionRight parts) lZ rZ)
  exact exact_OpenLiteralRawGuardReturnFromAtoms original (exact_OpenDualTypedRawAtoms P F A Z Va)
    ctx cod a (functionWitnessTerm w) b both

#print axioms exact_OpenSelectedJoinedRawWindows
#print axioms exact_OpenJoinedRawFunctionLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
