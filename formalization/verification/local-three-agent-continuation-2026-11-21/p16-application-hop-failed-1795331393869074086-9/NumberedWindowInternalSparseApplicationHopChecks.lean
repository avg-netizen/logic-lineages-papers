module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseStructuralApplicationTargets (window syntaxWindow)
open NumberedWindowInternalSparseStructuralApplicationChecks (exact_WindowSyntaxReport)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalSparseCoveredWindowChecks (exact_CoveredWindowReport)
open NumberedWindowInternalSparseApplicationHopTargets
open NumberedWindowInternalSparseApplicationHopBindingProof (providedRename rawRename introduce)
attribute [local irreducible] programGraph

theorem exact_RawApplicationHop : ExactRawApplicationHop := by
  intro C root other baseW V s body α Γ ctx dom cod arg f child g
  let W := window C s baseW V
  let raw := typedRaw5 root other W V
  let H := premises raw W ctx dom cod arg f child g
  let Δ := H :: Γ
  let h : Derivation body Δ H := Derivation.hypothesis List.mem_cons_self
  have windows := Derivation.conjunctionRight h
  obtain ⟨first⟩ := exact_WindowSyntaxReport C s baseW V body α Δ ctx cod (auxiliaryTerm dom cod f arg)
  obtain ⟨last⟩ := exact_WindowSyntaxReport C s baseW V body α Δ ctx cod (auxiliaryTerm dom cod g arg)
  have checked := Derivation.conjunctionIntroduction
    (Derivation.implicationElimination first (Derivation.conjunctionLeft windows))
    (Derivation.implicationElimination last (Derivation.conjunctionRight windows))
  obtain ⟨lifted⟩ := NumberedWindowInternalSparseTypedRawLiftGraphProof.wrap root other W V
    ctx dom cod arg f child g ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
      (Derivation.conjunctionIntroduction checked windows)⟩
  exact ⟨Derivation.implicationIntroduction lifted⟩

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

private theorem finishRight (ctx cod src wr dst left : OTerm α)
    (accepted : Nonempty (Derivation body Γ (rawAt raw ctx cod src wr dst)))
    (first : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod src left)))
    (last : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod dst))) :
    Nonempty (Derivation body Γ (provided C X W s raw ctx cod src wr dst)) := by
  apply casesLeast C X W s ctx cod dst _ last
  intro β j Δ right keep toLast
  rw [providedRename]
  have a := renameInto accepted j Δ keep
  rw [rawRename] at a
  have l := renameInto first j Δ keep
  rw [leastRename] at l
  obtain ⟨a⟩ := a
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := toLast
  have outputs := Derivation.conjunctionIntroduction l r
  obtain ⟨positive⟩ := NumberedWindowInternalSparseAddressSingletonCoreProof.fromCalls raw
    (packedLeastProgram C X W s) _ _ _ _ _ _ _ ⟨Derivation.conjunctionIntroduction a outputs⟩
  exact introduce C X W s raw _ _ _ _ _ _ _ ⟨Derivation.conjunctionIntroduction outputs positive⟩

private theorem finish (ctx cod src wr dst : OTerm α)
    (accepted : Nonempty (Derivation body Γ (rawAt raw ctx cod src wr dst)))
    (first : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod src)))
    (last : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod dst))) :
    Nonempty (Derivation body Γ (provided C X W s raw ctx cod src wr dst)) := by
  apply casesLeast C X W s ctx cod src _ first
  intro β j Δ left keep leftResult
  rw [providedRename]
  have a := renameInto accepted j Δ keep
  rw [rawRename] at a
  have r := renameInto last j Δ keep
  rw [hasRename] at r
  exact finishRight C X W s raw _ _ _ _ _ left a leftResult r

theorem exact_ExistentialApplicationHop : ExactExistentialApplicationHop := by
  intro C root other baseW V X s body α Γ ctx dom cod arg f child g
  let W := window C s baseW V
  let raw := typedRaw5 root other W V
  let H := premises raw W ctx dom cod arg f child g
  let Δ := H :: Γ
  let h : Derivation body Δ H := Derivation.hypothesis List.mem_cons_self
  let src := auxiliaryTerm dom cod f arg
  let dst := auxiliaryTerm dom cod g arg
  obtain ⟨lifted⟩ := exact_RawApplicationHop C root other baseW V s body α Δ ctx dom cod arg f child g
  have get (q : OTerm α) (d : Derivation body Δ (windowAt W ctx cod q)) :
      Nonempty (Derivation body Δ (hasLeast C X W s ctx cod q)) := by
    obtain ⟨report⟩ := exact_CoveredWindowReport C X s (syntaxWindow baseW V) body α Δ ctx cod q
    exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.implicationElimination report d))⟩
  obtain ⟨done⟩ := finish C X W s raw ctx cod src (functionWitnessTerm child) dst
    ⟨Derivation.implicationElimination lifted h⟩
    (get src (Derivation.conjunctionLeft (Derivation.conjunctionRight h)))
    (get dst (Derivation.conjunctionRight (Derivation.conjunctionRight h)))
  exact ⟨Derivation.implicationIntroduction done⟩

#print axioms exact_RawApplicationHop
#print axioms exact_ExistentialApplicationHop
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopChecks
