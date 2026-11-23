module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedRootProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedTypedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparseTypedRawOpenProof (graph)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseRawRunRootProof (rootRunRecover)
open NumberedWindowInternalCopyHeadClosedRootProof (exact_OriginalClosedCopyRootCone)
open NumberedWindowInternalCopyHeadClosedRootTargets

theorem exact_OriginalClosedEndpointTypedCopyCone : ExactOriginalClosedEndpointTypedCopyCone := by
  intro entries s root other window syntaxCode fit B α Γ ctx result src dst f ty label base extras g args goal
    accepted next
  obtain ⟨law⟩ := graph B root other window syntaxCode α Γ ctx result
    (numeral src) (rootWitnessTerm (numeral copyPayload)) (numeral dst)
  obtain ⟨accepted⟩ := accepted
  have guards := Derivation.implicationElimination (Derivation.conjunctionLeft law) accepted
  have rootAccepted := rootRunRecover root other (numeral src) (numeral copyPayload) (numeral dst)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft guards)⟩
  exact exact_OriginalClosedCopyRootCone entries s root fit B α Γ src dst f ty label base extras
    g args goal rootAccepted next

#print axioms exact_OriginalClosedEndpointTypedCopyCone

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadClosedTypedProof
