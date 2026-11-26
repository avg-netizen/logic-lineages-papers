module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityAddressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportRename dataRename reportsCases)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (suppliedEdgeRename)
open NumberedWindowInternalSparseAddressTransitivityComposeProof (fromReports)
open NumberedWindowInternalSparseAddressTransitivityTargets

theorem combine {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (cv tv : Program 1) (raw : Program 5) (least : Program 3) (left first mid second right : OTerm α)
    (one : Nonempty (Derivation body Γ (accepts (addressPositive cv tv raw least) left first mid)))
    (two : Nonempty (Derivation body Γ (accepts (addressPositive cv tv raw least) mid second right))) :
    Nonempty (Derivation body Γ (suppliedEdge (addressPositive cv tv raw least) left right)) := by
  let r := addressPositive cv tv raw least
  have firstRep := forward cv tv raw least left first mid one
  have secondRep := forward cv tv raw least mid second right two
  apply reportsCases cv tv raw least left first mid (suppliedEdge r left right) firstRep
  intro β j Δ c₁ t₁ src m₁ hJ a
  rw [suppliedEdgeRename]
  have other := renameInto secondRep j Δ hJ
  rw [reportRename] at other
  apply reportsCases cv tv raw least (mid.relabel j) (second.relabel j) (right.relabel j)
    (suppliedEdge r (left.relabel j) (right.relabel j)) other
  intro γ k Θ c₂ t₂ m₂ dst hK b
  rw [suppliedEdgeRename]
  have a' := renameInto a k Θ hK
  rw [dataRename] at a'
  exact fromReports cv tv raw least ((left.relabel j).relabel k) ((first.relabel j).relabel k)
    ((mid.relabel j).relabel k) ((second.relabel j).relabel k) ((right.relabel j).relabel k)
    (c₁.relabel k) (t₁.relabel k) (src.relabel k) (m₁.relabel k) c₂ t₂ m₂ dst a' b

theorem installed : ExactInstalledAddressTransitivity := by
  intro i j cv tv d raw least c α left first mid second right
  let r := addressPositive cv tv raw least
  let B := sourceBody (data i j r d) c
  let pair := accepts r left first mid ⊓ accepts r mid second right
  have both : Derivation B [pair] pair := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := combine cv tv raw least left first mid second right
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityAddressProof
