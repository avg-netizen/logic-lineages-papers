module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginInstalledProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressLowerProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ scalarLower exact_ActualScalarSingletonLowerInstance)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalLiteralSingletonOriginInstalledProof (exact_InstalledLiteralSingletonMemberEdge)
open NumberedWindowInternalLiteralSingletonProgressTargets
open NumberedWindowInternalLiteralSingletonProgressSyntaxProof (scalarLowerRename oddCertificateRename singletonCodeRename)

theorem exact_LiteralSingletonLowerMembers : ExactLiteralSingletonLowerMembers := by
  intro i r c α Γ head dst w decoded
  dsimp only
  intro lower accepted parsed
  let S := literalData i r
  let B := sourceBody S c
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := memberGraph (decoded.relabel ρ) key
  let Δ := H :: Γ.map (fun p => p.relabel ρ)
  have keep : ∀ p ∈ Γ, p.relabel ρ ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have cert : Nonempty (Derivation B Δ
    (certificate S true c (singletonCode (head.relabel ρ)) (dst.relabel ρ) (w.relabel ρ))) := by
    simpa only [oddCertificateRename,singletonCodeRename] using renameInto accepted ρ Δ keep
  have strict := exact_InstalledLiteralSingletonMemberEdge i r c (α ⊕ Fin 1) Δ (head.relabel ρ)
    (dst.relabel ρ) (w.relabel ρ) (decoded.relabel ρ) key cert
    (renameParser dst decoded parsed ρ Δ keep) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have old : Nonempty (Derivation B Δ (scalarLower S c (head.relabel ρ))) := by
    simpa only [scalarLowerRename] using renameInto lower ρ Δ keep
  obtain ⟨singleton⟩ := exact_ActualScalarSingletonLowerInstance S c Δ (head.relabel ρ) key old strict
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction singleton)⟩

#print axioms exact_LiteralSingletonLowerMembers
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressLowerProof
