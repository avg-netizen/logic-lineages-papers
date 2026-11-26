module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityScalarProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementTransitivityAddressProof (openTransitive)
open NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets

private theorem scalarRename {α β : Type} (S : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge S false c x y).relabel j = edge S false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S false c x y).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem scalarCompose (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
    (c : Nat) (left mid right : OTerm α) :
    let R := withEndpointCarriers i (addressPositive cv tv raw least)
    let S := data i j R d
    Nonempty (Derivation B Γ (edge S false c left mid)) →
    Nonempty (Derivation B Γ (edge S false c mid right)) →
    Nonempty (Derivation B Γ (edge S false c left right)) := by
  dsimp only
  intro a b
  let R := withEndpointCarriers i (addressPositive cv tv raw least)
  let S := data i j R d
  apply edgeCases S c left mid (edge S false c left right) a
  intro β ρ Δ first keepsA aa
  rw [scalarRename]
  have one := (exact_CertificateRules i j R d false c B β Δ
    (left.relabel ρ) (mid.relabel ρ) first).mp aa
  have b' := renameInto b ρ Δ keepsA
  rw [scalarRename] at b'
  apply edgeCases S c (mid.relabel ρ) (right.relabel ρ)
    (edge S false c (left.relabel ρ) (right.relabel ρ)) b'
  intro γ η Θ second keepsB bb
  rw [scalarRename]
  let x := (left.relabel ρ).relabel η
  let m := (mid.relabel ρ).relabel η
  let y := (right.relabel ρ).relabel η
  have one' := renameInto one η Θ keepsB
  rw [acceptsRename] at one'
  have two := (exact_CertificateRules i j R d false c B γ Θ m y second).mp bb
  have joined := openTransitive i cv tv raw least B γ Θ x (first.relabel η) m second y one' two
  apply consume R x y (edge S false c x y) joined
  intro δ k Ξ witness _ actual
  rw [scalarRename]
  exact edgeIntroduction ((exact_CertificateRules i j R d false c B δ Ξ
    (x.relabel k) (y.relabel k) witness).mpr actual)

theorem installed : ExactInstalledEndpointRefinedScalarEdgeTransitivity := by
  intro i j cv tv d raw least c α left middle right
  let R := withEndpointCarriers i (addressPositive cv tv raw least)
  let S := data i j R d
  let B := sourceBody S c
  let premise := edge S false c left middle ⊓ edge S false c middle right
  have both : Derivation B [premise] premise := Derivation.hypothesis List.mem_cons_self
  obtain ⟨out⟩ := scalarCompose i j cv tv d raw least c left middle right
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityScalarProof
