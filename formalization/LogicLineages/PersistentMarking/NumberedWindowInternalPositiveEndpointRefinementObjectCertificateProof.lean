module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectCertificateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody checkerFormula)
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalGraphCompositionSyntaxProof (applyGraphSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm z suc zSubst sucSubst)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCheckerCoordinates (domain)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementObjectTargets
open NumberedWindowInternalPositiveEndpointRefinementObjectGraphProof (exactGraphs)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem scalarAdapter (i j : Program 1) (R d : Program 3) (c : Nat) (q : OTerm α) :
    carrier (data i j R d) false c q = programGraph (domain i) (suc z) ![numeral c,q] := by
  change arithmeticEmbedding.onFormula ((checkerFormula (domain i)).subst ![numeral c,q]) = _
  unfold checkerFormula
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext k
    exact Fin.cases rfl (Fin.cases rfl (fun p => Fin.elim0 p)) k

section
attribute [local irreducible] programGraph

private theorem certificateGraph (i j : Program 1) (R d : Program 3)
    (c : Nat) (x w y : OTerm α)
    (seen : Nonempty (Derivation B Γ (certificate (data i j R d) false c x y w))) :
    Nonempty (Derivation B Γ (programGraph R (suc z) ![x,w,y])) := by
  let tape : Fin 4 → OTerm α := ![numeral c,x,y,w]
  let coords : Fin 3 → Program 4 :=
    Fin.cases (.projection 1) (Fin.cases (.projection 3) (fun _ => .projection 2))
  change Nonempty (Derivation B Γ (programGraph (.composition R coords) (suc z) tape)) at seen
  apply compositionRecover R coords (suc z) tape ![x,w,y] seen
  intro k
  refine Fin.cases ?_ (fun q => Fin.cases ?_ (fun p => ?_) q) k
  · exact projectionValue (1 : Fin 4) tape
  · exact projectionValue (3 : Fin 4) tape
  · obtain rfl := Fin.eq_zero p
    exact projectionValue (2 : Fin 4) tape

private theorem actualCarrier (i j : Program 1) (R d : Program 3) (c : Nat) (q : OTerm α)
    (runs : Nonempty (Derivation B Γ (programGraph i (suc z) ![q]))) :
    Nonempty (Derivation B Γ (carrier (data i j R d) false c q)) := by
  rw [scalarAdapter]
  unfold domain
  let tape : Fin 2 → OTerm α := ![numeral c,q]
  apply compositionValue i (fun _ : Fin 1 => .projection (1 : Fin 2)) (suc z) tape ![q] runs
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (1 : Fin 2) tape

theorem exactCertificate : ExactOriginalPositiveCertificateEndpointCarriers := by
  intro i j r d c α Γ x w y
  dsimp only
  intro seen
  let R := withEndpointCarriers i r
  let S := data i j R d
  let body := sourceBody S c
  have inner : Nonempty (Derivation body Γ (programGraph R (suc z) ![x,w,y])) :=
    certificateGraph i j R d c x w y seen
  obtain ⟨out⟩ := exactGraphs i r body α Γ x w y inner
  have sides := Derivation.conjunctionRight out
  obtain ⟨left⟩ := actualCarrier i j R d c x ⟨Derivation.conjunctionLeft sides⟩
  obtain ⟨right⟩ := actualCarrier i j R d c y ⟨Derivation.conjunctionRight sides⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft out)
    (Derivation.conjunctionIntroduction left right)⟩

end
end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectCertificateProof
