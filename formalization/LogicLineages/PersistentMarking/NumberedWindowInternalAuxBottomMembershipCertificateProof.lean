module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipCertificateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody checkerFormula)
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalGraphCompositionSyntaxProof (applyGraphSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zSubst sucSubst)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCheckerCoordinates (domain)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalAuxBottomMembershipObjectTargets
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenRefinedAtomicAcceptance)
open NumberedWindowInternalAuxBottomRefinementObjectChecks (exact_OpenAuxBottomTerminal exact_OpenAuxBottomForgets)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem scalarAdapter (i j : Program 1) (r d : Program 3) (c : Nat) (y : OTerm α) :
    carrier (data i j r d) false c y =
      programGraph (domain i) (suc z) ![numeral c,y] := by
  change arithmeticEmbedding.onFormula ((checkerFormula (domain i)).subst ![numeral c,y]) = _
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

private theorem readCertificate (i j : Program 1) (R d : Program 3)
    (c : Nat) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (certificate (data i j R d) false c x y w))) :
    Nonempty (Derivation B Γ (programGraph R (suc z) ![x,w,y])) := by
  let tape : Fin 4 → OTerm α := ![numeral c,x,y,w]
  let coords : Fin 3 → Program 4 :=
    Fin.cases (.projection 1) (Fin.cases (.projection 3) (fun _ => .projection 2))
  change Nonempty (Derivation B Γ (programGraph (.composition R coords) (suc z) tape)) at h
  apply compositionRecover R coords (suc z) tape ![x,w,y] h
  intro k
  refine Fin.cases ?_ (fun q => Fin.cases ?_ (fun p => ?_) q) k
  · exact projectionValue (1 : Fin 4) tape
  · exact projectionValue (3 : Fin 4) tape
  · obtain rfl := Fin.eq_zero p
    exact projectionValue (2 : Fin 4) tape

private theorem carry (i j : Program 1) (R d : Program 3) (c : Nat) (y : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph i (suc z) ![y]))) :
    Nonempty (Derivation B Γ (carrier (data i j R d) false c y)) := by
  rw [scalarAdapter]
  unfold domain
  let tape : Fin 2 → OTerm α := ![numeral c,y]
  apply compositionValue i (fun _ : Fin 1 => .projection (1 : Fin 2)) (suc z) tape ![y] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (1 : Fin 2) tape

theorem exactCertificate : ExactAugmentedTerminalCertificates := by
  constructor
  · intro i j r d c α Γ x w y ctx t
    dsimp only
    intro shape cert
    let R := augmented i r
    let S := data i j R d
    let body := sourceBody S c
    have actual := readCertificate i j R d c x w y cert
    have inner := exact_OpenAuxBottomForgets i (refined i r) body α Γ x w y actual
    exact exact_OpenRefinedAtomicAcceptance.2 i r body α Γ x w y ctx t shape inner
  · intro i j r d c α Γ x w y ctx dom cod stored arg
    dsimp only
    intro shape cert
    let R := augmented i r
    let S := data i j R d
    let body := sourceBody S c
    have actual := readCertificate i j R d c x w y cert
    obtain ⟨result⟩ := exact_OpenAuxBottomTerminal i (refined i r) body α Γ
      x w y ctx dom cod stored arg shape actual
    obtain ⟨carried⟩ := carry i j R d c y ⟨Derivation.conjunctionRight result⟩
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft result) carried⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipCertificateProof
