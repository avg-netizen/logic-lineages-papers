module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectCertificateProof
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
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementObjectTargets
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCheckerCoordinates (domain suppliedCertificate)
open NumberedWindowInternalAtomicRefinementObjectBranchProof (exactAcceptance)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem carrierGraph (i j : Program 1) (r d : Program 3) (context : Nat) (y : OTerm α) :
    carrier (data i j r d) false context y =
      programGraph (domain i) (suc z) ![numeral context,y] := by
  change arithmeticEmbedding.onFormula ((checkerFormula (domain i)).subst ![numeral context,y]) = _
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

private theorem certificateGraph (i j : Program 1) (r d : Program 3)
    (context : Nat) (x w y : OTerm α)
    (h : Nonempty (Derivation body Γ (certificate (data i j r d) false context x y w))) :
    Nonempty (Derivation body Γ (programGraph r (suc z) ![x,w,y])) := by
  let tape : Fin 4 → OTerm α := ![numeral context,x,y,w]
  let coords : Fin 3 → Program 4 :=
    Fin.cases (.projection 1) (Fin.cases (.projection 3) (fun _ => .projection 2))
  change Nonempty (Derivation body Γ (programGraph (.composition r coords) (suc z) tape)) at h
  apply compositionRecover r coords (suc z) tape ![x,w,y] h
  intro k
  refine Fin.cases ?_ (fun q => Fin.cases ?_ (fun p => ?_) q) k
  · exact projectionValue (1 : Fin 4) tape
  · exact projectionValue (3 : Fin 4) tape
  · obtain rfl := Fin.eq_zero p
    exact projectionValue (2 : Fin 4) tape

private theorem carrierFromGraph (i j : Program 1) (r d : Program 3) (context : Nat) (y : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph i (suc z) ![y]))) :
    Nonempty (Derivation body Γ (carrier (data i j r d) false context y)) := by
  rw [carrierGraph]
  unfold domain
  let tape : Fin 2 → OTerm α := ![numeral context,y]
  apply compositionValue i (fun _ : Fin 1 => .projection (1 : Fin 2)) (suc z) tape ![y] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (1 : Fin 2) tape

theorem exactCertificate : ExactOpenRefinedAtomicCertificate := by
  constructor
  · intro i j r d context α Γ x w y c t n
    dsimp only
    intro shape seen
    let S := data i j (refined i r) d
    let I := sourceBody S context
    have h := certificateGraph i j (refined i r) d context x w y seen
    obtain ⟨out⟩ := exactAcceptance.1 i r I α Γ x w y c t n shape h
    obtain ⟨member⟩ := carrierFromGraph i j (refined i r) d context y
      ⟨Derivation.conjunctionRight out⟩
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft out) member⟩
  · intro i j r d context α Γ x w y c t
    dsimp only
    intro shape seen
    let I := sourceBody (data i j (refined i r) d) context
    exact exactAcceptance.2 i r I α Γ x w y c t shape
      (certificateGraph i j (refined i r) d context x w y seen)

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectCertificateProof
