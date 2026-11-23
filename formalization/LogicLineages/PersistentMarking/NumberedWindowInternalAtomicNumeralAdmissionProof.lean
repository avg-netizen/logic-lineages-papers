module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicNumeralAdmissionTargets
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicNumeralAdmission
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (programGraph equal)
open ID1Completion.SourcePresentation (sourceBody)
open PositiveArithmeticOperators (Positive)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowAtomicPositiveTargets (bottomAddress freeAddress packedAddress)
open NumberedWindowInternalAtomicRefinement (bottomEmitter refined)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectEmitterChecks (exact_OpenAtomicBottomEmitter)
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_NumericAtomicBottomTarget)
open NumberedWindowInternalFreshProbeEmitter (packedEmitter packedFree)
open NumberedWindowInternalFreshProbeEmitterNumericChecks (exact_PackedFreeEmitterValue)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeEmitterObjectChecks (exact_PackedFreeEmitterGraph)
open NumberedWindowInternalCoordinateTargets (RawDomain)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalAtomicMembershipChecks (exact_RefinedAtomicMembership)
open NumberedWindowInternalAtomicRefinementReinstallChecks (exact_ReinstallConcreteRefinedTuple)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowScalarAlgorithm (scalar)
open NumberedWindowInternalAtomicNumeralAdmissionTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem bottomShape (ctx t : Nat) :
    Nonempty (Derivation B Γ (equal (numeral (bottomAddress ctx t))
      (packedBottomTerm (numeral ctx) (numeral t)))) := by
  have h := exact_NumeralGraph 2 bottomEmitter (ctx ::ᵥ t ::ᵥ nil) B α Γ
  have hc : inputs (α := α) (ctx ::ᵥ t ::ᵥ nil) = ![numeral ctx,numeral t] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [exact_NumericAtomicBottomTarget.1, hc] at h
  obtain ⟨shape⟩ := exact_OpenAtomicBottomEmitter B α Γ
    (numeral (bottomAddress ctx t)) (numeral ctx) (numeral t)
  obtain ⟨value⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft shape) value⟩

private theorem freeShape (ctx t n : Nat) :
    Nonempty (Derivation B Γ (equal (numeral (freeAddress ctx t n))
      (packedFreeTerm (numeral ctx) (numeral t) (numeral n)))) := by
  have h := exact_NumeralGraph 3 packedEmitter (ctx ::ᵥ t ::ᵥ n ::ᵥ nil) B α Γ
  have hc : inputs (α := α) (ctx ::ᵥ t ::ᵥ n ::ᵥ nil) = ![numeral ctx,numeral t,numeral n] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  have hv : evaluate packedEmitter (ctx ::ᵥ t ::ᵥ n ::ᵥ nil) = freeAddress ctx t n := by
    rw [exact_PackedFreeEmitterValue.1] <;> rfl
  rw [hv,hc] at h
  obtain ⟨shape⟩ := exact_PackedFreeEmitterGraph B α Γ
    (numeral (freeAddress ctx t n)) (numeral ctx) (numeral t) (numeral n)
  obtain ⟨value⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft shape) value⟩

private theorem numeralDomain (i : Program 1) (a : Nat)
    (ha : evaluate i (a ::ᵥ nil) = 1) :
    Nonempty (Derivation B Γ (RawDomain i (numeral a))) := by
  have h := exact_NumeralGraph 1 i (a ::ᵥ nil) B α Γ
  have hc : inputs (α := α) (a ::ᵥ nil) = ![numeral a] := by
    funext k
    exact Fin.cases rfl (fun j => Fin.elim0 j) k
  rw [ha,hc] at h
  exact h

theorem selectedAtomicNumeralAdmission : ExactSelectedAtomicNumeralAdmission := by
  intro xs s W hW
  obtain ⟨i,j,r,d,v,original,retained⟩ := exact_ReinstallConcreteRefinedTuple xs s W hW
  refine ⟨i,j,r,d,v,original,retained,?_⟩
  intro c β Δ
  let S := data i j (refined i r) d
  let Q := sourceBody S c
  have paid (a : Nat) (ha : scalar s a = true) :
      Nonempty (Derivation Q Δ (carrier S false c (numeral a))) := by
    apply (exact_DomainRules i j (refined i r) d false c Q β Δ (numeral a)).2
    apply numeralDomain
    have h : evaluate i (a ::ᵥ nil) = (scalar s a).toNat := retained.1.1 a
    change evaluate i (a ::ᵥ nil) = 1
    rw [h,ha] <;> rfl
  constructor
  · intro ctx t ha
    exact (exact_RefinedAtomicMembership.1 i j r d c β Δ
      (numeral (bottomAddress ctx t)) (numeral ctx) (numeral t) (bottomShape ctx t)).1
        (paid (bottomAddress ctx t) ha)
  · intro ctx t n ha
    exact (exact_RefinedAtomicMembership.2 i j r d c β Δ
      (numeral (freeAddress ctx t n)) (numeral ctx) (numeral t) (numeral n) (freeShape ctx t n)).1
        (paid (freeAddress ctx t n) ha)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicNumeralAdmission
