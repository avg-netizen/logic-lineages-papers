module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralForwardCoordinatesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport headTransport)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast addressGood)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalOriginalFirstHopCoreProof (exact_OriginalLiteralAddressReport)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
attribute [local irreducible] programGraph

theorem exact_OpenRetapeAddress (x co ty k c' t' k' : OTerm α)
    (old : D B Γ (addressReport x co ty k))
    (c : D B Γ (eqn co c')) (t : D B Γ (eqn ty t')) (l : D B Γ (eqn k k')) :
    D B Γ (addressReport x c' t' k') := by
  obtain ⟨s⟩ := old
  let d := Derivation.conjunctionRight s
  let e := Derivation.conjunctionRight d
  obtain ⟨cc⟩ := outputTransport rawContext co c' ![x] c ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨tt⟩ := outputTransport rawResult ty t' ![x] t ⟨Derivation.conjunctionLeft e⟩
  obtain ⟨kk⟩ := outputTransport rawLeast k k' ![x] l ⟨Derivation.conjunctionRight e⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft s)
    (Derivation.conjunctionIntroduction cc (Derivation.conjunctionIntroduction tt kk))⟩

theorem exact_OpenLiteralReportedAddress (x ctx ty k : OTerm α)
    (h : D B Γ (eqn x (addressTerm ctx ty k))) : D B Γ (addressReport x ctx ty k) := by
  obtain ⟨equal⟩ := h
  obtain ⟨r⟩ := exact_OriginalLiteralAddressReport (B := B) (Γ := Γ) ctx ty k
  let y := addressTerm ctx ty k
  let d := Derivation.conjunctionRight r
  let e := Derivation.conjunctionRight d
  obtain ⟨shape⟩ := headTransport addressGood (suc z) y x ![] ⟨symm equal⟩ ⟨Derivation.conjunctionLeft r⟩
  obtain ⟨first⟩ := headTransport rawContext ctx y x ![] ⟨symm equal⟩ ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨second⟩ := headTransport rawResult ty y x ![] ⟨symm equal⟩ ⟨Derivation.conjunctionLeft e⟩
  obtain ⟨third⟩ := headTransport rawLeast k y x ![] ⟨symm equal⟩ ⟨Derivation.conjunctionRight e⟩
  exact ⟨Derivation.conjunctionIntroduction shape
    (Derivation.conjunctionIntroduction first (Derivation.conjunctionIntroduction second third))⟩

theorem exact_OpenParsedOperandAddresses (f u ctx result dom cod fn arg : OTerm α)
    (h : D B Γ (parsedApplicationInputs f u ctx result dom cod fn arg)) :
    D B Γ (addressReport f ctx (rawCons dom cod) fn) ∧ D B Γ (addressReport u ctx dom arg) ∧
    D B Γ (eqn f (addressTerm ctx (rawCons dom cod) fn)) := by
  obtain ⟨all⟩ := h
  let uRows := Derivation.conjunctionRight all
  let arrowRows := Derivation.conjunctionRight uRows
  let fRows := Derivation.conjunctionRight arrowRows
  let aRows := Derivation.conjunctionRight fRows
  let coordinates := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight aRows))
  let arrowEq := Derivation.conjunctionLeft coordinates
  have fAddress : D B Γ (addressReport f ctx result fn) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft all) (Derivation.conjunctionLeft fRows)⟩
  have aAddress : D B Γ (addressReport u ctx dom arg) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft uRows) (Derivation.conjunctionLeft aRows)⟩
  exact ⟨exact_OpenRetapeAddress f ctx result fn ctx (rawCons dom cod) fn fAddress ⟨refl ctx⟩ ⟨arrowEq⟩ ⟨refl fn⟩,
    aAddress,rebuildAddress f ctx result fn ctx (rawCons dom cod) fn fAddress ⟨refl ctx⟩ ⟨arrowEq⟩ ⟨refl fn⟩⟩

theorem exact_OpenRetapePositiveFold (P : Program 5) (ctx ty src cert target c t a : OTerm α)
    (gc : D B Γ (eqn ctx c)) (gt : D B Γ (eqn ty t)) (ga : D B Γ (eqn src a))
    (old : D B Γ (programGraph P (suc z) ![ctx,ty,src,cert,target])) :
    D B Γ (programGraph P (suc z) ![c,t,a,cert,target]) := by
  unfold programGraph at *
  apply graphInputTransport B α 5 Γ (OrdinaryArithmetic.graphFormula P) (suc z)
    ![ctx,ty,src,cert,target] ![c,t,a,cert,target] _ old
  intro i
  rw [onEquality]
  exact Fin.cases gc (Fin.cases gt (Fin.cases ga
    (Fin.cases (⟨refl cert⟩ : D B Γ (eqn cert cert)) (Fin.cases (⟨refl target⟩ : D B Γ (eqn target target))
      (fun n => Fin.elim0 n))))) i

#print axioms exact_OpenRetapeAddress
#print axioms exact_OpenLiteralReportedAddress
#print axioms exact_OpenParsedOperandAddresses
#print axioms exact_OpenRetapePositiveFold
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralForwardCoordinatesProof
