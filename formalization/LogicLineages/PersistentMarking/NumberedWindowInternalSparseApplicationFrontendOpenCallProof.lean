module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenGateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenCallProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowGuardedGraphTargets (atSlot)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawDomain rawCodomain rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreOpenChecks (exact_OpenApplicationOutputCore)
open NumberedWindowInternalSparseApplicationFrontend (callOutput)
open NumberedWindowInternalSparseApplicationFrontendOpenGateProof (G)

attribute [local irreducible] programGraph equalityTest outputCore

abbrev Slot (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p : Program 1) (slot : Fin 3) (out : OTerm α) (xs : Fin 3 → OTerm α) : Prop :=
  Nonempty (Derivation body Γ (programGraph (atSlot p slot) out xs))

abbrev compareArgs (p q : Program 1) : Fin 2 → Program 3 := ![atSlot p 0,atSlot q 1]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem compareValues (p q : Program 1) (xs : Fin 3 → OTerm α) (a b : OTerm α)
    (left : Slot body Γ p 0 a xs) (right : Slot body Γ q 1 b xs) :
    ∀ j, Nonempty (Derivation body Γ (programGraph (compareArgs p q j)
      ((![a,b] : Fin 2 → OTerm α) j) xs)) := by
  intro j
  exact Fin.cases left (Fin.cases right (fun noIndex => Fin.elim0 noIndex)) j

theorem readCompare (p q : Program 1) (xs : Fin 3 → OTerm α) (a b : OTerm α)
    (left : Slot body Γ p 0 a xs) (right : Slot body Γ q 1 b xs)
    (same : G body Γ (.composition equalityTest (compareArgs p q)) xs) :
    Nonempty (Derivation body Γ (eqn a b)) := by
  exact equalityOfAcceptance a b (compositionRecover equalityTest (compareArgs p q) (suc z) xs
    ![a,b] same (compareValues p q xs a b left right))

theorem makeCompare (p q : Program 1) (xs : Fin 3 → OTerm α) (a : OTerm α)
    (left : Slot body Γ p 0 a xs) (right : Slot body Γ q 1 a xs) :
    G body Γ (.composition equalityTest (compareArgs p q)) xs :=
  compositionValue equalityTest (compareArgs p q) (suc z) xs ![a,a]
    (equalitySelf a) (compareValues p q xs a a left right)

abbrev outputArgs : Fin 6 → Program 3 := ![atSlot rawContext 0,atSlot rawDomain 0,atSlot rawCodomain 0,
  atSlot rawLeast 0,atSlot rawLeast 1,.projection 2]

private theorem outputValues (xs : Fin 3 → OTerm α) (c d e fn arg : OTerm α)
    (ctx : Slot body Γ rawContext 0 c xs) (dom : Slot body Γ rawDomain 0 d xs)
    (cod : Slot body Γ rawCodomain 0 e xs) (l : Slot body Γ rawLeast 0 fn xs)
    (r : Slot body Γ rawLeast 1 arg xs) :
    ∀ j, Nonempty (Derivation body Γ (programGraph (outputArgs j)
      ((![c,d,e,fn,arg,xs 2] : Fin 6 → OTerm α) j) xs)) := by
  intro j
  exact Fin.cases ctx (Fin.cases dom (Fin.cases cod (Fin.cases l
    (Fin.cases r (Fin.cases (projectionValue (2 : Fin 3) xs)
      (fun noIndex => Fin.elim0 noIndex)))))) j

theorem readOutput (least : Program 3) (xs : Fin 3 → OTerm α) (c d e fn arg : OTerm α)
    (ctx : Slot body Γ rawContext 0 c xs) (dom : Slot body Γ rawDomain 0 d xs)
    (cod : Slot body Γ rawCodomain 0 e xs) (l : Slot body Γ rawLeast 0 fn xs)
    (r : Slot body Γ rawLeast 1 arg xs) (passed : G body Γ (callOutput least) xs) :
    Nonempty (Derivation body Γ (outputReport least c e (auxiliaryTerm d e fn arg) (xs 2))) := by
  have core := compositionRecover (outputCore least) outputArgs (suc z) xs
    ![c,d,e,fn,arg,xs 2] passed (outputValues xs c d e fn arg ctx dom cod l r)
  obtain ⟨opened⟩ := exact_OpenApplicationOutputCore body least α Γ c d e fn arg (xs 2)
  obtain ⟨verified⟩ := core
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft opened) verified⟩

theorem makeOutput (least : Program 3) (xs : Fin 3 → OTerm α) (c d e fn arg : OTerm α)
    (ctx : Slot body Γ rawContext 0 c xs) (dom : Slot body Γ rawDomain 0 d xs)
    (cod : Slot body Γ rawCodomain 0 e xs) (l : Slot body Γ rawLeast 0 fn xs)
    (r : Slot body Γ rawLeast 1 arg xs)
    (report : Nonempty (Derivation body Γ (outputReport least c e (auxiliaryTerm d e fn arg) (xs 2)))) :
    G body Γ (callOutput least) xs := by
  obtain ⟨codec⟩ := exact_OpenApplicationOutputCore body least α Γ c d e fn arg (xs 2)
  obtain ⟨reported⟩ := report
  have core : Nonempty (Derivation body Γ (programGraph (outputCore least) (suc z) ![c,d,e,fn,arg,xs 2])) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight codec) reported⟩
  exact compositionValue (outputCore least) outputArgs (suc z) xs
    ![c,d,e,fn,arg,xs 2] core (outputValues xs c d e fn arg ctx dom cod l r)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenCallProof
