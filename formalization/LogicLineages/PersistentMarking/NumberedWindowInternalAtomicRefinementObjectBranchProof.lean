module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectRecognizeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectBranchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue valueUnique equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementObjectTargets
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (bottomEmitterGraph)
open NumberedWindowInternalAtomicRefinementObjectRecognizeProof (exactRecognition)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem branchAST (i : Program 1) (r : Program 3) :
    refined i r =
      branch (atSource freeSource) (branch (atSource bottomSource) r (constantZero 3))
        (conjunction r (conjunction bottomTarget (atTarget i))) := by
  unfold refined
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.2.2.2.2.1,
    exact_DispatchControlAST.1,exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2]

section
attribute [local irreducible] programGraph

private theorem callSource (p : Program 1) (out x w y : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p out ![x]))) :
    Nonempty (Derivation body Γ (programGraph (atSource p) out ![x,w,y])) := by
  unfold atSource
  let tape : Fin 3 → OTerm α := ![x,w,y]
  apply compositionValue p (fun _ : Fin 1 => .projection (0 : Fin 3)) out tape ![x] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (0 : Fin 3) tape

private theorem takeTarget (p : Program 1) (out x w y : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (atTarget p) out ![x,w,y]))) :
    Nonempty (Derivation body Γ (programGraph p out ![y])) := by
  unfold atTarget at h
  let tape : Fin 3 → OTerm α := ![x,w,y]
  apply compositionRecover p (fun _ : Fin 1 => .projection (2 : Fin 3)) out tape ![y] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (2 : Fin 3) tape

private theorem bottomReport (x c t : OTerm α)
    (rows : Nonempty (Derivation body Γ (sourceFields x c t))) :
    Nonempty (Derivation body Γ (programGraph bottomOf (packedBottomTerm c t) ![x])) := by
  obtain ⟨h⟩ := rows
  unfold bottomOf
  apply compositionValue bottomEmitter (Fin.cons rawContext (Fin.cons rawResult Fin.elim0))
    (packedBottomTerm c t) ![x] ![c,t] (bottomEmitterGraph c t)
  intro j
  have hc : Nonempty (Derivation body Γ (programGraph rawContext c ![x])) :=
    ⟨Derivation.conjunctionLeft h⟩
  have ht : Nonempty (Derivation body Γ (programGraph rawResult t ![x])) :=
    ⟨Derivation.conjunctionRight h⟩
  exact Fin.cases hc (Fin.cases ht (fun k => Fin.elim0 k)) j

private theorem checkedTarget (x w y c t : OTerm α)
    (fields : Nonempty (Derivation body Γ (sourceFields x c t)))
    (h : Nonempty (Derivation body Γ (programGraph bottomTarget (suc z) ![x,w,y]))) :
    Nonempty (Derivation body Γ (equal y (packedBottomTerm c t))) := by
  let t₀ := packedBottomTerm c t
  let tape : Fin 3 → OTerm α := ![x,w,y]
  have htarget : Nonempty (Derivation body Γ (programGraph (.projection (2 : Fin 3)) y tape)) :=
    projectionValue (2 : Fin 3) tape
  have hbottom : Nonempty (Derivation body Γ (programGraph (atSource bottomOf) t₀ tape)) :=
    callSource bottomOf t₀ x w y (bottomReport x c t fields)
  unfold bottomTarget at h
  rw [exact_DispatchControlAST.2.2.2.1] at h
  have hr := compositionRecover equalityTest
    (Fin.cons (.projection (2 : Fin 3)) (Fin.cons (atSource bottomOf) Fin.elim0))
    (suc z) tape ![y,t₀] h (fun j =>
      Fin.cases htarget (Fin.cases hbottom (fun k => Fin.elim0 k)) j)
  rw [equalEqn]
  exact equalityOfAcceptance y t₀ hr

private theorem freeAccepts (i : Program 1) (r : Program 3) (x w y c t n : OTerm α)
    (e : Nonempty (Derivation body Γ (equal x (packedFreeTerm c t n))))
    (h : Nonempty (Derivation body Γ (programGraph (refined i r) (suc z) ![x,w,y]))) :
    Nonempty (Derivation body Γ (equal y (packedBottomTerm c t) ⊓ programGraph i (suc z) ![y])) := by
  let tape : Fin 3 → OTerm α := ![x,w,y]
  let zeroArm := branch (atSource bottomSource) r (constantZero 3)
  let passed := conjunction bottomTarget (atTarget i)
  obtain ⟨hfree⟩ := exactRecognition.1 body α Γ x c t n e
  have hf := callSource freeSource (suc z) x w y ⟨Derivation.conjunctionLeft hfree⟩
  rw [branchAST i r] at h
  have hc := successorBranchElim (atSource freeSource) zeroArm (conjunction r passed)
    (suc z) z tape hf h
  obtain ⟨both⟩ := conjunctionRecover r passed tape hc
  obtain ⟨dataBits⟩ := conjunctionRecover bottomTarget (atTarget i) tape
    ⟨Derivation.conjunctionRight both⟩
  obtain ⟨shape⟩ := checkedTarget x w y c t ⟨Derivation.conjunctionRight hfree⟩
    ⟨Derivation.conjunctionLeft dataBits⟩
  obtain ⟨carrierGraph⟩ := takeTarget i (suc z) x w y ⟨Derivation.conjunctionRight dataBits⟩
  exact ⟨Derivation.conjunctionIntroduction shape carrierGraph⟩

private theorem bottomRejects (i : Program 1) (r : Program 3) (x w y c t : OTerm α)
    (e : Nonempty (Derivation body Γ (equal x (packedBottomTerm c t))))
    (h : Nonempty (Derivation body Γ (programGraph (refined i r) (suc z) ![x,w,y]))) :
    Nonempty (Derivation body Γ (⊥ : Formula α)) := by
  let tape : Fin 3 → OTerm α := ![x,w,y]
  let zeroArm := branch (atSource bottomSource) r (constantZero 3)
  let freeArm := conjunction r (conjunction bottomTarget (atTarget i))
  obtain ⟨hs⟩ := exactRecognition.2 body α Γ x c t e
  have hf := callSource freeSource z x w y ⟨Derivation.conjunctionLeft hs⟩
  have hb := callSource bottomSource (suc z) x w y ⟨Derivation.conjunctionRight hs⟩
  rw [branchAST i r] at h
  have selected := zeroBranchElim (atSource freeSource) zeroArm freeArm (suc z) tape hf h
  have impossible := successorBranchElim (atSource bottomSource) r (constantZero 3)
    (suc z) z tape hb selected
  obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z tape impossible (constantZeroValue tape)
  exact ⟨sucNeZeroApply bad⟩

theorem exactAcceptance : ExactOpenRefinedAtomicAcceptance :=
  ⟨fun i r _ _ _ => freeAccepts i r,fun i r _ _ _ => bottomRejects i r⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectBranchProof
