module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NativeProof
open GorbowSyntax GorbowPRProgram SixSol20261113 List.Vector
open HistoryRuleSuffix.NativeProof

theorem counterInputs {m : Nat} (n previous : Nat) (params : List.Vector Nat m) :
 (List.Vector.ofFn fun i => evaluate (atCounter m i) (n ::ᵥ previous ::ᵥ params)) = n ::ᵥ params := by
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => simp [atCounter,evaluate]
theorem successorInputs {m : Nat} (n previous : Nat) (params : List.Vector Nat m) :
 (List.Vector.ofFn fun i => evaluate (atSuccessor m i) (n ::ᵥ previous ::ᵥ params)) = (n+1) ::ᵥ params := by
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => simp [atSuccessor,evaluate]
theorem joinEval {m : Nat} (formula step : Program (m+1)) (n previous : Nat) (params : List.Vector Nat m) :
 evaluate (join formula step) (n ::ᵥ previous ::ᵥ params) =
 evaluate LiteralRawMP.constructor (0 ::ᵥ evaluate formula ((n+1) ::ᵥ params) ::ᵥ
  evaluate step (n ::ᵥ params) ::ᵥ previous ::ᵥ nil) := by
 change evaluate LiteralRawMP.constructor _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => change evaluate formula _ = _; rw [successorInputs]; rfl
   | succ i => cases i using Fin.cases with
     | zero => change evaluate step _ = _; rw [counterInputs]; rfl
     | succ i => cases i using Fin.cases with
       | zero => rfl
       | succ i => exact Fin.elim0 i

theorem raw : Targets.NativeRawTrace := by
 intro m base formula step params counter
 induction counter with
 | zero => rfl
 | succ n ih =>
  change evaluate (join formula step) (n ::ᵥ evaluate (producer base formula step) (n ::ᵥ params) ::ᵥ params) = _
  rw [joinEval,LiteralRawMP.NativeProof.nativeRaw.2,ih]
  rfl

theorem original : Targets.NativeOriginalTrace := by
 intro m base formula step params phi hf counter
 induction counter with
 | zero => rfl
 | succ n ih =>
  change evaluate (join formula step) (n ::ᵥ evaluate (producer base formula step) (n ::ᵥ params) ::ᵥ params) = _
  rw [joinEval,hf,LiteralRawMP.NativeProof.nativeEven,ih]
  rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NativeProof
