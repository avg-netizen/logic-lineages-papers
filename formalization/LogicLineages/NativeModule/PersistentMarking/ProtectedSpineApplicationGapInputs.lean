module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineApplicationCounterexampleTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineInterpretationProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorInventoryProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyBoundsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineApplicationGapInputs
open Spine NameBridge DecisionInventory DecisionPorts HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineApplicationCounterexampleTargets

theorem sourcePaper (S : Signature) : PaperTerm S source (.arrow .ground .ground) :=
  ⟨.head .nil,⟨⟨1,rfl⟩,trivial⟩⟩

theorem targetPaper (S : Signature) : PaperTerm S target (.arrow .ground .ground) :=
  ⟨.lam .free,trivial⟩

theorem sourceOrdinary : Ordinary source := trivial
theorem targetOrdinary : Ordinary target := trivial

theorem contextValid : WellFormed inputEnvironment.types inputEnvironment.ports context := by
  refine ⟨rfl,?_⟩
  intro i σ h
  cases i <;> simp [context] at h

theorem groundInInventory : .ground ∈ inputEnvironment.types := by decide

theorem bottomRetained : bottomFamily ∈ MarkedFamilyCoherence.retained inputEnvironment sourceHeads :=
  (MarkedFamilyBoundsProof.join inputEnvironment sourceHeads [] (by simp)).1

theorem initialAssignments : InputValid inputEnvironment context ⟨[],[]⟩ :=
  ⟨contextValid,by simp [ProtectedSpineEnvironmentTargets.FreeValid],
    by simp [ProtectedSpineEnvironmentTargets.BoundValid]⟩

theorem callTyped : CallTyped EmptyContext source.type arguments .ground := .cons .free .nil

theorem application : apply source arguments = some result := by
  simp [apply,source,arguments,argument,result,applyAux,consumeTypes,Head.result,Expr.type,substituteArgs]

theorem argumentRetained (S : Signature) :
    interpreted S argument ∈ (descriptor inputEnvironment .ground).carriers context :=
  (ProtectedSpineEncodingProof.encodeAt inputEnvironment .ground
    (evaluate S inputEnvironment sourceHeads bottomFamily argument)
    (ProtectedSpineVariableProof.free S inputEnvironment sourceHeads bottomFamily .ground 0)
    context ⟨[],[]⟩ initialAssignments).1

end LogicLineages.PersistentMarking.ProtectedSpineApplicationGapInputs
