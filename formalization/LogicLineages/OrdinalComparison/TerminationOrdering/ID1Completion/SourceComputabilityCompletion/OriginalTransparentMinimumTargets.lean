module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
open OriginalTransparentMinimum
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalTransparentMinimumClassSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ P : Program 3, ClassTestCalibrated n arity P

def ActualOriginalTransparentMinimumReflexiveCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1) (P : Program 3),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G → ClassTestCalibrated n arity P →
  ∀ v : List.Vector Nat 3,
    evaluate (reflexiveClassTest (OriginalTypedDecoder.target H G) P) v = evaluate P v

def ActualOriginalTransparentMinimumScanEvaluation : Prop :=
  ∀ (Q : Program 3) (v : List.Vector Nat 3), evaluate (scan Q) v =
    (List.range (v.get 0)).findIdx
      (fun candidate => decide (evaluate Q (List.Vector.ofFn ![v.get 1,candidate,v.get 2]) = 1))

def ActualOriginalTransparentMinimumCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1) (P : Program 3),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G → ClassTestCalibrated n arity P →
  ∀ v : List.Vector Nat 2,
    evaluate (minimum (OriginalTypedDecoder.target H G) P) v =
      InternalOriginalUniformParameterLeaves.representativeValue n arity v

def ActualOriginalTransparentMinimumInternalScan : Prop := ∀ Q : Program 3, ScanLaw Q

def ActualOriginalTransparentMinimumInternalReflexive : Prop :=
  ∀ (T : Program 2) (P : Program 3), ReflexiveLaw T P

def ActualOriginalTransparentMinimumInternalMinimum : Prop :=
  ∀ (T : Program 2) (P : Program 3), MinimumLaw T P

def ActualOriginalTransparentMinimumInternalGuardedClass : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    GuardedClassLaw p H G W P

def ActualOriginalTransparentMinimumLiteralFields : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    LiteralFields p H G W P

def ActualOriginalTransparentMinimumNativePreparation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
      (H G : Program 1) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G → ClassTestCalibrated n arity P →
  NativePreparation n arity p H G P

def ActualOriginalTransparentMinimumRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
      (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W → ClassTestCalibrated n arity P →
  Retained n arity p H G W P

def ActualOriginalTransparentMinimumSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
      Properties n arity p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
