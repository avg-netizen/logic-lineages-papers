module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.SpecializationNaturality
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.LiteralNaturality
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open GorbowSubstitution GorbowFormulaSubstitution FixedFormulaSubstitution SixSol20261112.Fuel
open NaturalityProof SpecializationNaturality
@[simp] theorem literalSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (r13 headerTag : Nat)
 (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (q : Program 5) (peelTag baseTag : Nat) (r s : Term m) :
 substitute sub (RetainedBaseLiteralBinary.certificate K r13 headerTag pF0 pCK box q peelTag baseTag r s) =
 RetainedBaseLiteralBinary.certificate K r13 headerTag pF0 pCK box q peelTag baseTag (substitute sub r) (substitute sub s) := by
 simp only [RetainedBaseLiteralBinary.certificate,RetainedBaseLiteralBinary.aliasCertificate,
  RetainedBaseSourceCalculation.certificate,RetainedBaseSourceCalculation.peelCertificate,
  RetainedBaseSourceCalculation.peelCall,RetainedBaseSourceCalculation.rawCall,CorrectedAugmentationErasure.left,
  CurrentStructuralProducerCore.code,CurrentNamedAliasCertificate.headerCode,
  PrescribedRuntimeCallCongruence.headerValue,pairSubst,tupleValueSubst,rawNumeral,
  transSubst,unaryCertSubst,unarySubst,callValueSubst,seedSubst,numeralSubst,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,
  GorbowRegistryTuple.headerTerm,CurrentCalculationFormulaProgram.NativeProof.substPair,
  CurrentCalculationFormulaProgram.NativeProof.substTuple,List.map_cons,List.map_nil,substitute]

@[simp] theorem valueSubst {m ctx : Nat} (sub : Fin m → Term ctx) (pF : Program 1) (c : Code) (sigma : Sentence) :
 substitute sub (value (ctx := m) pF c sigma) = value (ctx := ctx) pF c sigma := by
 simp only [value,GorbowBooleanTruth.binaryCodeTerm,GorbowRegistryTuple.headerTerm,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  List.map_cons,List.map_nil,substitute,Logic.substNumeral]

@[simp] theorem leftArgsSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (fuel cert : Term m) :
 (leftArgs K pF c sigma fuel cert).map (substitute sub) = leftArgs K pF c sigma (substitute sub fuel) (substitute sub cert) := by
 simp only [leftArgs,List.Vector.map_cons,List.Vector.map_nil,numeralSubst,Logic.substNumeral,substitute]
@[simp] theorem rightArgsSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (fuel cert : Term m) :
 (rightArgs K pF c sigma fuel cert).map (substitute sub) = rightArgs K pF c sigma (substitute sub fuel) (substitute sub cert) := by
 simp only [rightArgs,CurrentCheckerSuccessCertificate.checkerInputs,List.Vector.map_cons,List.Vector.map_nil,
  numeralSubst,Logic.substNumeral,valueSubst,substitute]

@[simp] theorem certificateSubst {m ctx : Nat} (sub : Fin m → Term ctx) (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (fuel cert literalProof checkerProof : Term m) :
 substitute sub (certificate K pF c sigma fuel cert literalProof checkerProof) =
 certificate K pF c sigma (substitute sub fuel) (substitute sub cert) (substitute sub literalProof) (substitute sub checkerProof) := by
 simp only [certificate,transSubst,callValueSubst,callCertSubst,leftArgsSubst,rightArgsSubst,
  numeralSubst,Logic.substNumeral,substitute,List.Vector.map_cons,List.Vector.map_nil,reflSubst,
  ← List.Vector.get_map,leftArgsSubst]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.LiteralNaturality
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.LiteralNaturality
