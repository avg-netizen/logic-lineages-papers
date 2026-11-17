module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.NaturalityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.SpecializationNaturality
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open GorbowSubstitution GorbowFormulaSubstitution FixedFormulaSubstitution SixSol20261112.Fuel
open NaturalityProof
@[simp] theorem formulaValueSubst {n depth inputs m ctx : Nat} (sub : Fin m → Term ctx) (ctag atag : Nat)
 (e : Environment n depth inputs) (raw : List.Vector (Term m) inputs) (f : Formula n) :
 substitute sub (formulaValue ctag atag raw f e) = formulaValue ctag atag (raw.map (substitute sub)) f e := by
 induction f generalizing depth with
 | equal t u => simp only [formulaValue,binarySubst,termValueSubst]
 | universalRelation t => simp only [formulaValue,unarySubst,termValueSubst]
 | agent t => simp only [formulaValue,unarySubst,termValueSubst]
 | knowledgeAll t => simp only [formulaValue,unarySubst,termValueSubst]
 | knowledge t u => simp only [formulaValue,binarySubst,termValueSubst]
 | truth t => simp only [formulaValue,unarySubst,termValueSubst]
 | neg f ih => simp only [formulaValue,unarySubst,ih]
 | imp f g ihf ihg => simp only [formulaValue,binarySubst,ihf,ihg]
 | conj f g ihf ihg => simp only [formulaValue,binarySubst,ihf,ihg]
 | disj f g ihf ihg => simp only [formulaValue,binarySubst,ihf,ihg]
 | all f ih => simp only [formulaValue,unarySubst,ih]
 | ex f ih => simp only [formulaValue,unarySubst,ih]

@[simp] theorem specializeSubst {n m ctx : Nat} (sub : Fin m → Term ctx) (mtag ctag atag r13 : Nat)
 (f : Formula n) (raw : List.Vector (Term m) n) (ant : Term m) :
 substitute sub (PrescribedRuntimeSpecialization.certificate mtag ctag atag r13 f raw ant) =
 PrescribedRuntimeSpecialization.certificate mtag ctag atag r13 f (raw.map (substitute sub)) (substitute sub ant) := by
 induction n with
 | zero => rfl
 | succ n ih =>
  simp only [PrescribedRuntimeSpecialization.certificate,UniformRuntimeSpecializationStep.certificate,
   UniformRuntimeSpecializationStep.body,mpSubst,formulaValueSubst,UniformClosedRule13Certificate.certificate,
   UniformClosedRule13.lineCall,HistoryLookup.consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   substitute,List.Vector.head_map,List.Vector.tail_map,ih]

@[simp] theorem seedSubst {n m ctx : Nat} (sub : Fin m → Term ctx) (mtag ctag atag r13 : Nat)
 (f : Formula n) (raw : List.Vector (Term m) n) :
 substitute sub (PrescribedSourceAxiomSpecialization.certificate mtag ctag atag r13 f raw) =
 PrescribedSourceAxiomSpecialization.certificate mtag ctag atag r13 f (raw.map (substitute sub)) := by
 simp only [PrescribedSourceAxiomSpecialization.certificate,specializeSubst,Logic.substNumeral]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.SpecializationNaturality
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.SpecializationNaturality
