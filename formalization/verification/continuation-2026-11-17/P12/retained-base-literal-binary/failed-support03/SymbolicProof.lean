module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.SymbolicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution

theorem raw {arity ctx : Nat} (p : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K) (r s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (rawBinary K r s) (unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s)))) := by
 obtain ⟨hh⟩ := CurrentNamedAliasCertificate.EncodingProof.header p K H
  (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
  (LiteralNumeralPrefix.numeralCall K.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag s ::ᵥ nil)
  0 ((Term.var 0 : Term 2) ::ᵥ .var 1 ::ᵥ nil)
 have hget : (LiteralNumeralPrefix.numeralCall K.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag s ::ᵥ nil).get (1 : Fin 2) = LiteralNumeralPrefix.numeralCall K.numeralTag s := rfl
 have h := CurrentCompositionCertificate.CodecProof.unary p K.ctag K.ctag 5 H.hc H.hc _ _ hh
 simpa only [rawBinary,GorbowBooleanTruth.binaryCodeTerm,termValue,List.Vector.map_cons,List.Vector.map_nil,
  PrescribedRuntimeSpecialization.runtimeEnvironment,List.Vector.get_cons_zero,List.Vector.get_cons_succ,
  CurrentNamedAliasCertificate.headerCode,hget,List.Vector.toList_cons,List.Vector.toList_nil,Term.numeral] using h

theorem namedAlias {ctx : Nat} (pF pR : Program 1) (q : Program 5) (r s : Term ctx) :
 Nonempty (Derivation (S pF pR q) (.equal (GorbowBooleanTruth.binaryCodeTerm 0 r s)
  (call 6 (GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil)))) := by
 have hvars : argumentVariables 2 = ((Term.var 0 : Term 2) ::ᵥ .var 1 ::ᵥ nil) := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
 have hget : (r ::ᵥ s ::ᵥ nil).get (1 : Fin 2) = s := rfl
 let subst : Fin 2 → Term ctx := (r ::ᵥ s ::ᵥ nil).get
 obtain ⟨h⟩ := GorbowPRSymbolicEquations.Proof.openAxiomSpecialization (S pF pR q) 2 ctx
  CurrentNamedAliasCertificate.matrix subst (CurrentNamedAliasCertificate.Membership.source pF pR q)
 simpa only [GorbowPRSymbolicEquations.symbolicInstance,CurrentNamedAliasCertificate.matrix,
  GorbowFormulaSubstitution.substituteFormula,GorbowSubstitution.substitute,
  GorbowNamedDefiningTheory.headerVariables,GorbowRegistryTuple.headerTerm,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,call,← List.Vector.toList_map,
  hvars,List.Vector.get_ofFn,
  List.Vector.map_cons,List.Vector.map_nil,subst,List.Vector.get_cons_zero,List.Vector.get_cons_succ,
  GorbowBooleanTruth.binaryCodeTerm,hget,List.Vector.toList_cons,List.Vector.toList_nil,GorbowSourceRegistryPadding.functionTag,Term.numeral] using (show Nonempty _ from ⟨h⟩)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.SymbolicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.SymbolicProof
