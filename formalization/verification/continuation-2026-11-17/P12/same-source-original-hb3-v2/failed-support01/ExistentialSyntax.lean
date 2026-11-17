module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ExistentialSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open SixSol20261112.Fuel NamedArithmeticGraph
open GorbowSubstitution GorbowFormulaSubstitution
def body {ctx : Nat} (tag index : Nat) (fuel u : Term ctx) : Formula (ctx+1) :=
 success tag (Term.numeral index) (liftTerm fuel) .zero (liftTerm u) (.var 0)
def outer {ctx : Nat} (tag index : Nat) (u : Term ctx) : Formula (ctx+1) :=
 .ex (body tag index (.var 0) (liftTerm u))
def prov {ctx : Nat} (tag index : Nat) (u : Term ctx) : Formula ctx :=
 .ex (outer tag index u)

theorem bodyAt {ctx : Nat} (tag index : Nat) (fuel u cert : Term ctx) :
 GorbowStandardInstances.instantiate (body tag index fuel u) cert =
 success tag (Term.numeral index) fuel .zero u cert := by
 simp only [GorbowStandardInstances.instantiate,body,FuelWitness.ExtractionLogicProof.substSuccess,
  Logic.substNumeral,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem outerAt {ctx : Nat} (tag index : Nat) (u fuel : Term ctx) :
 GorbowStandardInstances.instantiate (outer tag index u) fuel = .ex (body tag index fuel u) := by
 simp only [GorbowStandardInstances.instantiate,outer,body,substituteFormula,
  FuelWitness.ExtractionLogicProof.substSuccess,Logic.substNumeral,substitute,
  HistoryOrder.SupportProof.substituteLift,liftSubstitute,Fin.cases_zero,
  liftTerm,Support.shiftCancel]

theorem introduce {ctx : Nat} (U : Sentence → Prop) (tag index : Nat) (fuel u cert : Term ctx) :
 Nonempty (Derivation U (.imp (success tag (Term.numeral index) fuel .zero u cert)
  (prov tag index u))) := by
 have hi := HistoryOrder.SupportProof.existsIntroRule (T := U) (body tag index fuel u) cert
 rw [bodyAt] at hi
 have ho := HistoryOrder.SupportProof.existsIntroRule (T := U) (outer tag index u) fuel
 rw [outerAt] at ho
 exact ⟨Hilbert.compose ho hi⟩

theorem original {ctx : Nat} (pF : Program 1) (c : Code) (u : Term ctx) :
 prov (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c) u = applyProv pF c u := by
 simp only [prov,outer,body,success,inputs,applyProv,provability,substituteFormula,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Logic.substNumeral,
  liftSubstitute,Fin.cases_zero,Fin.cases_succ,liftTerm,renameTerm]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ExistentialSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ExistentialSyntax
