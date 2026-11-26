module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.CodeTransportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph ExistentialVerifierMP

theorem substSuccess {m n : Nat} (sub : Fin m → Term n) tag (index fuel context code cert : Term m) :
 substituteFormula sub (success tag index fuel context code cert) =
 success tag (substitute sub index) (substitute sub fuel) (substitute sub context) (substitute sub code) (substitute sub cert) := by
 simp only [success,inputs,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral]
theorem substProv {m n : Nat} (sub : Fin m → Term n) tag (index context code : Term m) :
 substituteFormula sub (provability tag index context code) =
 provability tag (substitute sub index) (substitute sub context) (substitute sub code) :=
 ExistentialVerifierMP.LogicProof.substProvability sub tag index context code

theorem provAt {ctx : Nat} tag (index context code : Term ctx) :
 GorbowStandardInstances.instantiate (provability tag (liftTerm index) (liftTerm context) (.var 0)) code =
 provability tag index context code := by
 simp only [GorbowStandardInstances.instantiate,substProv,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def codeTransport {T : Sentence → Prop} {ctx : Nat} tag (index context a b : Term ctx)
 (he : Derivation T (.equal a b)) : Derivation T (.imp (provability tag index context a) (provability tag index context b)) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (provability tag (liftTerm index) (liftTerm context) (.var 0)) a b)
 rw [GorbowPACore.logicalFormula,provAt,provAt] at h
 exact .mp h he

theorem applyProvEq {ctx : Nat} (pF : GorbowPRProgram.Program 1) (c : GorbowEnumeratedProvability.Code) (code : Term ctx) :
 GorbowPublishedDCB.applyProv pF c code = provability (GorbowNamedInternalProvability.checkerTag pF)
  (Term.numeral (Encodable.encode c)) .zero code := by
 simp only [GorbowPublishedDCB.applyProv,GorbowPublishedDCB.provability,provability,success,inputs,
  substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,Logic.substNumeral,
  substitute,liftSubstitute,Fin.cases_zero,Fin.cases_succ,liftTerm,renameTerm]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.CodeTransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.CodeTransportProof
