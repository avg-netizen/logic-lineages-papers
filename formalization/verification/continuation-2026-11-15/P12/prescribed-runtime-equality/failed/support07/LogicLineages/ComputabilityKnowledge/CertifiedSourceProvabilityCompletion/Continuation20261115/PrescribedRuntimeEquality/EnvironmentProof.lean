module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open FixedFormulaSubstitution GorbowFormulaSubstitution
/-- Additional closed coordinate stores f[t]; old coordinates are shifted once. -/
def prepend {n inputs : Nat} (e : Environment n 1 inputs) : Environment (n+1) 1 (inputs+1) :=
 Fin.cases (.inr 0) (fun i => match e i with
  | .inl j => .inl j
  | .inr j => .inr j.succ)
def matrix {n : Nat} (f : Term n) : Formula (n+1) :=
 .equal (.var 0) (renameTerm Fin.succ f)
theorem shifted {n inputs ctx : Nat} (ctag atag : Nat) (e : Environment n 1 inputs)
 (raw : List.Vector (Term ctx) inputs) (head : Term ctx) (f : Term n) :
 termValue ctag atag (prepend e) (head ::ᵥ raw) (renameTerm Fin.succ f) =
 termValue ctag atag e raw f := by
 induction f with
 | var i => cases h : e i <;> simp [renameTerm,termValue,prepend,h]
 | zero => rfl
 | succ t ih => simp only [renameTerm,termValue,ih]
 | add t u iht ihu => simp only [renameTerm,termValue,iht,ihu]
 | mul t u iht ihu => simp only [renameTerm,termValue,iht,ihu]
 | universalFunction t ih => simp only [renameTerm,termValue,ih]
theorem specializedShifted {n inputs ctx : Nat} (ctag atag : Nat) (e : Environment n 1 inputs)
 (raw : List.Vector (Term ctx) inputs) (head replacement : Term ctx) (f : Term n) :
 termValue ctag atag (UniformRuntimeEnvironmentAgreement.specialize (prepend e))
  (replacement ::ᵥ head ::ᵥ raw) (renameTerm Fin.succ f) =
 specializedValue ctag atag e f raw replacement := by
 induction f with
 | var i => cases h : e i <;>
   simp [renameTerm,termValue,prepend,specializedValue,UniformRuntimeEnvironmentAgreement.specialize,h]
 | zero => rfl
 | succ t ih => simp only [renameTerm,termValue,specializedValue] at ih ⊢; rw [ih]
 | add t u iht ihu => simp only [renameTerm,termValue,specializedValue] at iht ihu ⊢; rw [iht,ihu]
 | mul t u iht ihu => simp only [renameTerm,termValue,specializedValue] at iht ihu ⊢; rw [iht,ihu]
 | universalFunction t ih => simp only [renameTerm,termValue,specializedValue] at ih ⊢; rw [ih]
theorem matrixValue {n inputs ctx : Nat} (ctag atag : Nat) (e : Environment n 1 inputs)
 (raw : List.Vector (Term ctx) inputs) (head : Term ctx) (f : Term n) :
 formulaValue ctag atag (head ::ᵥ raw) (matrix f) (prepend e) =
 equalValue ctag atag head (termValue ctag atag e raw f) := by
 simp only [matrix,formulaValue,termValue,prepend,Fin.cases_zero,List.Vector.get_cons_zero]
 rw [shifted]
 rfl
theorem matrixSpecialized {n inputs ctx : Nat} (ctag atag : Nat) (e : Environment n 1 inputs)
 (raw : List.Vector (Term ctx) inputs) (head replacement : Term ctx) (f : Term n) :
 formulaValue ctag atag (replacement ::ᵥ head ::ᵥ raw) (matrix f)
  (UniformRuntimeEnvironmentAgreement.specialize (prepend e)) =
 equalValue ctag atag head (specializedValue ctag atag e f raw replacement) := by
 change equalValue ctag atag head
  (termValue ctag atag (UniformRuntimeEnvironmentAgreement.specialize (prepend e))
   (replacement ::ᵥ head ::ᵥ raw) (renameTerm Fin.succ f)) = _
 rw [specializedShifted]
def transEnvironment : Environment 2 1 1 := Fin.cases (.inr 0) (Fin.cases (.inl 0) Fin.elim0)
def transMatrix : Formula 2 := .equal (.var 0) (.var 1)
theorem transValue {ctx : Nat} (ctag atag : Nat) (t : Term ctx) :
 formulaValue ctag atag (t ::ᵥ nil) transMatrix transEnvironment =
 equalValue ctag atag t (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1))))) := by
 rfl
theorem transSpecialized {ctx : Nat} (ctag atag : Nat) (t u : Term ctx) :
 formulaValue ctag atag (u ::ᵥ t ::ᵥ nil) transMatrix
  (UniformRuntimeEnvironmentAgreement.specialize transEnvironment) = equalValue ctag atag t u := by
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
