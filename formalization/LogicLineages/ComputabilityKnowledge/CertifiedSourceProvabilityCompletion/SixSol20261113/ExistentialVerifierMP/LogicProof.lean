module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.LogicProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph

def certBody {ctx : Nat} (tag : Nat) (index context code fuel : Term ctx) : Formula (ctx+1) :=
 success tag (liftTerm index) (liftTerm fuel) (liftTerm context) (liftTerm code) (.var 0)
def fuelBody {ctx : Nat} (tag : Nat) (index context code : Term ctx) : Formula (ctx+1) :=
 .ex (certBody tag (liftTerm index) (liftTerm context) (liftTerm code) (.var 0))
def body {ctx : Nat} (tag : Nat) (index context code : Term ctx) : Formula (ctx+1+1) :=
 success tag (liftTerm (liftTerm index)) (.var 1) (liftTerm (liftTerm context)) (liftTerm (liftTerm code)) (.var 0)

theorem substCertBody {m n : Nat} (sub : Fin m → Term n) (tag : Nat) (index context code fuel : Term m) :
 substituteFormula (liftSubstitute sub) (certBody tag index context code fuel) =
 certBody tag (substitute sub index) (substitute sub context) (substitute sub code) (substitute sub fuel) := by
 simp only [certBody,FuelWitness.ExtractionLogicProof.substSuccess,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substFuelBody {m n : Nat} (sub : Fin m → Term n) (tag : Nat) (index context code : Term m) :
 substituteFormula (liftSubstitute sub) (fuelBody tag index context code) =
 fuelBody tag (substitute sub index) (substitute sub context) (substitute sub code) := by
 simp only [fuelBody,substituteFormula,substCertBody,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem substProvability {m n : Nat} (sub : Fin m → Term n) (tag : Nat) (index context code : Term m) :
 substituteFormula sub (provability tag index context code) =
 provability tag (substitute sub index) (substitute sub context) (substitute sub code) := by
 change substituteFormula sub (.ex (fuelBody tag index context code)) = .ex (fuelBody tag _ _ _)
 simp only [substituteFormula,substFuelBody]
theorem weakenProvability {ctx : Nat} (tag : Nat) (index context code : Term ctx) :
 GorbowPACore.weaken (provability tag index context code) = provability tag (liftTerm index) (liftTerm context) (liftTerm code) := by
 rw [GorbowPACore.weaken,substProvability]
 rfl

theorem certBodyAt {ctx : Nat} (tag : Nat) (index context code fuel cert : Term ctx) :
 GorbowStandardInstances.instantiate (certBody tag index context code fuel) cert = success tag index fuel context code cert := by
 simp only [GorbowStandardInstances.instantiate,certBody,FuelWitness.ExtractionLogicProof.substSuccess,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]
theorem fuelBodyAt {ctx : Nat} (tag : Nat) (index context code fuel : Term ctx) :
 GorbowStandardInstances.instantiate (fuelBody tag index context code) fuel = .ex (certBody tag index context code fuel) := by
 simp only [GorbowStandardInstances.instantiate,fuelBody,substituteFormula,substCertBody,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]

noncomputable def introduce {T : Sentence → Prop} {ctx : Nat} (tag : Nat) (index context code fuel cert : Term ctx) :
 Derivation T (.imp (success tag index fuel context code cert) (provability tag index context code)) := by
 have hc := HistoryOrder.SupportProof.existsIntroRule (T := T) (certBody tag index context code fuel) cert
 rw [certBodyAt] at hc
 have hf := HistoryOrder.SupportProof.existsIntroRule (T := T) (fuelBody tag index context code) fuel
 rw [fuelBodyAt] at hf
 exact Hilbert.compose hf hc

theorem eliminate (T : Sentence → Prop) {ctx : Nat} (tag : Nat) (index context code : Term ctx) (Q : Formula ctx)
 (h : Derivation T (.imp (body tag index context code) (GorbowPACore.weaken (GorbowPACore.weaken Q)))) :
 Nonempty (Derivation T (.imp (provability tag index context code) Q)) := by
 obtain ⟨hc⟩ := HBQuantifier.existentialElimination T (body tag index context code) (GorbowPACore.weaken Q) ⟨h⟩
 exact HBQuantifier.existentialElimination T (fuelBody tag index context code) Q ⟨hc⟩

theorem twoProvabilities (T : Sentence → Prop) {ctx : Nat} (tag : Nat) (index context codeI codeA : Term ctx) (Q : Formula ctx)
 (h : Derivation T (.imp
   (GorbowPACore.weaken (GorbowPACore.weaken (body tag index context codeI)))
   (.imp (body tag (liftTerm (liftTerm index)) (liftTerm (liftTerm context)) (liftTerm (liftTerm codeA)))
    (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken Q))))))) :
 Nonempty (Derivation T (.imp (provability tag index context codeI) (.imp (provability tag index context codeA) Q))) := by
 let A := body tag index context codeI
 let B := body tag (liftTerm (liftTerm index)) (liftTerm (liftTerm context)) (liftTerm (liftTerm codeA))
 let A4 := GorbowPACore.weaken (GorbowPACore.weaken A)
 let Q2 := GorbowPACore.weaken (GorbowPACore.weaken Q)
 let Q4 := GorbowPACore.weaken (GorbowPACore.weaken Q2)
 have ha : Hilbert.Local T (ctx+1+1+1+1) [A4,B] A4 := .hypothesis List.mem_cons_self
 have hb : Hilbert.Local T (ctx+1+1+1+1) [A4,B] B := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have result : Hilbert.Local T (ctx+1+1+1+1) [A4,B] Q4 := .mp (.mp (.base h) ha) hb
 have rev : Derivation T (.imp B (GorbowPACore.weaken (GorbowPACore.weaken (.imp A Q2)))) :=
  Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge result))
 obtain ⟨he⟩ := eliminate T tag (liftTerm (liftTerm index)) (liftTerm (liftTerm context)) (liftTerm (liftTerm codeA)) (.imp A Q2) rev
 let P := provability tag (liftTerm (liftTerm index)) (liftTerm (liftTerm context)) (liftTerm (liftTerm codeA))
 have ha2 : Hilbert.Local T (ctx+1+1) [P,A] A := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hp2 : Hilbert.Local T (ctx+1+1) [P,A] P := .hypothesis List.mem_cons_self
 have result2 : Hilbert.Local T (ctx+1+1) [P,A] Q2 := .mp (.mp (.base he) hp2) ha2
 have rev2 : Derivation T (.imp A (GorbowPACore.weaken (GorbowPACore.weaken (.imp (provability tag index context codeA) Q)))) := by
  simpa only [P,Q2,GorbowPACore.weaken,substituteFormula,substProvability,liftTerm,renameTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge result2))
 exact eliminate T tag index context codeI _ rev2
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.LogicProof
