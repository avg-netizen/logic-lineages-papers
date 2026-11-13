module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.DoubleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.TailProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralCheckerAuxiliaries
open LiteralCheckerAcceptance.WitnessProof

def tailBody {ctx : Nat} (ptag ctag : Nat) (state context raw : Term ctx) : Formula (ctx+1) :=
 .equal (liftTerm state) (successfulState ptag ctag (liftTerm context) (liftTerm raw) (.var 0) .zero)
def tailWitness {ctx : Nat} (ptag ctag : Nat) (state context raw : Term ctx) : Formula ctx :=
 .ex (tailBody ptag ctag state context raw)
theorem tailAt {ctx : Nat} ptag ctag (state context raw tail : Term ctx) :
 GorbowStandardInstances.instantiate (tailBody ptag ctag state context raw) tail =
 .equal state (successfulState ptag ctag context raw tail .zero) := by
 simp only [tailBody,GorbowStandardInstances.instantiate,substituteFormula,substState,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem substTail {m n : Nat} (sub : Fin m → Term n) ptag ctag (state context raw : Term m) :
 substituteFormula sub (tailWitness ptag ctag state context raw) =
 tailWitness ptag ctag (substitute sub state) (substitute sub context) (substitute sub raw) := by
 simp only [tailWitness,tailBody,substituteFormula,substState,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def introTail {T : Sentence → Prop} {ctx : Nat} ptag ctag (state context raw tail : Term ctx) :
 Derivation T (.imp (.equal state (successfulState ptag ctag context raw tail .zero)) (tailWitness ptag ctag state context raw)) := by
 have h := HistoryOrder.SupportProof.existsIntroRule (T := T) (tailBody ptag ctag state context raw) tail
 rw [tailAt] at h
 exact h
noncomputable def transportRaw {T : Sentence → Prop} {ctx : Nat} ptag ctag (state context a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (tailWitness ptag ctag state context a) (tailWitness ptag ctag state context b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (tailWitness ptag ctag (liftTerm state) (liftTerm context) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substTail,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem bodyToTail (T : Sentence → Prop) {ctx : Nat} ptag ctag (state context raw chosen tail : Term ctx) :
 Nonempty (Derivation T (.imp (body ptag ctag state context (.add raw raw) chosen tail)
  (tailWitness ptag ctag state context raw))) := by
 let H := body ptag ctag state context (.add raw raw) chosen tail
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hd := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hs := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨hi⟩ := DoubleProof.injective T raw chosen
 have he := Hilbert.Local.mp (.base hi) hd
 have hw := Hilbert.Local.mp (.base (introTail ptag ctag state context chosen tail)) hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (transportRaw ptag ctag state context chosen raw)) (HistoryOrder.StepProof.localSym _ _ he)) hw))⟩

theorem innerToTail (T : Sentence → Prop) {ctx : Nat} ptag ctag (state context raw chosen : Term ctx) :
 Nonempty (Derivation T (.imp (.ex (inner ptag ctag state context (.add raw raw) chosen))
  (tailWitness ptag ctag state context raw))) := by
 obtain ⟨h⟩ := bodyToTail T ptag ctag (liftTerm state) (liftTerm context) (liftTerm raw) (liftTerm chosen) (.var (0 : Fin (ctx+1)))
 have hb : Derivation T (.imp (inner ptag ctag state context (.add raw raw) chosen)
  (GorbowPACore.weaken (tailWitness ptag ctag state context raw))) := by
  simpa only [inner,GorbowPACore.weaken,substTail,liftTerm,renameTerm,substitute] using h
 exact HBQuantifier.existentialElimination T _ _ ⟨hb⟩

theorem witnessToTail (T : Sentence → Prop) {ctx : Nat} ptag ctag (state context raw : Term ctx) :
 Nonempty (Derivation T (.imp (witness ptag ctag state context (.add raw raw))
  (tailWitness ptag ctag state context raw))) := by
 obtain ⟨h⟩ := innerToTail T ptag ctag (liftTerm state) (liftTerm context) (liftTerm raw) (.var (0 : Fin (ctx+1)))
 have hb : Derivation T (.imp (outer ptag ctag state context (.add raw raw))
  (GorbowPACore.weaken (tailWitness ptag ctag state context raw))) := by
  simpa only [outer,GorbowPACore.weaken,substTail,liftTerm,renameTerm,substitute] using h
 exact HBQuantifier.existentialElimination T _ _ ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.TailProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.TailProof
