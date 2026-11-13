module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixOptionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixBoundedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset
open PrefixSupportProof HistoryLengthOffset.OffsetSupportProof (substLength)
def bounded {ctx : Nat} (itag ltag atag ptag : Nat) (count left right index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (lengthCall ltag left) count) (property itag ltag atag ptag left right index fuel)
def allBounded {ctx : Nat} (itag ltag atag ptag : Nat) (count right index fuel : Term ctx) : Formula ctx :=
  .all (bounded itag ltag atag ptag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index) (liftTerm fuel))
theorem substBounded {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag (count left right index fuel : Term m) :
    substituteFormula sub (bounded itag ltag atag ptag count left right index fuel)=
      bounded itag ltag atag ptag (substitute sub count) (substitute sub left) (substitute sub right) (substitute sub index) (substitute sub fuel) := by
  simp only [bounded,substituteFormula,substLength,substProperty]
theorem substAll {m n : Nat} (sub : Fin m → Term n) itag ltag atag ptag (count right index fuel : Term m) :
    substituteFormula sub (allBounded itag ltag atag ptag count right index fuel)=
      allBounded itag ltag atag ptag (substitute sub count) (substitute sub right) (substitute sub index) (substitute sub fuel) := by
  simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]
theorem allAt {ctx : Nat} itag ltag atag ptag (count left right index fuel : Term ctx) :
    GorbowStandardInstances.instantiate
      (bounded itag ltag atag ptag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index) (liftTerm fuel)) left =
      bounded itag ltag atag ptag count left right index fuel := by
  simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def allElim {T : Sentence → Prop} {ctx : Nat} itag ltag atag ptag (count left right index fuel : Term ctx) :
    Derivation T (.imp (allBounded itag ltag atag ptag count right index fuel) (bounded itag ltag atag ptag count left right index fuel)) := by
  have h := Derivation.logical (A := T) (.allInstantiate
    (bounded itag ltag atag ptag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index) (liftTerm fuel)) left)
  rwa [GorbowPACore.logicalFormula,allAt] at h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixBoundedProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixBoundedProof
