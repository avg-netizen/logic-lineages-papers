module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.BoundedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset
open SupportProof
open HistoryLengthOffset.OffsetSupportProof (substLength)
def bounded {ctx : Nat} (itag ltag  ptag : Nat) (count left  index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (lengthCall ltag left) count) (property itag ltag  ptag left  index fuel)
def allBounded {ctx : Nat} (itag ltag  ptag : Nat) (count  index fuel : Term ctx) : Formula ctx :=
  .all (bounded itag ltag  ptag (liftTerm count) (.var 0)  (liftTerm index) (liftTerm fuel))
theorem substBounded {m n : Nat} (sub : Fin m → Term n) itag ltag  ptag (count left  index fuel : Term m) :
    substituteFormula sub (bounded itag ltag  ptag count left  index fuel)=
      bounded itag ltag  ptag (substitute sub count) (substitute sub left)  (substitute sub index) (substitute sub fuel) := by
  simp only [bounded,substituteFormula,substLength,substProperty]
theorem substAll {m n : Nat} (sub : Fin m → Term n) itag ltag  ptag (count  index fuel : Term m) :
    substituteFormula sub (allBounded itag ltag  ptag count  index fuel)=
      allBounded itag ltag  ptag (substitute sub count)  (substitute sub index) (substitute sub fuel) := by
  simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,
    substitute,liftSubstitute,Fin.cases_zero]
theorem allAt {ctx : Nat} itag ltag  ptag (count left  index fuel : Term ctx) :
    GorbowStandardInstances.instantiate
      (bounded itag ltag  ptag (liftTerm count) (.var 0)  (liftTerm index) (liftTerm fuel)) left =
      bounded itag ltag  ptag count left  index fuel := by
  simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def allElim {T : Sentence → Prop} {ctx : Nat} itag ltag  ptag (count left  index fuel : Term ctx) :
    Derivation T (.imp (allBounded itag ltag  ptag count  index fuel) (bounded itag ltag  ptag count left  index fuel)) := by
  have h := Derivation.logical (A := T) (.allInstantiate
    (bounded itag ltag  ptag (liftTerm count) (.var 0)  (liftTerm index) (liftTerm fuel)) left)
  rwa [GorbowPACore.logicalFormula,allAt] at h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.BoundedProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.BoundedProof
