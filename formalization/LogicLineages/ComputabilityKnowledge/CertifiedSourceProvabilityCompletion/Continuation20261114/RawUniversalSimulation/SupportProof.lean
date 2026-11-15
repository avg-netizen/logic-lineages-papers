module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.RelationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.SupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open RelationProof
def evolves {ctx : Nat} (ot nt ptag : Nat) (old new  index fuel out rest : Term ctx) : Formula ctx :=
  .imp (relation ptag old new )
    (body ptag (kernelCall ot old index fuel) (kernelCall nt new index fuel)  out rest)

theorem substKernel {m n : Nat} (sub : Fin m → Term n) tag (state index fuel : Term m) :
    substitute sub (kernelCall tag state index fuel) =
      kernelCall tag (substitute sub state) (substitute sub index) (substitute sub fuel) := by
  simp only [kernelCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substEvolves {m n : Nat} (sub : Fin m → Term n) ot nt ptag (old new  index fuel out rest : Term m) :
    substituteFormula sub (evolves ot nt ptag old new  index fuel out rest) =
      evolves ot nt ptag (substitute sub old) (substitute sub new) 
        (substitute sub index) (substitute sub fuel) (substitute sub out) (substitute sub rest) := by
  simp only [evolves,substituteFormula,substRelation,substBody,substKernel]

theorem evolvesAt {ctx : Nat} ot nt ptag (old new  index fuel out rest : Term ctx) :
    GorbowStandardInstances.instantiate (evolves ot nt ptag (.var 0) (liftTerm new) 
      (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) old =
      evolves ot nt ptag old new  index fuel out rest := by
  simp only [GorbowStandardInstances.instantiate,substEvolves,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenEvolves {ctx : Nat} ot nt ptag (old new  index fuel out rest : Term ctx) :
    GorbowPACore.weaken (evolves ot nt ptag old new  index fuel out rest) =
      evolves ot nt ptag (liftTerm old) (liftTerm new) 
        (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) := by
  rw [GorbowPACore.weaken,substEvolves]
  rfl

noncomputable def oldTransport {T : Sentence → Prop} {ctx : Nat} ot nt ptag
    (old old' new  index fuel out rest : Term ctx) :
    Derivation T (.imp (.equal old old') (.imp (evolves ot nt ptag old new  index fuel out rest)
      (evolves ot nt ptag old' new  index fuel out rest))) := by
  have he := Derivation.logical (A := T) (.equalityReplace
    (evolves ot nt ptag (.var 0) (liftTerm new)  (liftTerm index)
      (liftTerm fuel) (liftTerm out) (liftTerm rest)) old old')
  rwa [GorbowPACore.logicalFormula,evolvesAt,evolvesAt] at he

noncomputable def kernelCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (old new index fuel : Term ctx) (he : Hilbert.Local T ctx G (.equal old new)) :
    Hilbert.Local T ctx G (.equal (kernelCall tag old index fuel) (kernelCall tag new index fuel)) := by
  have h := localUnary (kernelCall tag (.var 0) (liftTerm index) (liftTerm fuel)) old new he
  simpa only [substKernel,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.SupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.SupportProof
