module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.RelationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.StepGeneralProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.SimulationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel RelationProof

def premise {ctx : Nat} (ptag : Nat) (old new s t : Term ctx) : Formula ctx :=
 .conj (orderGuard s t) (relation ptag old new)
def evolves {ctx : Nat} (tag ptag : Nat) (old new index s t out rest : Term ctx) : Formula ctx :=
 .imp (premise ptag old new s t)
  (body ptag (kernelCall tag old index s) (kernelCall tag new index t) out rest)
theorem substKernel {m n : Nat} (sub : Fin m → Term n) tag (state index fuel : Term m) :
 substitute sub (kernelCall tag state index fuel) = kernelCall tag (substitute sub state) (substitute sub index) (substitute sub fuel) :=
 HistoryIteratorSuffix.SimulationProof.substKernel sub tag state index fuel
theorem substOrder {m n : Nat} (sub : Fin m → Term n) (s t : Term m) :
 substituteFormula sub (orderGuard s t) = orderGuard (substitute sub s) (substitute sub t) := by
 simp only [orderGuard,substituteFormula,substitute,HistoryOrder.SupportProof.substituteLift,liftSubstitute,Fin.cases_zero]
theorem substPremise {m n : Nat} (sub : Fin m → Term n) ptag (old new s t : Term m) :
 substituteFormula sub (premise ptag old new s t) = premise ptag (substitute sub old) (substitute sub new) (substitute sub s) (substitute sub t) := by
 simp only [premise,substituteFormula,substOrder,substRelation]
theorem substEvolves {m n : Nat} (sub : Fin m → Term n) tag ptag (old new index s t out rest : Term m) :
 substituteFormula sub (evolves tag ptag old new index s t out rest) =
 evolves tag ptag (substitute sub old) (substitute sub new) (substitute sub index) (substitute sub s) (substitute sub t) (substitute sub out) (substitute sub rest) := by
 simp only [evolves,substituteFormula,substPremise,substBody,substKernel]
theorem evolvesAt {ctx : Nat} tag ptag (old new index s t out rest : Term ctx) :
 GorbowStandardInstances.instantiate (evolves tag ptag (.var 0) (liftTerm new) (liftTerm index)
  (liftTerm s) (liftTerm t) (liftTerm out) (liftTerm rest)) old = evolves tag ptag old new index s t out rest := by
 simp only [GorbowStandardInstances.instantiate,substEvolves,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem weakenEvolves {ctx : Nat} tag ptag (old new index s t out rest : Term ctx) :
 GorbowPACore.weaken (evolves tag ptag old new index s t out rest) =
 evolves tag ptag (liftTerm old) (liftTerm new) (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm out) (liftTerm rest) := by
 rw [GorbowPACore.weaken,substEvolves]
 rfl
noncomputable def oldTransport {T : Sentence → Prop} {ctx : Nat} tag ptag
 (old old' new index s t out rest : Term ctx) :
 Derivation T (.imp (.equal old old') (.imp (evolves tag ptag old new index s t out rest)
  (evolves tag ptag old' new index s t out rest))) := by
 have he := Derivation.logical (A := T) (.equalityReplace
  (evolves tag ptag (.var 0) (liftTerm new) (liftTerm index) (liftTerm s) (liftTerm t) (liftTerm out) (liftTerm rest)) old old')
 rwa [GorbowPACore.logicalFormula,evolvesAt,evolvesAt] at he
noncomputable def kernelCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 tag (old new index fuel : Term ctx) (he : Hilbert.Local T ctx G (.equal old new)) :
 Hilbert.Local T ctx G (.equal (kernelCall tag old index fuel) (kernelCall tag new index fuel)) :=
 HistoryIteratorSuffix.SimulationProof.kernelCongruence tag old new index fuel he

theorem someEvolves {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (h lines new index s t out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (evolves tag ptag (pairCall ptag (.succ h) lines) new index s t out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let old := pairCall ptag (.succ h) lines
 let R := premise ptag old new s t
 let H := Formula.equal (kernelCall tag old index s) (pairCall ptag (.succ out) rest)
 have hr : Hilbert.Local T ctx [H,R] R := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
 have horder := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hr
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hr
 have en : Hilbert.Local T ctx [H,R] (.equal new old) :=
  .mp (.mp (.base (instanceRule ptag old new h lines)) hrel) (.base (.logical (.reflexive old)))
 obtain ⟨hs⟩ := StepGeneralProof.internalStep v l a x n p tag ptag ctag ht hp hc ctx index s t h lines out rest
 have next := Hilbert.Local.mp (.mp (.base hs) horder) hh
 have ek := kernelCongruence tag new old index t en
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ ek next)))⟩

theorem noneEvolves {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,kernel v l a (SaturatedAxiomLeaf.saturated x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (lines new index s t out rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (evolves tag ptag (pairCall ptag .zero lines) new index s t out rest)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let old := pairCall ptag .zero lines
 let R := premise ptag old new s t
 let H := Formula.equal (kernelCall tag old index s) (pairCall ptag (.succ out) rest)
 let Q := Formula.equal (kernelCall tag new index t) (pairCall ptag (.succ out) rest)
 obtain ⟨hn⟩ := HistoryIteratorSuffix.NoneProof.noneReject p tag ptag ctag v l a (SaturatedAxiomLeaf.saturated x) ht hp hc index s out rest lines
 have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
 have hout : Hilbert.Local T ctx [H,R] Q := Hilbert.Local.explosion Q hh (.base hn)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.SimulationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.SimulationProof
