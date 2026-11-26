module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.RelationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepGeneralProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel RelationProof

def evolves {ctx : Nat} (tag atag ptag : Nat) (old new tail index fuel out rest : Term ctx) : Formula ctx :=
  .imp (relation atag ptag old new tail)
    (body atag ptag (kernelCall tag old index fuel) (kernelCall tag new index fuel) tail out rest)

theorem substKernel {m n : Nat} (sub : Fin m → Term n) tag (state index fuel : Term m) :
    substitute sub (kernelCall tag state index fuel) =
      kernelCall tag (substitute sub state) (substitute sub index) (substitute sub fuel) := by
  simp only [kernelCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem substEvolves {m n : Nat} (sub : Fin m → Term n) tag atag ptag (old new tail index fuel out rest : Term m) :
    substituteFormula sub (evolves tag atag ptag old new tail index fuel out rest) =
      evolves tag atag ptag (substitute sub old) (substitute sub new) (substitute sub tail)
        (substitute sub index) (substitute sub fuel) (substitute sub out) (substitute sub rest) := by
  simp only [evolves,substituteFormula,substRelation,substBody,substKernel]

theorem evolvesAt {ctx : Nat} tag atag ptag (old new tail index fuel out rest : Term ctx) :
    GorbowStandardInstances.instantiate (evolves tag atag ptag (.var 0) (liftTerm new) (liftTerm tail)
      (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest)) old =
      evolves tag atag ptag old new tail index fuel out rest := by
  simp only [GorbowStandardInstances.instantiate,substEvolves,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenEvolves {ctx : Nat} tag atag ptag (old new tail index fuel out rest : Term ctx) :
    GorbowPACore.weaken (evolves tag atag ptag old new tail index fuel out rest) =
      evolves tag atag ptag (liftTerm old) (liftTerm new) (liftTerm tail)
        (liftTerm index) (liftTerm fuel) (liftTerm out) (liftTerm rest) := by
  rw [GorbowPACore.weaken,substEvolves]
  rfl

noncomputable def oldTransport {T : Sentence → Prop} {ctx : Nat} tag atag ptag
    (old old' new tail index fuel out rest : Term ctx) :
    Derivation T (.imp (.equal old old') (.imp (evolves tag atag ptag old new tail index fuel out rest)
      (evolves tag atag ptag old' new tail index fuel out rest))) := by
  have he := Derivation.logical (A := T) (.equalityReplace
    (evolves tag atag ptag (.var 0) (liftTerm new) (liftTerm tail) (liftTerm index)
      (liftTerm fuel) (liftTerm out) (liftTerm rest)) old old')
  rwa [GorbowPACore.logicalFormula,evolvesAt,evolvesAt] at he

noncomputable def kernelCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (old new index fuel : Term ctx) (he : Hilbert.Local T ctx G (.equal old new)) :
    Hilbert.Local T ctx G (.equal (kernelCall tag old index fuel) (kernelCall tag new index fuel)) := by
  have h := localUnary (kernelCall tag (.var 0) (liftTerm index) (liftTerm fuel)) old new he
  simpa only [substKernel,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem someEvolves {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (h lines new tail index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves tag atag ptag (pairCall ptag (.succ h) lines) new tail index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let old := pairCall ptag (.succ h) lines
  let R := relation atag ptag old new tail
  let H := Formula.equal (kernelCall tag old index fuel) (pairCall ptag (.succ out) rest)
  have hr : Hilbert.Local T ctx [H,R] R := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
  have en : Hilbert.Local T ctx [H,R] (.equal new (pairCall ptag (.succ (pairCall atag h tail)) lines)) :=
    .mp (.mp (.base (instanceRule atag ptag old new tail h lines)) hr) (.base (.logical (.reflexive old)))
  obtain ⟨hs⟩ := StepGeneralProof.generalSuffix p tag atag ptag ctag v l a x ht ha hp hc index fuel h tail out rest lines
  have next := Hilbert.Local.mp (.base hs) hh
  have ek := kernelCongruence tag _ _ index fuel en
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ ek next)))⟩

theorem noneEvolves {n ctx : Nat} (p : Program n) (tag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (lines new tail index fuel out rest : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (evolves tag atag ptag (pairCall ptag .zero lines) new tail index fuel out rest)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let old := pairCall ptag .zero lines
  let R := relation atag ptag old new tail
  let H := Formula.equal (kernelCall tag old index fuel) (pairCall ptag (.succ out) rest)
  let Q := Formula.equal (kernelCall tag new index fuel) (pairCall ptag (.succ (pairCall atag out tail)) rest)
  obtain ⟨hn⟩ := NoneProof.noneReject p tag ptag ctag v l a x ht hp hc index fuel out rest lines
  have hh : Hilbert.Local T ctx [H,R] H := .hypothesis List.mem_cons_self
  have hout : Hilbert.Local T ctx [H,R] Q := Hilbert.Local.explosion Q hh (.base hn)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SimulationProof
