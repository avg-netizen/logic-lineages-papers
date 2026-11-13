module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.CircuitProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph ArithmeticSupport

private def base : Program 2 := .projection 0
private def step : Program 4 := .projection 3

theorem selectZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨3,select⟩)
    (a b : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.zero ::ᵥ a ::ᵥ b ::ᵥ nil)) a)) := by
  have hbase := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨3,select⟩ 1 ⟨2,base⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 2 base step)
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 2 base step ht ctx (a ::ᵥ b ::ᵥ nil)
  obtain ⟨hb⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (0 : Fin 2) hbase (a ::ᵥ b ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hr hb⟩

theorem selectPositive {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨3,select⟩)
    (a b k : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.succ k ::ᵥ a ::ᵥ b ::ᵥ nil)) b)) := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag base step ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 2 base step ht ctx k (a ::ᵥ b ::ᵥ nil)
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+stepTag base) (3 : Fin 4) hs
    (k ::ᵥ call tag (k ::ᵥ a ::ᵥ b ::ᵥ nil) ::ᵥ a ::ᵥ b ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hr hp⟩

theorem pairEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,pair⟩)
    (a b : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (a ::ᵥ b ::ᵥ nil))
        (call (tag+1) (call (differenceTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ
          .add (.add (.mul a a) a) b ::ᵥ .add (.mul b b) a ::ᵥ nil)))) := by
  have hh := SixSol20261112.Fuel.Equations.argumentChild p tag select pairArguments ht 1
  have hl := SixSol20261112.Fuel.Equations.argumentChild p tag select pairArguments ht 2
  obtain ⟨hhigh⟩ := CircuitProof.highEquation p (tag+argumentTag select pairArguments 1) hh a b
  obtain ⟨hlow⟩ := CircuitProof.lowEquation p (tag+argumentTag select pairArguments 2) hl a b
  apply SixSol20261112.Fuel.Equations.compositionValues p tag select pairArguments ht
    (a ::ᵥ b ::ᵥ nil)
    (call (differenceTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ
      .add (.add (.mul a a) a) b ::ᵥ .add (.mul b b) a ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.logical (.reflexive _)⟩
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨hhigh⟩
    | succ i => cases i using Fin.cases with
      | zero => exact ⟨hlow⟩
      | succ i => exact Fin.elim0 i

private def selectCongruence {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    tag (s t a b : Term ctx) (h : Hilbert.Local T ctx gamma (.equal s t)) :
    Hilbert.Local T ctx gamma (.equal (call tag (s ::ᵥ a ::ᵥ b ::ᵥ nil))
      (call tag (t ::ᵥ a ::ᵥ b ::ᵥ nil))) := by
  have d := localUnary (call tag (.var 0 ::ᵥ liftTerm a ::ᵥ liftTerm b ::ᵥ nil)) s t h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,
    Support.shiftCancel,substitute,Fin.cases_zero] using d

theorem internalPairZero : Targets.InternalPairZero := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let test := call (differenceTag tag) (a ::ᵥ b ::ᵥ nil)
  let hi := Term.add (.add (.mul a a) a) b
  let lo := Term.add (.mul b b) a
  have hsel := SixSol20261112.Fuel.Equations.functionChild p tag select pairArguments ht
  obtain ⟨hp⟩ := pairEquation p tag ht a b
  obtain ⟨hz⟩ := selectZero p (tag+1) hsel hi lo
  have hh : Hilbert.Local T ctx [.equal test .zero] (.equal test .zero) :=
    .hypothesis List.mem_cons_self
  have hc := selectCongruence (tag+1) test .zero hi lo hh
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ (.base hp) (localTrans _ _ _ hc (.base hz))))⟩

theorem internalPairPositive : Targets.InternalPairPositive := by
  intro n p tag ht ctx a b k
  let T := GorbowPRNumeralCalculation.Theory p
  let test := call (differenceTag tag) (a ::ᵥ b ::ᵥ nil)
  let hi := Term.add (.add (.mul a a) a) b
  let lo := Term.add (.mul b b) a
  have hsel := SixSol20261112.Fuel.Equations.functionChild p tag select pairArguments ht
  obtain ⟨hp⟩ := pairEquation p tag ht a b
  obtain ⟨hz⟩ := selectPositive p (tag+1) hsel hi lo k
  have hh : Hilbert.Local T ctx [.equal test (.succ k)] (.equal test (.succ k)) :=
    .hypothesis List.mem_cons_self
  have hc := selectCongruence (tag+1) test (.succ k) hi lo hh
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ (.base hp) (localTrans _ _ _ hc (.base hz))))⟩

theorem internalCons : Targets.InternalCons := by
  intro n p tag ht ctx a b
  have hsucc := SixSol20261112.Fuel.Equations.functionChild p tag Program.succ
    (fun _ : Fin 1 => pair) ht
  obtain ⟨hc⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag 2 1 Program.succ
    (fun _ : Fin 1 => pair) ht ctx (a ::ᵥ b ::ᵥ nil)
  obtain ⟨hs⟩ := Support.intoRegistry p Program.succ (tag+1) hsucc _
    (NamedArithmeticGraph.Equations.successor (tag+1) ctx
      (call (tag+argumentTag Program.succ (fun _ : Fin 1 => pair) 0) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil))
  exact ⟨Logic.trans _ _ _ hc hs⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.PairProof
