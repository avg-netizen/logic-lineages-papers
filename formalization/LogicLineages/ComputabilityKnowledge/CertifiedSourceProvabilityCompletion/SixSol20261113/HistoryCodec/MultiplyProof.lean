module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.AddProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.MultiplyProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph ArithmeticSupport

private def base : Program 1 := zeroProgram 1
private def step : Program 3 := .composition add
  (Fin.cases (.projection (1 : Fin 3)) (Fin.cases (.projection (2 : Fin 3)) Fin.elim0))

theorem zero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,multiply⟩)
    (b : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.zero ::ᵥ b ::ᵥ nil)) .zero)) := by
  have hbase := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,multiply⟩ 1 ⟨1,base⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 base step)
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 base step ht ctx (b ::ᵥ nil)
  have hf := SixSol20261112.Fuel.Equations.functionChild p (tag+1) Program.zero Fin.elim0 hbase
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p (tag+1) Program.zero Fin.elim0 hbase
    (b ::ᵥ nil) nil (fun i => Fin.elim0 i)
  obtain ⟨hz⟩ := Support.intoRegistry p Program.zero (tag+1+1) hf _
    (NamedArithmeticGraph.Equations.zero (tag+1+1) ctx)
  exact ⟨Logic.trans _ _ _ hr (Logic.trans _ _ _ hc hz)⟩

private def indices : Fin 2 → Fin 3 := Fin.cases 1 (Fin.cases 2 Fin.elim0)
private def args : Fin 2 → Program 3 :=
  Fin.cases (.projection 1) (Fin.cases (.projection 2) Fin.elim0)
private theorem projections (i : Fin 2) : args i = .projection (indices i) := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

private theorem vector {ctx : Nat} (a previous b : Term ctx) :
    (List.Vector.ofFn fun i => (a ::ᵥ previous ::ᵥ b ::ᵥ nil).get (indices i)) =
      previous ::ᵥ b ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem successor {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,multiply⟩)
    (a b : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (.succ a ::ᵥ b ::ᵥ nil)) (.add b (call tag (a ::ᵥ b ::ᵥ nil))))) := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag base step ht
  have hf := SixSol20261112.Fuel.Equations.functionChild p (tag+stepTag base) add args hs
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1 base step ht ctx a (b ::ᵥ nil)
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionProjections p (tag+stepTag base) add args hs
    indices projections (a ::ᵥ call tag (a ::ᵥ b ::ᵥ nil) ::ᵥ b ::ᵥ nil)
  rw [vector] at hc
  obtain ⟨hv⟩ := AddProof.internalAdd n p (tag+stepTag base+1) hf ctx
    (call tag (a ::ᵥ b ::ᵥ nil)) b
  exact ⟨Logic.trans _ _ _ hr (Logic.trans _ _ _ hc hv)⟩

private def template {ctx : Nat} (tag : Nat) (b : Term ctx) : Formula (ctx+1) :=
  .equal (call tag (.var 0 ::ᵥ liftTerm b ::ᵥ nil)) (.mul (liftTerm b) (.var 0))
private theorem templateAt {ctx : Nat} tag (b a : Term ctx) :
    GorbowStandardInstances.instantiate (template tag b) a =
      .equal (call tag (a ::ᵥ b ::ᵥ nil)) (.mul b a) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalMultiply : Targets.InternalMultiply := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag b
  obtain ⟨hz⟩ := zero p tag ht b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag b from rfl,templateAt]
    exact Logic.trans _ _ _ hz (Support.equalitySymmetry _ _ (.arithmetic (.mulZero b)))
  obtain ⟨hnext⟩ := successor p tag ht (.var 0) (liftTerm b)
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (call tag (.var 0 ::ᵥ liftTerm b ::ᵥ nil)) (.mul (liftTerm b) (.var 0))) :=
    .hypothesis List.mem_cons_self
  have hc := localUnary (.add (liftTerm (liftTerm b)) (.var 0)) _ _ ih
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (template tag b)))
    simp only [GorbowStandardInduction.successorInstance,template,substituteFormula,Logic.substCall,
      List.Vector.map_cons,List.Vector.map_nil,substitute,successorLift,Fin.cases_zero]
    have hend : Derivation T (.equal (.add (liftTerm b) (.mul (liftTerm b) (.var 0)))
        (.mul (liftTerm b) (.succ (.var 0)))) :=
      Logic.trans _ _ _ (addComm (liftTerm b) (.mul (liftTerm b) (.var 0)))
        (Support.equalitySymmetry _ _ (.arithmetic (.mulSucc (liftTerm b) (.var 0))))
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base hnext) (localTrans _ _ _ hc (.base hend))))
  have h := atTerm phi a (ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag b from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.MultiplyProof
