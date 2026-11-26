module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.FusionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations
open GorbowFormulaSubstitution GorbowSubstitution GorbowPRChildTags List.Vector
open SixSol20261112.HistoryMachine SixSol20261112.Fuel NamedArithmeticGraph

private theorem substIteration {m n : Nat} (sub : Fin m → Term n) tag
    (count state index fuel : Term m) :
    substitute sub (iterationCall tag count state index fuel) =
      iterationCall tag (substitute sub count) (substitute sub state)
        (substitute sub index) (substitute sub fuel) := by
  simp only [iterationCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

private theorem baseInstance {ctx : Nat} tag (s state index fuel : Term ctx) :
    GorbowStandardInstances.instantiate (fusionTemplate tag s state index fuel) .zero =
      .equal (iterationCall tag (.add s .zero) state index fuel)
        (iterationCall tag .zero (iterationCall tag s state index fuel) index fuel) := by
  simp only [GorbowStandardInstances.instantiate,fusionTemplate,substituteFormula,substIteration,
    liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]

private theorem successorLift {ctx : Nat} (t : Term ctx) :
    substitute (Fin.cases (.succ (.var 0)) (fun i : Fin ctx => Term.var i.succ)) (liftTerm t) =
      liftTerm t := by
  unfold liftTerm renameTerm
  rw [substitute_composition]
  have he : (fun i : Fin ctx => substitute
      (Fin.cases (.succ (.var 0)) (fun j : Fin ctx => Term.var j.succ)) (Term.var i.succ)) =
      (fun i : Fin ctx => Term.var i.succ) := by
    funext i
    rfl
  rw [he]

private theorem successorInstance {ctx : Nat} tag (s state index fuel : Term ctx) :
    GorbowStandardInduction.successorInstance (fusionTemplate tag s state index fuel) =
      .equal (iterationCall tag (.add (liftTerm s) (.succ (.var 0)))
        (liftTerm state) (liftTerm index) (liftTerm fuel))
      (iterationCall tag (.succ (.var 0))
        (iterationCall tag (liftTerm s) (liftTerm state) (liftTerm index) (liftTerm fuel))
        (liftTerm index) (liftTerm fuel)) := by
  simp only [GorbowStandardInduction.successorInstance,fusionTemplate,substituteFormula,
    substIteration,successorLift,substitute,Fin.cases_zero]

private def localTrans {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    (s t u : Term ctx) (hst : Hilbert.Local T ctx gamma (.equal s t))
    (htu : Hilbert.Local T ctx gamma (.equal t u)) : Hilbert.Local T ctx gamma (.equal s u) := by
  have h := Derivation.logical (A := T)
    (.equalityReplace (.equal (renameTerm Fin.succ s) (.var 0)) t u)
  change Derivation T (.imp (.equal t u)
    (.imp (.equal (substitute (Fin.cases t Term.var) (renameTerm Fin.succ s)) t)
      (.equal (substitute (Fin.cases u Term.var) (renameTerm Fin.succ s)) u))) at h
  rw [Support.shiftCancel,Support.shiftCancel] at h
  exact .mp (.mp (.base h) htu) hst

private def localUnary {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    (f : Term (ctx+1)) (s t : Term ctx) (h : Hilbert.Local T ctx gamma (.equal s t)) :
    Hilbert.Local T ctx gamma (.equal (substitute (Fin.cases s Term.var) f)
      (substitute (Fin.cases t Term.var) f)) := by
  let fs := substitute (Fin.cases s Term.var) f
  let phi := Formula.equal (renameTerm Fin.succ fs) f
  have hi : Derivation T (GorbowStandardInstances.instantiate phi s) := by
    change Derivation T (.equal (substitute (Fin.cases s Term.var) (renameTerm Fin.succ fs)) fs)
    rw [Support.shiftCancel]
    exact .logical (.reflexive fs)
  have hr : Hilbert.Local T ctx gamma (GorbowStandardInstances.instantiate phi t) :=
    .mp (.mp (.base (.logical (.equalityReplace phi s t))) h) (.base hi)
  change Hilbert.Local T ctx gamma (.equal
    (substitute (Fin.cases t Term.var) (renameTerm Fin.succ fs))
    (substitute (Fin.cases t Term.var) f)) at hr
  rw [Support.shiftCancel] at hr
  exact hr

private def countCongruence {T : Sentence → Prop} {ctx : Nat} tag
    (a b state index fuel : Term ctx) (h : Derivation T (.equal a b)) :
    Derivation T (.equal (iterationCall tag a state index fuel)
      (iterationCall tag b state index fuel)) := by
  have d := Logic.unary (iterationCall tag (.var 0) (liftTerm state)
    (liftTerm index) (liftTerm fuel)) a b h
  simpa only [substIteration,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

private def kernelCongruence {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    tag (a b index fuel : Term ctx) (h : Hilbert.Local T ctx gamma (.equal a b)) :
    Hilbert.Local T ctx gamma (.equal (call tag (a ::ᵥ index ::ᵥ fuel ::ᵥ nil))
      (call tag (b ::ᵥ index ::ᵥ fuel ::ᵥ nil))) := by
  have d := localUnary (call tag (.var 0 ::ᵥ liftTerm index ::ᵥ liftTerm fuel ::ᵥ nil)) a b h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,
    Support.shiftCancel,substitute,Fin.cases_zero] using d

theorem openFusion : SixSol20261112.HistoryMachine.Targets.OpenFusion := by
  intro n p tag kernel ht ctx s state index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := fusionTemplate tag s state index fuel
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = fusionTemplate tag s state index fuel from rfl,baseInstance]
    obtain ⟨hz⟩ := Equations.zero p tag kernel ht (iterationCall tag s state index fuel) index fuel
    have hleft := countCongruence tag (.add s .zero) s state index fuel
      (Derivation.arithmetic (A := T) (.addZero s))
    exact Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hz)
  let a := iterationCall tag (.add (liftTerm s) (.var 0))
    (liftTerm state) (liftTerm index) (liftTerm fuel)
  let b := iterationCall tag (.var 0)
    (iterationCall tag (liftTerm s) (liftTerm state) (liftTerm index) (liftTerm fuel))
    (liftTerm index) (liftTerm fuel)
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal a b) := .hypothesis List.mem_cons_self
  have hk := kernelCongruence (tag + stepTag iterationBase + 1) a b
    (liftTerm index) (liftTerm fuel) ih
  have ha := countCongruence tag (.add (liftTerm s) (.succ (.var 0)))
    (.succ (.add (liftTerm s) (.var 0))) (liftTerm state) (liftTerm index) (liftTerm fuel)
    (Derivation.arithmetic (A := T) (.addSucc (liftTerm s) (.var 0)))
  obtain ⟨hl⟩ := Equations.successor p tag kernel ht (.add (liftTerm s) (.var 0))
    (liftTerm state) (liftTerm index) (liftTerm fuel)
  obtain ⟨hr⟩ := Equations.successor p tag kernel ht (.var 0)
    (iterationCall tag (liftTerm s) (liftTerm state) (liftTerm index) (liftTerm fuel))
    (liftTerm index) (liftTerm fuel)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    rw [show phi = fusionTemplate tag s state index fuel from rfl,successorInstance]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (Logic.trans _ _ _ ha hl))
        (localTrans _ _ _ hk (.base (Support.equalitySymmetry _ _ hr)))))
  exact ⟨.mp (.mp (.arithmetic (.induction phi)) hb) (.generalize hs)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.FusionProof
