module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StepProof

@[expose] public section
/-! Actual full-language PA induction on an internally bound arbitrary fuel
increment. No numeral schema, external bound or semantic completeness rule
supplies the universal conclusion. All original runtime parameters remain. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open GorbowFormulaSubstitution GorbowSubstitution
open NamedArithmeticGraph

private theorem substSuccess {m n : Nat} (sub : Fin m → Term n) (tag : Nat)
    (index fuel context formula cert : Term m) :
    substituteFormula sub (success tag index fuel context formula cert) =
      success tag (substitute sub index) (substitute sub fuel) (substitute sub context)
        (substitute sub formula) (substitute sub cert) := by
  simp only [success,inputs,substituteFormula,Logic.substCall,List.Vector.map_cons,
    List.Vector.map_nil,Logic.substNumeral]

private theorem baseInstance {ctx : Nat} (tag : Nat)
    (index fuel context formula cert : Term ctx) :
    GorbowStandardInstances.instantiate (incrementTemplate tag index fuel context formula cert) .zero =
      .imp (success tag index fuel context formula cert)
        (success tag index (.add fuel .zero) context formula cert) := by
  simp only [GorbowStandardInstances.instantiate,incrementTemplate,substituteFormula,substSuccess,
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

private theorem successorInstance {ctx : Nat} (tag : Nat)
    (index fuel context formula cert : Term ctx) :
    GorbowStandardInduction.successorInstance (incrementTemplate tag index fuel context formula cert) =
      .imp (success tag (liftTerm index) (liftTerm fuel) (liftTerm context) (liftTerm formula) (liftTerm cert))
        (success tag (liftTerm index) (.add (liftTerm fuel) (.succ (.var 0)))
          (liftTerm context) (liftTerm formula) (liftTerm cert)) := by
  simp only [GorbowStandardInduction.successorInstance,incrementTemplate,substituteFormula,
    substSuccess,successorLift,substitute,Fin.cases_zero]

theorem openIncrement : Targets.OpenIncrement := by
  intro n p tag q0 htag ctx index fuel context formula cert
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := incrementTemplate tag index fuel context formula cert
  have hz : Derivation T (.equal fuel (.add fuel .zero)) :=
    Support.equalitySymmetry _ _ (.arithmetic (.addZero fuel))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = incrementTemplate tag index fuel context formula cert from rfl,baseInstance]
    exact Logic.fuelTransport tag index context formula cert fuel (.add fuel .zero) hz
  obtain ⟨hnext⟩ := StepProof.openStep n p tag q0 htag (ctx+1)
    (liftTerm index) (.add (liftTerm fuel) (.var 0))
    (liftTerm context) (liftTerm formula) (liftTerm cert)
  have he : Derivation T (.equal (.succ (.add (liftTerm fuel) (.var 0)))
      (.add (liftTerm fuel) (.succ (.var 0)))) :=
    Support.equalitySymmetry _ _ (.arithmetic (.addSucc (liftTerm fuel) (.var 0)))
  have htransport := Logic.fuelTransport tag (liftTerm index) (liftTerm context)
    (liftTerm formula) (liftTerm cert) (.succ (.add (liftTerm fuel) (.var 0)))
    (.add (liftTerm fuel) (.succ (.var 0))) he
  have hq := Hilbert.compose htransport hnext
  let P := success tag (liftTerm index) (liftTerm fuel)
    (liftTerm context) (liftTerm formula) (liftTerm cert)
  let Q := success tag (liftTerm index) (.add (liftTerm fuel) (.var 0))
    (liftTerm context) (liftTerm formula) (liftTerm cert)
  let R := success tag (liftTerm index) (.add (liftTerm fuel) (.succ (.var 0)))
    (liftTerm context) (liftTerm formula) (liftTerm cert)
  have hp : Hilbert.Local T (ctx+1) [P,Formula.imp P Q] P := .hypothesis List.mem_cons_self
  have hi : Hilbert.Local T (ctx+1) [P,Formula.imp P Q] (.imp P Q) :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr : Hilbert.Local T (ctx+1) [P,Formula.imp P Q] R :=
    .mp (.base hq) (.mp hi hp)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    rw [show phi = incrementTemplate tag index fuel context formula cert from rfl,successorInstance]
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hr))
  exact ⟨.mp (.mp (.arithmetic (.induction phi)) hb) (.generalize hs)⟩

private theorem weakenImp {ctx : Nat} (tag : Nat)
    (index s t context formula cert : Term ctx) :
    GorbowPACore.weaken (.imp (success tag index s context formula cert)
      (success tag index t context formula cert)) =
      .imp (success tag (liftTerm index) (liftTerm s) (liftTerm context) (liftTerm formula) (liftTerm cert))
        (success tag (liftTerm index) (liftTerm t) (liftTerm context) (liftTerm formula) (liftTerm cert)) := by
  simp only [GorbowPACore.weaken,substituteFormula,substSuccess]
  rfl

theorem openMonotonicity : Targets.OpenMonotonicity := by
  intro n p tag q0 htag ctx index s t context formula cert
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := incrementTemplate tag index s context formula cert
  obtain ⟨hinc⟩ := openIncrement n p tag q0 htag ctx index s context formula cert
  obtain ⟨hbody⟩ := Logic.openAll T phi ⟨hinc⟩
  let E : Formula (ctx+1) := .equal (.add (liftTerm s) (.var 0)) (liftTerm t)
  let P := success tag index s context formula cert
  let R := success tag index t context formula cert
  let PL := success tag (liftTerm index) (liftTerm s) (liftTerm context) (liftTerm formula) (liftTerm cert)
  let RL := success tag (liftTerm index) (liftTerm t) (liftTerm context) (liftTerm formula) (liftTerm cert)
  have heq : Derivation T (.imp E (.imp
      (success tag (liftTerm index) (.add (liftTerm s) (.var 0))
        (liftTerm context) (liftTerm formula) (liftTerm cert)) RL)) :=
    Logic.fuelEqualityRule T tag (liftTerm index) (liftTerm context) (liftTerm formula)
      (liftTerm cert) (.add (liftTerm s) (.var 0)) (liftTerm t)
  have hp : Hilbert.Local T (ctx+1) [PL,E] PL := .hypothesis List.mem_cons_self
  have he : Hilbert.Local T (ctx+1) [PL,E] E :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr : Hilbert.Local T (ctx+1) [PL,E] RL :=
    .mp (.mp (.base heq) he) (.mp (.base hbody) hp)
  have hstep : Derivation T (.imp E (GorbowPACore.weaken (.imp P R))) := by
    rw [show P = success tag index s context formula cert from rfl,
      show R = success tag index t context formula cert from rfl,weakenImp]
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hr))
  exact HBQuantifier.existentialElimination T E (.imp P R) ⟨hstep⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.InductionProof
