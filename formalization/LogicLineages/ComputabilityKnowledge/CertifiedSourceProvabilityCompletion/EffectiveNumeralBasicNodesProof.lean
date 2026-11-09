module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralEquationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.BasicNodes
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowSubstitution
open Family

private def numSub {n : Nat} (v : List.Vector Nat n) (i : Fin n) : Term 0 :=
  Term.numeral (v.get i)

private theorem subCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem subArguments {n : Nat} (v : List.Vector Nat n) :
    (argumentVariables n).map (substitute (numSub v)) =
      GorbowPRNumeralCalculation.numeralArguments v := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables, numSub, GorbowPRNumeralCalculation.numeralArguments, substitute]

private theorem numSubEffective (arity : Nat) : ∀ i,
    TermEffective (fun z : Nat × List.Vector Nat arity => numSub z.2 i) := by
  intro i
  exact TermEffective.numeral (Primrec.vector_get.comp Primrec.snd (Primrec.const i))

/-- One producer works at EVERY runtime registry tag for the zero node. -/
theorem zero : HasCertificates
    (fun z : Nat × List.Vector Nat 0 => NodeSupport.check Program.zero z.1)
    (fun z => calculation z.1 Program.zero z.2) := by
  have he := FormulaEffective.calculation Program.zero (alpha := Nat × List.Vector Nat 0)
    Primrec.fst Primrec.snd
  apply HasCertificates.axiomFamily _ he
  intro z
  apply decide_eq_true
  apply List.mem_map.mpr
  refine ⟨_, NodeSupport.rootIncluded Program.zero z.1 _ ?_, rfl⟩
  have hv : z.2 = List.Vector.nil := by
    apply List.Vector.ext
    intro i
    exact Fin.elim0 i
  rw [hv]
  simp only [calculation, nodeEquations, equation, GorbowStandardInduction.universalClosure,
    GorbowPRNumeralCalculation.numeralArguments, List.Vector.map_nil, evaluate, Term.numeral,
    List.mem_singleton]

theorem successor : HasCertificates
    (fun z : Nat × List.Vector Nat 1 => NodeSupport.check Program.succ z.1)
    (fun z => calculation z.1 Program.succ z.2) := by
  let lhs := fun z : Nat × List.Vector Nat 1 => call z.1 (argumentVariables 1)
  let rhs := fun _ : Nat × List.Vector Nat 1 => (Term.succ (.var 0) : Term 1)
  have hl : TermEffective lhs := TermEffective.call Primrec.fst
    (fun _ => argumentVariables 1) (fun i => TermEffective.constant ((argumentVariables 1).get i))
  have hr : TermEffective rhs := TermEffective.constant _
  have he := HasCertificates.nodeEquationInstance Program.succ lhs rhs hl hr
    (by intro z; exact List.mem_singleton.mpr rfl) (numSubEffective 1)
  simpa only [lhs, rhs, subCall, subArguments, substitute, numSub, evaluate,
    List.Vector.get_zero, Term.numeral, calculation] using he

theorem projection {arity : Nat} (i : Fin arity) : HasCertificates
    (fun z : Nat × List.Vector Nat arity => NodeSupport.check (Program.projection i) z.1)
    (fun z => calculation z.1 (Program.projection i) z.2) := by
  let lhs := fun z : Nat × List.Vector Nat arity => call z.1 (argumentVariables arity)
  let rhs := fun _ : Nat × List.Vector Nat arity => (Term.var i : Term arity)
  have hl : TermEffective lhs := TermEffective.call Primrec.fst
    (fun _ => argumentVariables arity) (fun j => TermEffective.constant ((argumentVariables arity).get j))
  have hr : TermEffective rhs := TermEffective.constant _
  have he := HasCertificates.nodeEquationInstance (Program.projection i) lhs rhs hl hr
    (by intro z; exact List.mem_singleton.mpr rfl) (numSubEffective arity)
  simpa only [lhs, rhs, subCall, subArguments, substitute, numSub, evaluate, calculation] using he

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.BasicNodes
