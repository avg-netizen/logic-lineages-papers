module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralCallProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralNodeSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowFormulaSubstitution

variable {alpha : Type} [Primcodable alpha]

namespace FormulaEffective

theorem universalClosure : ∀ n {phi : alpha → Formula n}, FormulaEffective phi →
    FormulaEffective (fun x => GorbowStandardInduction.universalClosure (phi x)) := by
  intro n
  induction n with
  | zero => intro phi hp; exact hp
  | succ n ih => intro phi hp; exact ih hp.all

end FormulaEffective

namespace TermEffective

theorem numeralArguments {arity : Nat} {inputs : alpha → List.Vector Nat arity}
    (hi : Primrec inputs) : ∀ i,
    TermEffective (fun x => (GorbowPRNumeralCalculation.numeralArguments (inputs x)).get i) := by
  intro i
  have hget : Primrec (fun x => (inputs x).get i) :=
    Primrec.vector_get.comp hi (Primrec.const i)
  simpa only [GorbowPRNumeralCalculation.numeralArguments, List.Vector.get_map] using
    (TermEffective.numeral (n := 0) hget)

end TermEffective

namespace FormulaEffective

theorem calculation {arity : Nat} (q : Program arity) {tag : alpha → Nat}
    (htag : Primrec tag) {inputs : alpha → List.Vector Nat arity} (hi : Primrec inputs) :
    FormulaEffective (fun x => EffectiveNumeral.calculation (tag x) q (inputs x)) := by
  have heval : Primrec (fun x => evaluate q (inputs x)) :=
    (GorbowPRProgram.Proof.primitiveEvaluation arity q).comp hi
  exact FormulaEffective.equal
    (TermEffective.call htag (fun x => GorbowPRNumeralCalculation.numeralArguments (inputs x))
      (TermEffective.numeralArguments hi))
    (TermEffective.numeral heval)

end FormulaEffective

namespace HasCertificates

/-- An input-dependent instance of one ACTUAL node equation. The produced
certificate uses canonical source axiomLine, allInstantiate and numeric MP. -/
theorem nodeEquationInstance {m arity : Nat} (q : Program m) {tag : alpha → Nat}
    (lhs rhs : alpha → Term arity) (hl : TermEffective lhs) (hr : TermEffective rhs)
    (hnode : ∀ x, equation (lhs x) (rhs x) ∈ nodeEquations q (tag x))
    {sigma : alpha → Fin arity → Term 0}
    (hs : ∀ i, TermEffective (fun x => sigma x i)) :
    HasCertificates (fun x => NodeSupport.check q (tag x)) (fun x =>
      Formula.equal (GorbowSubstitution.substitute (sigma x) (lhs x))
        (GorbowSubstitution.substitute (sigma x) (rhs x))) := by
  let E := fun x => Formula.equal (lhs x) (rhs x)
  have hE : FormulaEffective E := FormulaEffective.equal hl hr
  have hC := FormulaEffective.universalClosure arity hE
  have ha : ∀ x, NodeSupport.check q (tag x)
      (GorbowFormulaPrefixCode.encode (equation (lhs x) (rhs x))) = true := by
    intro x
    apply decide_eq_true
    exact List.mem_map.mpr ⟨_, NodeSupport.rootIncluded q (tag x) _ (hnode x), rfl⟩
  have hc := axiomFamily (fun x => NodeSupport.check q (tag x)) hC ha
  have hi := universalSpecialization (fun x => NodeSupport.check q (tag x)) arity hE hs hc
  exact hi

/-- Checkers for any two finite equation lists are monotone under literal
source inclusion, independently of standard interpretations. -/
theorem finiteCheckInclusion (left right : List Sentence)
    (hsub : ∀ sigma ∈ left, sigma ∈ right) (raw : List Nat)
    (h : decide (raw ∈ left.map GorbowFormulaPrefixCode.encode) = true) :
    decide (raw ∈ right.map GorbowFormulaPrefixCode.encode) = true := by
  simp only [decide_eq_true_eq] at h ⊢
  obtain ⟨sigma,hs,he⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨sigma,hsub sigma hs,he⟩

end HasCertificates
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
