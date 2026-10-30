module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramSemantics

@[expose] public section

/-! Literal finite-name transport of the already checked source envelope.
No existential/choice extraction is used to construct the finite expression. -/
namespace LogicLineages.ComputabilityKnowledge.WWFiniteEnvelope

open PositiveExpression CircuitReduction

def narrow (d : Nat) : (e : Expr Nat) → Bounded d e → Expr (Fin d)
  | .one, _ => .one
  | .var i, h => .var ⟨i, h⟩
  | .add a b, h => .add (narrow d a h.1) (narrow d b h.2)
  | .emul a b, h => .emul (narrow d a h.1) (narrow d b h.2)

def envelope (d : Nat) (e : Expr (Fin d)) : Expr (Fin d) :=
  narrow d (FiniteDepthEnvelope.envelope (e.rename Fin.val))
    ((FiniteDepthEnvelopeProof.sameVariables d _).mpr
      (ExponentialNormalizerProgramSemantics.finite_rename_bounded d e))

end LogicLineages.ComputabilityKnowledge.WWFiniteEnvelope
