module

public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction

@[expose] public section
/-! A temporary closed assumption used only in existing ordinary Hilbert
proof trees. No theorem-only knowledge/truth rule is introduced or used
under assumptions. Derived classical proof operations will support actual
negative numeral certificates, not semantic nonderivability substitutes. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation
open GorbowSyntax

def contradictionBranch (A : Sentence → Prop) (p : Sentence) : Sentence → Prop :=
  GorbowClosedDeduction.extend A (.neg p)

end LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation
