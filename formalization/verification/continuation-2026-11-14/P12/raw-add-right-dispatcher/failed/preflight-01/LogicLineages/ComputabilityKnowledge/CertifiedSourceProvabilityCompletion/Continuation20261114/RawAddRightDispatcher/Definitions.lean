module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightAcceptance.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightDispatcher
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Literal original dispatcher with actual bounded-search logical refinement;
arithmetic and axiom programs remain arbitrary and unchanged. -/
abbrev dispatcher (old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator (RawAddRightReplace.logicalLeaf old) arithmetic x
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) extends
 toAcceptance : RawAddRightAcceptance.Installation p old where
 ftag : Nat
 ltag : Nat
 dtag : Nat
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher old arithmetic x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightDispatcher
