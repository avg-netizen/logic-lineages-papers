module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open SixSol20261113 SixSol20261112.Fuel
/-- Concrete original step witnesses: no decoded-list premise and no assumed
expansion success. All three facts are obtained from the actual successful step. -/
def witnessBody {ctx : Nat} (etag ctag atag : Nat)
 (tasks tok result head tail added : Term ctx) : Formula ctx :=
 .conj (.equal tasks (HistoryLookup.consCall ctag head tail))
  (.conj (.equal (LiteralSyntaxStep.expandCall etag head tok) (.succ added))
   (.equal result (HistoryAppend.appendCall atag added tail)))
/-- Quantifier order is head, tail, added. In the innermost body these are
original de Bruijn indices2,1,0; each external parameter is lifted three times. -/
def witnesses {ctx : Nat} (etag ctag atag : Nat) (tasks tok result : Term ctx) : Formula ctx :=
 .ex (.ex (.ex (witnessBody etag ctag atag
  (liftTerm (liftTerm (liftTerm tasks))) (liftTerm (liftTerm (liftTerm tok)))
  (liftTerm (liftTerm (liftTerm result))) (.var 2) (.var 1) (.var 0))))
/-- Successful original step decomposition for ALL raw runtime stack codes.
Empty/malformed-success branches must be ruled out internally. -/
def InternalStepSuccessDecomposition : Prop := ∀ n (p : Program n) (stag etag ctag atag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (tasks tok result : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) tok) (.succ result))
   (witnesses etag ctag atag tasks tok result)))
/-- Recover an ORIGINAL difference node already inside the installed expansion
at the SAME registry p, rather than assume a new program/extension is installed. -/
def OriginalDifferenceInstalled : Prop := ∀ n (p : Program n) (etag : Nat),
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 ∃ dtag : Nat, (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessTargets
