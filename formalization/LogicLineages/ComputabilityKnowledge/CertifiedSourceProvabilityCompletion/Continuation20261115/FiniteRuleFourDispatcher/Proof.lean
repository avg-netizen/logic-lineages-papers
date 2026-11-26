module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.DispatcherProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Extract the actual branch copy first, then obtain common fuel there. The
supplied xtag is never identified with this independently recovered tag. -/
theorem finiteLiteralDispatcher : Targets.FiniteLiteralDispatcher := by
 intro pF pR q c hA logical arithmetic x xtag dtag hn hx hd
 obtain ⟨branchTag,hbranch⟩ := InstallationProof.actualLeaf
  (FiniteRuleFourLeaf.sourceRoot pF pR q) dtag logical arithmetic x hd
 obtain ⟨fuel,hfuel⟩ := FiniteRuleFourLeaf.StatementChecks.exactFiniteLiteralLeaf
  pF pR q c hA x branchTag hn hbranch
 refine ⟨fuel,?_⟩
 intro sigma hsigma ctx larger history
 obtain ⟨hseed⟩ := (hfuel sigma hsigma).2.2 ctx larger
 have hlocal := DispatcherProof.fromLeaf (FiniteRuleFourLeaf.sourceRoot pF pR q)
  dtag branchTag logical arithmetic x hd hbranch sigma
  (Term.numeral (Encodable.encode c)) larger history
 obtain ⟨hsource⟩ := GorbowTheoryProofProof.monotonicity _ (S pF pR q)
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hlocal
 exact ⟨Hilbert.compose hsource hseed⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Proof
