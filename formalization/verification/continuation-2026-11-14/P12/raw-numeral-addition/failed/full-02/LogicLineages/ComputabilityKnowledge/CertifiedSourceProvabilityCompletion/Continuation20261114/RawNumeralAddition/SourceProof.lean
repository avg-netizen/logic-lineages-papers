module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.AdditionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowSubstitution GorbowFormulaSubstitution
open RawAdditionSource GorbowPublishedDCB

theorem oneUniformSource : Targets.OneUniformSource := by
 obtain ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,xtag,I,hI,hold,holdA,hbase,hret,hpackages,hsingle,hcomp⟩ := RawAdditionSource.StatementChecks.exactSource
 refine ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,xtag,I,hI,hold,holdA,hbase,hret,hpackages,hsingle,hcomp,?_⟩
 intro ctx m k index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _
  (AdditionProof.internalAddition 4 (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I ctx m k index fuel)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.SourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.SourceProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.SourceProof.oneUniformSource
