module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.AtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryLookup.DestructorProof
theorem nilCase {n ctx : Nat} (p : Program n) (etag ntag otag ptag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (ho : (nodes p)[otag]? = some ⟨1,LiteralSyntaxScan.tick⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (eraseCall etag (newTickCall ntag (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag state out)) raw))
   (oldTickCall otag (eraseCall etag (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag state out)))))) := by
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.TickProof.tickNil p ptag hp (HistoryKernel.pairCall ptag state out) raw ntag hn
 obtain ⟨hold⟩ := LiteralSyntaxScan.TickProof.tickNil p ptag hp state otag ho
 obtain ⟨heq⟩ := AtomsProof.equation p etag ptag he hp .zero state out
 have hl := Logic.trans _ _ _ (unaryCallCongruence etag _ _ hnew.finish) heq
 have hr := Logic.trans _ _ _ (unaryCallCongruence otag _ _ heq) hold.finish
 exact ⟨Logic.trans _ _ _ hl (Support.equalitySymmetry _ _ hr)⟩
theorem consCase {n ctx : Nat} (p : Program n) (etag ntag otag ptag ctag stag emitTag atag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩)
 (ho : (nodes p)[otag]? = some ⟨1,LiteralSyntaxScan.tick⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hm : (nodes p)[emitTag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens state out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (eraseCall etag (newTickCall ntag
   (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out)) raw))
   (oldTickCall otag (eraseCall etag
    (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token tokens) (HistoryKernel.pairCall ptag state out)))))) := by
 obtain ⟨hnew⟩ := UniformClosedSubstitutionFold.TickProof.tickCons p ptag ctag stag emitTag atag hp hc hs hm ha token tokens state out raw ntag hn
 obtain ⟨hold⟩ := LiteralSyntaxScan.TickProof.tickCons p ptag ctag stag hp hc hs token tokens state otag ho
 obtain ⟨heq⟩ := AtomsProof.equation p etag ptag he hp (HistoryLookup.consCall ctag token tokens) state out
 obtain ⟨hnext⟩ := AtomsProof.equation p etag ptag he hp tokens (LiteralSyntaxStep.stepCall stag state token)
  (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall emitTag state token raw))
 have hl := Logic.trans _ _ _ (unaryCallCongruence etag _ _ hnew.finish) hnext
 have hr := Logic.trans _ _ _ (unaryCallCongruence otag _ _ heq) hold.finish
 exact ⟨Logic.trans _ _ _ hl (Support.equalitySymmetry _ _ hr)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.TickCasesProof
