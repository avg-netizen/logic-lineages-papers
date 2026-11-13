module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
/-- Internal associativity of the actual literal append on arbitrary codes.
No native list image, associativity, or tail-decrease premise is supplied. -/
def InternalAppendAssociativity : Prop := ∀ n (p : Program n) atag ctag ltag rtag,
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (left middle right : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (HistoryAppend.appendCall atag left middle) right)
    (HistoryAppend.appendCall atag left (HistoryAppend.appendCall atag middle right))))

/-- Operational success-only frame law for the SAME literal step AST.
Tasks/out/suffix/token are arbitrary internal terms. No list-code image,
nonempty task row, expansion-success, Boolean, or native semantic premise is
supplied. The only operational premise is the actual successful step equality.
Nonemptiness and expansion success must be recovered internally. This is not
the full scan frame law and does not identify any earlier selected validity leaf. -/
def InternalStepFrame : Prop := ∀ n (p : Program n) stag atag ctag ltag rtag,
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (tasks out suffix token : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) (.succ out))
   (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryAppend.appendCall atag tasks suffix)) token)
     (.succ (HistoryAppend.appendCall atag out suffix)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.Targets
