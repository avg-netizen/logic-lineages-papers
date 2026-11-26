module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- All annotation argument lists, including wrong length and malformed raw
formulas/replacements. Literal original Option(List Nat) encoding. -/
def ExactOriginalCase13 : Prop := ∀ (args : List (List Nat)),
 evaluate caseCode (Encodable.encode args ::ᵥ nil) =
 Encodable.encode (GorbowLogicalAxiomCode.case13 0 args)
/-- Actual internal length/Option branch laws on arbitrary encoded arguments.
No canonical-pair, source image or successful-instance premise is external;
all branch hypotheses remain inside the derived object-language graph. -/
def InternalCaseGraph : Prop := ∀ n (p : Program n)
 (qtag itag ltag htag ttag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,caseCode⟩ →
 (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩ →
 (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (args result : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.imp (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2))
    (.imp (.equal (instanceValue itag htag ttag args) (.succ result))
     (.equal (caseCall qtag args) (.succ (formulaValue ctag atag (firstValue htag args) result)))))
   (.conj
    (.imp (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 2)))
     (.equal (caseCall qtag args) .zero))
    (.imp (.equal (instanceValue itag htag ttag args) .zero)
     (.equal (caseCall qtag args) .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.Targets
