module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- Every numeric argument code. Actual original nested-list codec/default and
Option(List Nat) output codec, not a canonical triple or successful syntax image. -/
def ExactOriginalCase12 : Prop := ∀ code : Nat,
 evaluate caseCode (code ::ᵥ nil) =
 Encodable.encode (GorbowLogicalAxiomCode.case12 0 (decodedArguments code))
/-- Actual internal graph for arbitrary runtime argument/result terms.
Length and two Option conditions are object-language hypotheses only. The
membership-only interface exposes no successful instance or native-image premise. -/
def InternalCaseGraph : Prop := ∀ n (p : Program n)
 (qtag itag ltag htag ttag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,caseCode⟩ →
 (nodes p)[itag]? = some ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩ →
 (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩ →
 (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (args left right : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.imp (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3))
    (.imp (.equal (leftValue itag htag ttag args) (.succ left))
     (.imp (.equal (rightValue itag htag ttag args) (.succ right))
      (.equal (caseCall qtag args) (.succ (formulaValue ctag atag
       (secondValue htag ttag args) (thirdValue htag ttag args) left right))))))
   (.conj
    (.imp (.neg (.equal (HistoryLengthOffset.lengthCall ltag args) (Term.numeral 3)))
     (.equal (caseCall qtag args) .zero))
    (.conj
     (.imp (.equal (leftValue itag htag ttag args) .zero) (.equal (caseCall qtag args) .zero))
     (.imp (.equal (rightValue itag htag ttag args) .zero) (.equal (caseCall qtag args) .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.Targets
