module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph
theorem substFrame {m n : Nat} (s : Fin m → Term n) ptag atag ltag rtag (prefixCode state : Term m) :
 substitute s (frameTerm ptag atag ltag rtag prefixCode state) =
 frameTerm ptag atag ltag rtag (substitute s prefixCode) (substitute s state) := by
 simp only [frameTerm,HistoryKernel.pairCall,HistoryAppend.appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem outputEquation {n ctx : Nat} (p : Program n) (ptag atag ltag rtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (prefixCode state out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (frameTerm ptag atag ltag rtag prefixCode (HistoryKernel.pairCall ptag state out))
   (HistoryKernel.pairCall ptag state (HistoryAppend.appendCall atag prefixCode out)))) := by
 obtain ⟨hlp⟩ := HistoryLookup.DestructorProof.decoderCrossPair p ltag ptag false hl hp state out
 obtain ⟨hrp⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp state out
 have happ := UniformClosedRule13Validity.GraphProof.binaryCongruence atag prefixCode _ prefixCode out
  (.logical (.reflexive prefixCode)) hrp
 exact ⟨UniformClosedRule13Validity.GraphProof.binaryCongruence ptag _ _ state _ hlp happ⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.AtomsProof
