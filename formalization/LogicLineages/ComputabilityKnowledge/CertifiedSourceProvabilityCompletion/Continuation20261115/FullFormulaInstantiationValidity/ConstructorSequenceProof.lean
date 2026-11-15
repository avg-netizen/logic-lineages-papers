module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorSequenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ConstructorValidityTargets RelationalSyntaxDepthTransport
/-- Finite explicit child rows, never an arbitrary raw-stack image assertion.
Fusion and framing are paid using the ORIGINAL scan laws for each child. -/
theorem sequence {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (stag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (tasks children : List (Term ctx))
 (hchildren : List.Forall₂ (fun task raw => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) raw) (.succ .zero)))) tasks children) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (FinitePrefixTargets.prefixTerm ctag tasks) (rawSequence atag children)) (.succ .zero))) := by
 induction hchildren with
 | nil =>
  obtain ⟨h⟩ := LiteralSyntaxScan.EmptyProof.internalEmpty n p stag hs ctx .zero
  exact ⟨.base h⟩
 | @cons task raw tasks children hchild hchildren ih =>
  obtain ⟨hv⟩ := hchild
  cases hchildren with
  | nil => exact ⟨hv⟩
  | @cons next nextRaw rest remaining hnext hrest =>
   obtain ⟨htail⟩ := ih
   let tail := FinitePrefixTargets.prefixTerm ctag (next :: rest)
   obtain ⟨hfirst⟩ := ConstructorFrameProof.frameOne p G stag ctag atag hs hc ha task raw tail hv
   obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionProof.internalFusion n p stag atag hs ha ctx
    (HistoryLookup.consCall ctag task tail) raw (rawSequence atag (nextRaw :: remaining)) tail
   have hrow := Hilbert.Local.mp (.base hfuse) hfirst
   exact ⟨localTrans _ _ _ hrow htail⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorSequenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorSequenceProof
