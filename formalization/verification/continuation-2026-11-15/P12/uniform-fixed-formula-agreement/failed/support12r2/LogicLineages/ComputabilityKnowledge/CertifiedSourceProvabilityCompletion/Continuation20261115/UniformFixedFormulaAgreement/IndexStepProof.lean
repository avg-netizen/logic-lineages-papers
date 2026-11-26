module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Every actual typed index is consumed by the original scanner; both bound
and replaced indices are covered. The strict gap is proved, not supplied. -/
theorem consumes {n ctx : Nat} (p : Program n) (stag xtag ptag ctag atag dtag ltag rtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (depth : Nat) (index : Fin (depth+1)) (rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxStep.stepCall stag
   (.succ (HistoryLookup.consCall ctag
    (LiteralSyntaxStep.taskCall ptag 2 (Term.numeral (depth+1))) rest))
   (Term.numeral index.val)) (.succ rest))) := by
 let task : Term ctx := LiteralSyntaxStep.taskCall ptag 2 (Term.numeral (depth+1))
 obtain ⟨hk⟩ := HistoryLookup.DestructorProof.decoderCrossPair p ltag ptag false hl hp
  (Term.numeral (n := ctx) 2) (Term.numeral (depth+1))
 obtain ⟨hb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp
  (Term.numeral (n := ctx) 2) (Term.numeral (depth+1))
 obtain ⟨gap,hgap⟩ := FullFormulaInstantiationValidity.BoundVariableArithmeticProof.positiveDifference
  (depth+1) index p dtag hd (ctx := ctx)
 obtain ⟨hg⟩ := hgap
 have hchange := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) dtag
  (Term.numeral index.val ::ᵥ call rtag (task ::ᵥ nil) ::ᵥ nil)
  (Term.numeral index.val ::ᵥ Term.numeral (depth+1) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 obtain ⟨hout⟩ := RelationalSyntaxDepthTransport.StepTransportIndexProof.indexStep
  p [] stag xtag ctag atag dtag ltag rtag hs hx hc ha hd hl hr task rest
  (Term.numeral index.val) (Term.numeral gap) (.base hk) (.base (Logic.trans _ _ _ hchange hg))
 exact ⟨hout.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexStepProof
