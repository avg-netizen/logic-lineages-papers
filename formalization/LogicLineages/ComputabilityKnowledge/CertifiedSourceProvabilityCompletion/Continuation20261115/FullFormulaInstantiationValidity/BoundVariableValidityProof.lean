module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorValidityTargets
/-- Original kind2 scanner at the concrete index token, with its positive
runtime difference derived internally from the Fin index. -/
theorem indexScan (depth : Nat) (index : Fin depth) {n ctx : Nat} (p : Program n)
 (stag ptag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (singleton ctag (LiteralSyntaxStep.taskCall ptag 2 (Term.numeral (n := ctx) depth)))
   (HistoryLookup.consCall ctag (Term.numeral index.val) .zero)) (.succ .zero))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨dtag,hd⟩ := StepInstallationProof.originalDifferenceInstalled n p etag he
 obtain ⟨al,aq,l,ar,_,_,hl,_⟩ := InstallationProof.auxiliaryTags p stag atag hs ha
 let task := LiteralSyntaxStep.taskCall ptag 2 (Term.numeral (n := ctx) depth)
 let token := Term.numeral (n := ctx) index.val
 obtain ⟨hk⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral (n := ctx) 2) (Term.numeral depth)
 obtain ⟨hb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral (n := ctx) 2) (Term.numeral depth)
 obtain ⟨gap,hgap⟩ := BoundVariableArithmeticProof.positiveDifference depth index (ctx := ctx) p dtag hd
 obtain ⟨hg⟩ := hgap
 have hdarg := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) dtag
  (token ::ᵥ GorbowPRDefiningEquations.call r (task ::ᵥ nil) ::ᵥ nil)
  (token ::ᵥ Term.numeral depth ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive token)
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 have hdiff := Logic.trans _ _ _ hdarg hg
 obtain ⟨hindex⟩ := StepTransportIndexProof.indexStep p [] stepTag etag ctag atag dtag l r
  hstep he hc ha hd hl hr task .zero token (Term.numeral gap) (.base hk) (.base hdiff)
 obtain ⟨hcons⟩ := ScanStateTransportConsProof.consAt p [] itag len ptag r ctag stepTag hi hlen hp hc hstep
  token .zero (singleton ctag task) (.succ .zero) hindex
 obtain ⟨hnil⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ (.zero : Term ctx))
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr
  (singleton ctag task) (HistoryLookup.consCall ctag token .zero)
 exact ⟨Logic.trans _ _ _ hbind (Logic.trans _ _ _ hcons.finish hnil)⟩
/-- Exact encoded bound variable, matching the original in-scope variable case. -/
theorem boundVariableValidity : BoundVariableValidityTargets.InternalBoundVariableValidity := by
 intro depth index n p stag ptag ctag atag hs hp hc ha ctx
 let token := Term.numeral (n := ctx) index.val
 let rawIndex := HistoryLookup.consCall ctag token .zero
 obtain ⟨hindex⟩ := indexScan depth index (ctx := ctx) p stag ptag ctag atag hs hp hc ha
 have hchildren : List.Forall₂ (fun task raw => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) raw) (.succ .zero))))
  (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.term 0)) [rawIndex] :=
  .cons ⟨.base hindex⟩ .nil
 obtain ⟨hconstructor⟩ := ConstructorValidityProof.constructorValidity n p stag ptag ctag atag hs hp hc ha ctx []
  (.term 0) (Term.numeral depth) [rawIndex] hchildren
 obtain ⟨hi⟩ := BoundVariableArithmeticProof.numeralCons (ctx := ctx) p ctag hc index.val []
 obtain ⟨ho⟩ := BoundVariableArithmeticProof.numeralCons (ctx := ctx) p ctag hc 0 [index.val]
 have hraw1 := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) ctag
  (Term.numeral 0 ::ᵥ rawIndex ::ᵥ nil)
  (Term.numeral 0 ::ᵥ Term.numeral (Encodable.encode ([index.val] : List Nat)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hi
     | succ i => exact Fin.elim0 i)
 have hraw := Logic.trans _ _ _ hraw1 ho
 have hscan := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) stag
  (ClosedTermDepthTargets.tasks ptag ctag (Term.numeral depth) ::ᵥ HistoryLookup.consCall ctag (Term.numeral 0) rawIndex ::ᵥ nil)
  (ClosedTermDepthTargets.tasks ptag ctag (Term.numeral depth) ::ᵥ Term.numeral (Encodable.encode ([0,index.val] : List Nat)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hraw
     | succ i => exact Fin.elim0 i)
 exact ⟨Logic.trans _ _ _ (Support.equalitySymmetry _ _ hscan) hconstructor.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityProof
