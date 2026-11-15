module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.VariableProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport FullFormulaInstantiationValidity.ConstructorValidityTargets
theorem indexScan {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag ptag ctag atag dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (index depth positive : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag index depth) (.succ positive))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag (LiteralSyntaxStep.taskCall ptag 2 depth))
   (HistoryLookup.consCall ctag index .zero)) (.succ .zero))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨al,aq,l,ar,_,_,hl,_⟩ := InstallationProof.auxiliaryTags p stag atag hs ha
 let task := LiteralSyntaxStep.taskCall ptag 2 depth
 obtain ⟨hk⟩ := HistoryLookup.DestructorProof.decoderCrossPair p l ptag false hl hp (Term.numeral (n := ctx) 2) depth
 obtain ⟨hb⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp (Term.numeral (n := ctx) 2) depth
 have hdarg := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) dtag
  (index ::ᵥ GorbowPRDefiningEquations.call r (task ::ᵥ nil) ::ᵥ nil) (index ::ᵥ depth ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive index)
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 have hdiff := localTrans _ _ _ (.base hdarg) hg
 obtain ⟨hindex⟩ := StepTransportIndexProof.indexStep p G stepTag etag ctag atag dtag l r
  hstep he hc ha hd hl hr task .zero index positive (.base hk) hdiff
 obtain ⟨hcons⟩ := ScanStateTransportConsProof.consAt p G itag len ptag r ctag stepTag hi hlen hp hc hstep
  index .zero (singleton ctag task) (.succ .zero) hindex
 obtain ⟨hnil⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ (.zero : Term ctx))
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr
  (singleton ctag task) (HistoryLookup.consCall ctag index .zero)
 exact ⟨localTrans _ _ _ (.base hbind) (localTrans _ _ _ hcons (.base hnil))⟩
theorem exactVariable : Targets.InternalVariableChunk := by
 intro n p stag ptag ctag dtag hs hp hc hd ctx index depth positive
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨atag,ha⟩ := LiteralSyntaxValidator.QuantifierNodesProof.appendInstalled p stepTag hstep
 let H := Formula.equal (HistoryDifference.differenceCall dtag index depth) (.succ positive)
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hindex⟩ := indexScan p [H] stag ptag ctag atag dtag hs hp hc ha hd index depth positive hh
 let rawIndex := HistoryLookup.consCall ctag index .zero
 have hchildren : List.Forall₂ (fun task raw => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H]
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) raw) (.succ .zero))))
  (ConstructorStepTargets.tasks ptag depth (.term 0)) [rawIndex] := .cons ⟨hindex⟩ .nil
 obtain ⟨hconstructor⟩ := FullFormulaInstantiationValidity.ConstructorValidityProof.constructorValidity n p stag ptag ctag atag
  hs hp hc ha ctx [H] (.term 0) depth [rawIndex] hchildren
 exact ⟨hconstructor.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.VariableProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.VariableProof
