module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorTokenProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport LiteralRawMP.DispatcherSupportProof
open ConstructorValidityTargets ConstructorStepTargets
/-- Right-empty append only for the explicit finite task prefix needed here;
no unsupported right-identity assertion on arbitrary malformed raw stacks. -/
theorem prefixNil {n ctx : Nat} (p : Program n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (xs : List (Term ctx)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag xs) .zero)
   (FinitePrefixTargets.prefixTerm ctag xs))) := by
 induction xs with
 | nil => exact HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx .zero
 | cons x xs ih =>
  obtain ⟨hih⟩ := ih
  obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx x (FinitePrefixTargets.prefixTerm ctag xs) .zero
  have htail := callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := []) ctag
   (x ::ᵥ HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag xs) .zero ::ᵥ nil)
   (x ::ᵥ FinitePrefixTargets.prefixTerm ctag xs ::ᵥ nil) (fun i => by
    cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive x))
    | succ i => cases i using Fin.cases with
      | zero => exact .base hih
      | succ i => exact Fin.elim0 i)
  exact ⟨Logic.trans _ _ _ hcons htail.finish⟩
/-- Consume the actual constructor token, equating original scan to the actual
finite child-row scan. All installed step/expand nodes are recovered from scan. -/
theorem tokenScan {n ctx : Nat} (p : Program n) (stag ptag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (ctor : Constructor) (bound raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) bound))
    (HistoryLookup.consCall ctag (Term.numeral (token ctor)) raw))
   (LiteralSyntaxScan.scanCall stag (FinitePrefixTargets.prefixTerm ctag (tasks ptag bound ctor)) raw))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨stepTag,hstep⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := ClosedScanInstallationProof.expandNode p stepTag hstep
 let row := FinitePrefixTargets.prefixTerm ctag (tasks ptag bound ctor)
 let single := singleton ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) bound)
 obtain ⟨hrow⟩ := ConstructorStepProof.stepAt p stepTag etag ptag ctag atag hstep he hp hc ha ctor bound (.zero : Term ctx)
 obtain ⟨happend⟩ := prefixNil p ctag atag hc ha (tasks ptag bound ctor)
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := []) happend)
 have hsucc' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (.succ (HistoryAppend.appendCall atag row .zero)) (.succ row)) := by
  simpa only [row,GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 have hstepRow := localTrans _ _ _ (.base hrow) hsucc'
 obtain ⟨hcons⟩ := ScanStateTransportConsProof.consAt p [] itag len ptag r ctag stepTag hi hlen hp hc hstep
  (Term.numeral (token ctor)) raw single (.succ row) hstepRow
 obtain ⟨hleft⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr single
  (HistoryLookup.consCall ctag (Term.numeral (token ctor)) raw)
 obtain ⟨hright⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr row raw
 exact ⟨Logic.trans _ _ _ hleft (Logic.trans _ _ _ hcons.finish (Support.equalitySymmetry _ _ hright))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorTokenProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorTokenProof
