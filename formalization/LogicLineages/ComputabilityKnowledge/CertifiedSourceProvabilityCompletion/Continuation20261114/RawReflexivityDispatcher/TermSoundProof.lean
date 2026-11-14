module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.TermSoundProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof List.Vector SixSol20261113
open TwoSol20261113.ReflexivityRecognizer SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

def tasks {ctx : Nat} (ptag ctag : Nat) : Term ctx :=
 HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag .zero) .zero

theorem binding {n ctx : Nat} (p : Program n) (vtag stag ptag ctag etag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (he : (nodes p)[etag]? = some ⟨2,equalCode⟩) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall vtag raw) (HistoryKernel.pairCall etag
   (LiteralSyntaxScan.scanCall stag (tasks ptag ctag) raw) (.succ .zero)))) := by
 let args := raw ::ᵥ nil
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let ts := tasks (ctx := ctx) ptag ctag
 let result := LiteralSyntaxScan.scanCall stag ts raw
 have hz := constantValue p [] args 0
 have ht : Computes p [] (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0)) args task :=
  binary p [] args HistoryCodec.pair _ _ .zero .zero task hz hz (copies p [] _ ptag hp _)
 have hts : Computes p [] termTasks args ts :=
  binary p [] args HistoryCodec.cons _ _ task .zero ts ht hz (copies p [] _ ctag hc _)
 have hsc : Computes p [] termScan args result :=
  binary p [] args LiteralSyntaxScan.scanCode _ _ ts raw result
   hts (projection p [] args 0) (copies p [] LiteralSyntaxScan.scanCode stag hs _)
 obtain ⟨hout⟩ := binary p [] args equalCode termScan (constant 1 1) result (.succ .zero)
  (HistoryKernel.pairCall etag result (.succ .zero)) hsc (constantValue p [] args 1)
  (copies p [] equalCode etag he _) vtag hv
 exact ⟨Hilbert.Local.finish hout⟩

theorem sound {n ctx : Nat} (p : Program n) (vtag stag ptag ctag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (valid vtag raw)
   (.equal (LiteralSyntaxScan.scanCall stag (tasks ptag ctag) raw) (.succ .zero)))) := by
 let g : Fin 2 → Program 1 := Fin.cases termScan (Fin.cases (constant 1 1) Fin.elim0)
 have he := Equations.functionChild p vtag equalCode g hv
 obtain ⟨hb⟩ := binding p vtag stag ptag ctag (vtag+1) hv hs hp hc he raw
 obtain ⟨heq⟩ := HistoryKernel.EqualProof.internalEqualSound n p (vtag+1) he ctx
  (LiteralSyntaxScan.scanCall stag (tasks ptag ctag) raw) (.succ .zero)
 let H := valid vtag raw
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.base heq) (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hb)) hh)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.TermSoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.TermSoundProof
