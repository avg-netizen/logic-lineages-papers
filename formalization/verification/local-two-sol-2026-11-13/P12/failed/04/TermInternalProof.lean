module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.TermInternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem scanInstalled {n : Nat} (p : Program n) (vtag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩) :
 ∃ stag, (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ := by
 let g : Fin 2 → Program 1 := Fin.cases termScan (Fin.cases (constant 1 1) Fin.elim0)
 have hscan := Equations.argumentChild p vtag equalCode g hv 0
 let sw := vtag + argumentTag equalCode g 0
 let sg : Fin 2 → Program 1 := Fin.cases termTasks (Fin.cases (.projection 0) Fin.elim0)
 exact ⟨sw+1,Equations.functionChild p sw LiteralSyntaxScan.scanCode sg hscan⟩

theorem binding {n ctx : Nat} (p : Program n) (vtag stag ptag ctag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (raw : Term ctx)
 (hscan : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag
   (LiteralNumeralPrefix.termTask ptag .zero) .zero) raw) (.succ .zero)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall vtag raw) (.succ .zero))) := by
 let args := raw ::ᵥ nil
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let tasks := HistoryLookup.consCall ctag task .zero
 have hz := constantValue p [] args 0
 have ht : Computes p [] (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0)) args task :=
  binary p [] args HistoryCodec.pair _ _ .zero .zero task hz hz (copies p [] _ ptag hp _)
 have hts : Computes p [] termTasks args tasks :=
  binary p [] args HistoryCodec.cons _ _ task .zero tasks ht hz (copies p [] _ ctag hc _)
 have hscan' : Computes p [] LiteralSyntaxScan.scanCode (tasks ::ᵥ raw ::ᵥ nil) (.succ .zero) := by
  intro tag htag
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag stag 2
   LiteralSyntaxScan.scanCode htag hs ctx (tasks ::ᵥ raw ::ᵥ nil)
  obtain ⟨h⟩ := hscan
  exact ⟨.base (Logic.trans _ _ _ hcopy h)⟩
 have hsc : Computes p [] termScan args (.succ .zero) :=
  binary p [] args LiteralSyntaxScan.scanCode _ _ tasks raw (.succ .zero)
   hts (projection p [] args 0) hscan'
 obtain ⟨hout⟩ := binary p [] args equalCode termScan (constant 1 1)
  (.succ .zero) (.succ .zero) (.succ .zero) hsc (constantValue p [] args 1)
  (equalDiagonal p [] (.succ .zero)) vtag hv
 exact ⟨Hilbert.Local.finish hout⟩

theorem internalTerm : Targets.InternalTerm := by
 intro k t n p ttag vtag ptag ctag atag ht hv hp hc ha ctx values
 obtain ⟨stag,hs⟩ := scanInstalled p vtag hv
 have hscan := LiteralTemplateQuote.ScanProof.internalScan k t n p ttag stag ptag ctag atag
  ht hs hp hc ha ctx values .zero .zero
 exact binding p vtag stag ptag ctag hv hs hp hc (LiteralTemplateQuote.quoteCall ttag values) hscan
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.TermInternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.TermInternalProof
