module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

def taskList {ctx : Nat} (ptag ctag : Nat) (context : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag (.succ .zero) context) .zero

theorem nodesInstalled {n : Nat} (p : Program n) (vtag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨2,formulaValidator⟩) :
 ∃ (stag ptag ctag etag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ ∧
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ ∧
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ ∧
 (nodes p)[etag]? = some ⟨2,equalCode⟩ := by
 let args : Fin 2 → Program 2 := Fin.cases formulaScan (Fin.cases (constant 2 1) Fin.elim0)
 have he := Equations.functionChild p vtag equalCode args hv
 have hsw := Equations.argumentChild p vtag equalCode args hv 0
 let sw := vtag + argumentTag equalCode args 0
 let sargs : Fin 2 → Program 2 := Fin.cases formulaTasks (Fin.cases (.projection 1) Fin.elim0)
 have hs := Equations.functionChild p sw LiteralSyntaxScan.scanCode sargs hsw
 have hcw := Equations.argumentChild p sw LiteralSyntaxScan.scanCode sargs hsw 0
 let cw := sw + argumentTag LiteralSyntaxScan.scanCode sargs 0
 let cargs : Fin 2 → Program 2 := Fin.cases formulaTask (Fin.cases (constant 2 0) Fin.elim0)
 have hc := Equations.functionChild p cw HistoryCodec.cons cargs hcw
 have hpw := Equations.argumentChild p cw HistoryCodec.cons cargs hcw 0
 let pw := cw + argumentTag HistoryCodec.cons cargs 0
 let pargs : Fin 2 → Program 2 := Fin.cases (constant 2 1) (Fin.cases (.projection 0) Fin.elim0)
 have hp := Equations.functionChild p pw HistoryCodec.pair pargs hpw
 exact ⟨sw+1,pw+1,cw+1,vtag+1,hs,hp,hc,he⟩

theorem binding {n ctx : Nat} (p : Program n) (vtag stag ptag ctag etag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨2,formulaValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (he : (nodes p)[etag]? = some ⟨2,equalCode⟩)
 (context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaCall vtag context raw)
   (HistoryKernel.pairCall etag (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero)))) := by
 let args := context ::ᵥ raw ::ᵥ nil
 let task := HistoryKernel.pairCall ptag (.succ .zero) context
 let tasks := taskList ptag ctag context
 let result := LiteralSyntaxScan.scanCall stag tasks raw
 have htask : Computes p [] formulaTask args task :=
  binary p [] args HistoryCodec.pair (constant 2 1) (.projection 0) (.succ .zero) context task
   (constantValue p [] args 1) (projection p [] args 0) (copies p [] HistoryCodec.pair ptag hp _)
 have htasks : Computes p [] formulaTasks args tasks :=
  binary p [] args HistoryCodec.cons formulaTask (constant 2 0) task .zero tasks
   htask (constantValue p [] args 0) (copies p [] HistoryCodec.cons ctag hc _)
 have hscan : Computes p [] formulaScan args result :=
  binary p [] args LiteralSyntaxScan.scanCode formulaTasks (.projection 1) tasks raw result
   htasks (projection p [] args 1) (copies p [] LiteralSyntaxScan.scanCode stag hs _)
 have h : Computes p [] formulaValidator args (HistoryKernel.pairCall etag result (.succ .zero)) :=
  binary p [] args equalCode formulaScan (constant 2 1) result (.succ .zero) _
   hscan (constantValue p [] args 1) (copies p [] equalCode etag he _)
 obtain ⟨hout⟩ := h vtag hv
 exact ⟨Hilbert.Local.finish hout⟩

theorem sound {n ctx : Nat} (p : Program n) (vtag stag ptag ctag etag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨2,formulaValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (he : (nodes p)[etag]? = some ⟨2,equalCode⟩)
 (context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (formulaCall vtag context raw) (.succ .zero))
   (.equal (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (formulaCall vtag context raw) (.succ .zero)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hb⟩ := binding p vtag stag ptag ctag etag hv hs hp hc he context raw
 obtain ⟨heq⟩ := HistoryKernel.EqualProof.internalEqualSound n p etag he ctx
  (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.base heq) (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hb)) hh)))⟩

theorem complete {n ctx : Nat} (p : Program n) (vtag stag ptag ctag etag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨2,formulaValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (he : (nodes p)[etag]? = some ⟨2,equalCode⟩)
 (context raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero))
   (.equal (formulaCall vtag context raw) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hb⟩ := binding p vtag stag ptag ctag etag hv hs hp hc he context raw
 obtain ⟨heq⟩ := HistoryKernel.EqualProof.internalEqualComplete n p etag he ctx
  (LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw) (.succ .zero)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hb) (.mp (.base heq) hh)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
