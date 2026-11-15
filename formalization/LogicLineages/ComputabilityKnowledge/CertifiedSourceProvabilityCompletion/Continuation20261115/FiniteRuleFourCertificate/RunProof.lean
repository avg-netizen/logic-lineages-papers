module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.RunProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRunSplice HistoryKernel.TransitionEquationsProof
def kernelTag (itag : Nat) : Nat := itag + stepTag iterationBase + 1
def dispatchTag (itag : Nat) (logical arithmetic : Program 1) (x : Program 3) : Nat :=
 dispatcherTag (kernelTag itag) LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)
theorem dispatchInstalled {n : Nat} (p : Program n) (logical arithmetic : Program 1) (x : Program 3)
 (I : Installation p logical arithmetic x) :
 (nodes p)[dispatchTag I.itag logical arithmetic x]? = some ⟨4,HistoryDispatcher.lineDispatcher
  LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)⟩ := by
 have hk := IdleProof.kernelInstalled p I.itag LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) I.hi
 obtain ⟨_,_,_,hd,_⟩ := HistoryKernel.OptionProof.kernelNodes p (kernelTag I.itag)
  LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) hk
 exact hd
noncomputable def runCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (itag ptag : Nat) (index fuel a b : Term ctx) (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (LiteralCheckerAcceptance.runCall itag ptag index fuel a)
  (LiteralCheckerAcceptance.runCall itag ptag index fuel b)) := by
 have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) ptag
  (.succ .zero) a (.succ .zero) b (.base (.logical (.reflexive _))) h
 apply LiteralRawMP.DispatcherSupportProof.callCongruence itag
  (a ::ᵥ state ptag (.succ .zero) a ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  (b ::ᵥ state ptag (.succ .zero) b ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => cases i using Fin.cases with
   | zero => exact hs
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive index))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive fuel))
       | succ i => exact Fin.elim0 i
/-- Successful dispatcher is consumed and discharged, not assumed in the final
finite package. Iteration count is the actual encoded singleton certificate. -/
theorem fromDispatcher {n ctx : Nat} (p : Program n) (logical arithmetic : Program 1) (x : Program 3)
 (I : Installation p logical arithmetic x) (sigma : Sentence) (index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (HistoryDispatcher.dispatcherCall (dispatchTag I.itag logical arithmetic x)
   index fuel .zero (Term.numeral (FiniteRuleFourLeaf.lineCode sigma))) (.succ .zero))
  (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel (Term.numeral (certificateCode sigma)))
   (LiteralCheckerAuxiliaries.successfulState I.ptag I.ctag .zero (Term.numeral (rawCode sigma)) .zero .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let line : Term ctx := Term.numeral (FiniteRuleFourLeaf.lineCode sigma)
 let H := Formula.equal (HistoryDispatcher.dispatcherCall (dispatchTag I.itag logical arithmetic x) index fuel .zero line) (.succ .zero)
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let cert := HistoryLookup.consCall I.ctag line .zero
 let kt := kernelTag I.itag
 let count := call (I.ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0) (line ::ᵥ .zero ::ᵥ nil)
 have hk := IdleProof.kernelInstalled p I.itag LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) I.hi
 obtain ⟨hoption⟩ := HistoryKernel.OptionProof.optionAccepted p kt LiteralSyntaxValidator.lineValidator logical arithmetic
  (SaturatedAxiomLeaf.saturated x) hk index fuel .zero line
 have ho := Hilbert.Local.mp (.base hoption) hh
 obtain ⟨hentry⟩ := EntryProof.newHistory (ctx := ctx) p
  (someTag kt LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)) I.ptag I.ctag
  (someInstalled p kt LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) hk)
  I.hp I.hc sigma
 have hs := Logic.unary (.succ (.var 0)) _ _ hentry
 have hout := localTrans _ _ _ ho (.base hs)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p I.ctag I.hc ctx line .zero
 obtain ⟨hstep⟩ := ConsRunProof.someCons p I.itag I.ptag I.ctag LiteralSyntaxValidator.lineValidator logical arithmetic
  (SaturatedAxiomLeaf.saturated x) I.hi I.hp I.hc count .zero line .zero index fuel
 obtain ⟨hidle⟩ := IdleProof.internalIdle LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)
  n p I.itag I.ptag I.hi I.hp ctx count
  (optionValue kt LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) index fuel .zero line) index fuel
 have hcount := StationaryProof.iterationCount (T := T) (G := G) I.itag cert (.succ count)
  (state I.ptag (.succ .zero) cert) index fuel (.base hcons)
 have hpair := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ptag _ .zero _ .zero
  hout (.base (.logical (.reflexive .zero)))
 have hrun := localTrans _ _ _ hcount (localTrans _ _ _ (.base hstep) (localTrans _ _ _ (.base hidle) hpair))
 obtain ⟨hcoded⟩ := EncodingProof.certificate (ctx := ctx) p I.ctag I.hc sigma
 have hchange := runCongruence I.itag I.ptag index fuel (Term.numeral (certificateCode sigma)) cert
  (.base (Support.equalitySymmetry _ _ hcoded))
 exact ⟨(localTrans _ _ _ hchange hrun).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.RunProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.RunProof
