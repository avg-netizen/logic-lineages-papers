module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.VariableProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.TermProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport FixedFormulaSubstitution
open UniformFixedFormulaAgreement.Traversal MachineProof
open RelationalSyntaxDepthTransport.ConstructorStepTargets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual runtime environment traversal for every original term constructor.
Runtime input chunks retain their own validator guards; replacement is arbitrary. -/
theorem traverses {arity ctx n depth inputs : Nat} (p : Program arity) (I : Installation p)
 (vtag scanTag len q : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (G : List (Formula ctx)) (e : Environment n (depth+1) inputs) (raw : List.Vector (Term ctx) inputs)
 (replacement : Term ctx)
 (hinputs : ∀ j : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag (raw.get j)))) (t : Term n) :
 ∀ rest out : Term ctx, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I (termValue I.ctag I.atag e raw t)
   (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 0 (Term.numeral (depth+1))) rest)) out replacement)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) t))))) := by
 induction t with
 | var i =>
  intro rest out
  exact VariableProof.traverses p I vtag scanTag len q hv hscan hlen hq G e raw replacement hinputs i rest out
 | zero =>
  intro rest out
  obtain ⟨hz⟩ := UniformFixedFormulaAgreement.TermProof.traverses p I depth (.zero : Term (depth+1)) replacement rest out
  obtain ⟨hcode⟩ := UniformFixedFormulaAgreement.PrefixCodeProof.encoded p I.ctag I.hc [1] (ctx := ctx)
  have hchange := UniformRawFoldInputFusion.LogicProof.inputCongruence I.ftag _ _
   (HistoryKernel.pairCall I.ptag
    (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 0 (Term.numeral (depth+1))) rest)) out)
   replacement hcode
  have hresult := Logic.trans _ _ _ (Support.equalitySymmetry _ _ hchange) hz
  exact ⟨.base hresult⟩
 | succ t ih =>
  intro rest out
  exact ChildrenProof.unary p I G (.term 2) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw t)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) t)
   replacement rfl ih rest out
 | add t u ht hu =>
  intro rest out
  exact ChildrenProof.binary p I G (.term 3) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw t) (termValue I.ctag I.atag e raw u)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) t)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) u)
   replacement rfl ht hu rest out
 | mul t u ht hu =>
  intro rest out
  exact ChildrenProof.binary p I G (.term 4) (by intro h; cases h) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw t) (termValue I.ctag I.atag e raw u)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) t)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) u)
   replacement rfl ht hu rest out
 | universalFunction t ih =>
  intro rest out
  exact ChildrenProof.unary p I G (.term 5) (by intro h; cases h)
   (Term.numeral (depth+1)) (Term.numeral (depth+1)) 0
   (termValue I.ctag I.atag e raw t)
   (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) t)
   replacement rfl ih rest out
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.TermProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.TermProof
