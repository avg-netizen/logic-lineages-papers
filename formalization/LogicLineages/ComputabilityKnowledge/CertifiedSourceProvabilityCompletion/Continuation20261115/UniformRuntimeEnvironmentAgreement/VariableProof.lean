module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.MachineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.VariableProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport FixedFormulaSubstitution
open UniformFixedFormulaAgreement.Traversal MachineProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Old runtime chunks are actually traversed using the closed-term framed
identity; inserted replacement is only emitted in the bound-coordinate case. -/
theorem traverses {arity ctx n depth inputs : Nat} (p : Program arity) (I : Installation p)
 (vtag scanTag len q : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (G : List (Formula ctx)) (e : Environment n (depth+1) inputs) (raw : List.Vector (Term ctx) inputs)
 (replacement : Term ctx)
 (hinputs : ∀ j : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag (raw.get j)))) (i : Fin n) (rest out : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I (termValue I.ctag I.atag e raw (.var i))
   (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 0 (Term.numeral (depth+1))) rest)) out replacement)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (termValue I.ctag I.atag (specialize e) (replacement ::ᵥ raw) (.var i)))))) := by
 cases he : e i with
 | inr j =>
  obtain ⟨hvj⟩ := hinputs j
  obtain ⟨hclosed⟩ := UniformClosedTermFrame.StatementChecks.exactFramedClosedIdentity arity p
   I.ftag I.etag vtag I.stag scanTag I.ptag I.ctag I.atag I.dtag len q I.ltag I.rtag
   I.hf I.he hv I.hs hscan I.hp I.hc I.ha I.hd hlen hq I.hl I.hr ctx
   (raw.get j) (Term.numeral (depth+1)) rest out replacement
  have hout := Hilbert.Local.mp (Hilbert.Local.base hclosed) hvj
  have hvalue := EnvironmentProof.runtimeValue I.ctag I.atag e raw replacement i j he
  rw [hvalue]
  simpa only [MachineProof.run,termValue,he,UniformClosedTermFrame.initial,UniformClosedTermFrame.final] using (show Nonempty _ from ⟨hout⟩)
 | inl j =>
  obtain ⟨hvar⟩ := UniformFixedFormulaAgreement.VariableProof.traverses p I depth j rest out replacement
  obtain ⟨hcode⟩ := UniformFixedFormulaAgreement.PrefixCodeProof.encoded p I.ctag I.hc
   (GorbowTermPrefixCode.encode (.var j)) (ctx := ctx)
  have hchange := UniformRawFoldInputFusion.LogicProof.inputCongruence I.ftag _ _
   (HistoryKernel.pairCall I.ptag
    (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag 0 (Term.numeral (depth+1))) rest)) out)
   replacement hcode
  have hresult := Logic.trans _ _ _ (Support.equalitySymmetry _ _ hchange) hvar
  have hvalue := EnvironmentProof.boundValue I.ctag I.atag e raw replacement i j he
  rw [hvalue]
  simpa only [MachineProof.run,termValue,he] using
   (show Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G _) from ⟨.base hresult⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.VariableProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.VariableProof
