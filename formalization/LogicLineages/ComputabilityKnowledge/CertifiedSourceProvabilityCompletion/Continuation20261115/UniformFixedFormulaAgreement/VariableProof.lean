module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableEmitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport Traversal
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- Complete original two-token variable traversal, including suppressed marker,
actual index success, exact capture-correct value and accumulator normalization. -/
theorem traverses {n ctx : Nat} (p : Program n) (I : Installation p)
 (depth : Nat) (index : Fin (depth+1)) (rest out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (GorbowTermPrefixCode.encode (.var index))
   (input I.ptag I.ctag (.term 0) (Term.numeral (depth+1)) rest) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out
     (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth)
      (raw ::ᵥ nil) (.var index)))))) := by
 let bound : Term ctx := Term.numeral (depth+1)
 let idx : Term ctx := Term.numeral index.val
 let task := LiteralSyntaxStep.taskCall I.ptag 2 bound
 let state := .succ (HistoryLookup.consCall I.ctag task rest)
 let pending := HistoryLookup.consCall I.ctag idx .zero
 let out0 := HistoryAppend.appendCall I.atag out .zero
 let value := FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth) (raw ::ᵥ nil) (.var index)
 obtain ⟨hmarker⟩ := MarkerProof.consume p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.xtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hx bound rest pending out raw
 obtain ⟨hrows⟩ := StackProof.appendPrefix p I.ctag I.atag I.hc I.ha [task] rest
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := []) hrows)
 have hsucc' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (.succ (output I.ptag I.ctag I.atag (.term 0) bound rest)) state) := by
  simpa only [RelationalSyntaxDepthTransport.ConstructorStepTargets.output,RelationalSyntaxDepthTransport.ConstructorStepTargets.tasks,StackProof.prepend,GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 have hpacked := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag _ out0 state out0 hsucc'
  (.base (.logical (.reflexive _)))
 have hchange := FoldProof.stateCongruence I.ftag pending _ _ raw hpacked.finish
 obtain ⟨hrec⟩ := (UniformClosedSubstitutionRawFold.StatementChecks.exactRawRecursion
  n p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.hf I.hp I.hc I.hs I.he I.ha
  ctx idx .zero state out0 raw).2
 let nextState := HistoryKernel.pairCall I.ptag (LiteralSyntaxStep.stepCall I.stag state idx)
  (HistoryAppend.appendCall I.atag out0 (UniformClosedSubstitutionEmit.emitCall I.etag state idx raw))
 obtain ⟨hr0,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p I.ftag I.hf
 obtain ⟨hnil⟩ := UniformClosedSubstitutionRawFold.Proof.nilFold p I.ftag I.ptag _ _ _
  I.hf I.hp hi hlen hr0 nextState raw
 obtain ⟨hstep⟩ := IndexStepProof.consumes p I.stag I.xtag I.ptag I.ctag I.atag I.dtag I.ltag I.rtag
  I.hs I.hx I.hp I.hc I.ha I.hd I.hl I.hr depth index rest
 obtain ⟨hemit⟩ := VariableEmitProof.exactValue p I depth index rest raw
 have heq := OutputProof.rightCongruence I.atag out0 _ value hemit
 obtain ⟨hout⟩ := OutputProof.zeroThen p I.atag I.ctag I.ltag I.rtag I.ha I.hc I.hl I.hr out value
 have hfinal := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag _ _ (.succ rest)
  (HistoryAppend.appendCall I.atag out value) (.base hstep) (.base (Logic.trans _ _ _ heq hout))
 exact ⟨Logic.trans _ _ _ hmarker (Logic.trans _ _ _ hchange
  (Logic.trans _ _ _ hrec (Logic.trans _ _ _ hnil hfinal.finish)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableProof
