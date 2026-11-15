module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TraversalDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OneTokenProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open Traversal RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- A complete singleton-token fold, with original finite child tasks expanded
onto arbitrary rest and the copied token accumulated. -/
theorem constructor {n ctx : Nat} (p : Program n) (I : Installation p)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound rest out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I [token ctor] (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag
    (.succ (StackProof.prepend I.ctag (tasks I.ptag bound ctor) rest))
    (HistoryAppend.appendCall I.atag out
     (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor))))))) := by
 obtain ⟨hhead⟩ := ConstructorProof.consume p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.xtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hx ctor hmarker bound rest .zero out raw
 obtain ⟨hr0,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p I.ftag I.hf
 obtain ⟨hnil⟩ := UniformClosedSubstitutionRawFold.Proof.nilFold p I.ftag I.ptag _ _ _
  I.hf I.hp hi hlen hr0
  (HistoryKernel.pairCall I.ptag (.succ (output I.ptag I.ctag I.atag ctor bound rest))
   (HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor))))) raw
 obtain ⟨hrows⟩ := StackProof.appendPrefix p I.ctag I.atag I.hc I.ha (tasks I.ptag bound ctor) rest
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := []) hrows)
 have hsucc' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx []
  (.equal (.succ (output I.ptag I.ctag I.atag ctor bound rest))
   (.succ (StackProof.prepend I.ctag (tasks I.ptag bound ctor) rest))) := by
  simpa only [RelationalSyntaxDepthTransport.ConstructorStepTargets.output,GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 have hp := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag _ (HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))) _ (HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))) hsucc'
  (.base (.logical (.reflexive _)))
 exact ⟨Logic.trans _ _ _ hhead (Logic.trans _ _ _ hnil hp.finish)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OneTokenProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OneTokenProof
