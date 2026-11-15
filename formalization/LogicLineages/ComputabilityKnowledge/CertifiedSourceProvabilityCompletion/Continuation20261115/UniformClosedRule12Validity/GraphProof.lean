module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.ArgumentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
noncomputable def binaryCongruence {T : Sentence → Prop} {ctx : Nat} (tag : Nat) (a b c d : Term ctx)
 (ha : Derivation T (.equal a c)) (hb : Derivation T (.equal b d)) :
 Derivation T (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (call tag (c ::ᵥ d ::ᵥ nil))) := by
 apply Logic.callCongruence T tag (a ::ᵥ b ::ᵥ nil) (c ::ᵥ d ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact ha
 | succ i => cases i using Fin.cases with
   | zero => exact hb
   | succ i => exact Fin.elim0 i
/-- Original guards, actual decoded triple, and both installed instance graphs. -/
theorem exactConclusionGraph : Targets.InternalConclusionGraph := by
 intro n p I ctx f t u
 let T := GorbowPRNumeralCalculation.Theory p
 let L := UniformClosedInstanceRecognizer.guards I.fval I.vtag f t
 let R := UniformClosedInstanceRecognizer.guards I.fval I.vtag f u
 let V := Continuation20261114.RawReflexivityDispatcher.valid I.vtag u
 let A := UniformClosedRule12.guards I.fval I.vtag f t u
 let G := [A]
 let args := UniformClosedRule12.argumentsValue I.ctag f t u
 let leftResult := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f t
 let rightResult := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag f u
 have ha : Hilbert.Local T ctx G (.conj L V) := .hypothesis List.mem_cons_self
 have hL := Hilbert.Local.mp (.base (.logical (.andLeft L V))) ha
 have hV := Hilbert.Local.mp (.base (.logical (.andRight L V))) ha
 have hF := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hL
 have hR : Hilbert.Local T ctx G R :=
  Hilbert.Local.mp (Hilbert.Local.mp (.base (.logical (.andIntro _ _))) hF) hV
 obtain ⟨hfirst⟩ := ArgumentsProof.first p I f t u
 obtain ⟨hsecond⟩ := ArgumentsProof.second p I f t u
 obtain ⟨hthird⟩ := ArgumentsProof.third p I f t u
 obtain ⟨hlen⟩ := ArgumentsProof.lengthThree p I f t u
 obtain ⟨hleftGraph⟩ := UniformClosedInstanceRecognizer.StatementChecks.exactGuardedGraph n p
  I.itag I.ftag I.fval I.vtag I.ptag I.ctag I.rtag I.h_itag I.h_ftag I.h_fval I.h_vtag I.h_ptag I.h_ctag I.h_rtag ctx f t
 obtain ⟨hrightGraph⟩ := UniformClosedInstanceRecognizer.StatementChecks.exactGuardedGraph n p
  I.itag I.ftag I.fval I.vtag I.ptag I.ctag I.rtag I.h_itag I.h_ftag I.h_fval I.h_vtag I.h_ptag I.h_ctag I.h_rtag ctx f u
 have hleftPos := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := G) hleftGraph)
 have hrightPos := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := G) hrightGraph)
 have hleft := Hilbert.Local.mp hleftPos hL
 have hright := Hilbert.Local.mp hrightPos hR
 have hleftArgs := binaryCongruence I.itag _ _ f t hfirst hsecond
 have hrightArgs := binaryCongruence I.itag _ _ f u hfirst hthird
 have hleftCall : Hilbert.Local T ctx G
  (.equal (UniformClosedCase12.leftValue I.itag I.htag I.ttag args) (.succ leftResult)) :=
  localTrans _ _ _ (.base hleftArgs) hleft
 have hrightCall : Hilbert.Local T ctx G
  (.equal (UniformClosedCase12.rightValue I.itag I.htag I.ttag args) (.succ rightResult)) :=
  localTrans _ _ _ (.base hrightArgs) hright
 obtain ⟨hcase⟩ := UniformClosedCase12.BranchProof.accepted p G I.itag I.len I.htag I.ttag I.ctag I.atag
  I.h_itag I.h_len I.h_htag I.h_ttag I.h_ctag I.h_atag args leftResult rightResult
  (.base hlen) hleftCall hrightCall I.caseTag I.h_caseTag
 let expanded := UniformClosedCase12.formulaValue I.ctag I.atag
  (UniformClosedCase12.secondValue I.htag I.ttag args) (UniformClosedCase12.thirdValue I.htag I.ttag args)
  leftResult rightResult
 have hpredArgs := callCongruence I.predTag
  (UniformClosedCase12.caseCall I.caseTag args ::ᵥ nil) ((.succ expanded) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcase
   | succ i => exact Fin.elim0 i)
 obtain ⟨hpred⟩ := predecessor p G expanded I.predTag I.h_predTag
 have hcompiled := localTrans _ _ _ hpredArgs hpred
 have hterms := binaryCongruence I.atag _ _ t u hsecond hthird
 have hequality := binaryCongruence I.ctag (Term.numeral 0) _ (Term.numeral 0) _
  (.logical (.reflexive _)) hterms
 let consequent := FixedFormulaSubstitution.binaryValue I.ctag I.atag 7 leftResult rightResult
 have happ := binaryCongruence I.atag _ consequent _ consequent hequality (.logical (.reflexive _))
 have hshape := binaryCongruence I.ctag (Term.numeral 7) _ (Term.numeral 7) _
  (.logical (.reflexive _)) happ
 have hout := localTrans _ _ _ hcompiled (.base hshape)
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.GraphProof
