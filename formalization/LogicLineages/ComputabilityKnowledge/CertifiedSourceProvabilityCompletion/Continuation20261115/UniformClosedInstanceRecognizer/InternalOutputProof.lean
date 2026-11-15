module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.InternalOutputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
/-- Original successor defining equation, not native evaluation. -/
theorem succComputes {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a : Term ctx) :
 Computes p G .succ (a ::ᵥ nil) (.succ a) := by
 intro tag ht
 obtain ⟨h⟩ := Support.intoRegistry p .succ tag ht _ (NamedArithmeticGraph.Equations.successor tag ctx (a ::ᵥ nil))
 exact ⟨.base h⟩
theorem output {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ftag ptag ctag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (formula replacement : Term ctx) :
 Computes p G outputCode (formula ::ᵥ replacement ::ᵥ nil) (outputValue ftag ptag ctag rtag formula replacement) := by
 let args := formula ::ᵥ replacement ::ᵥ nil
 let task := HistoryKernel.pairCall ptag (.succ .zero) (.succ .zero)
 let tasks := HistoryLookup.consCall ctag task .zero
 let state := HistoryKernel.pairCall ptag (.succ tasks) .zero
 have ht : Computes p G initialTask args task :=
  binary p G args HistoryCodec.pair _ _ _ _ _ (constantValue p G args 1) (constantValue p G args 1)
   (copies p G HistoryCodec.pair ptag hp _)
 have hts : Computes p G initialTasks args tasks :=
  binary p G args HistoryCodec.cons _ _ _ _ _ ht (constantValue p G args 0)
   (copies p G HistoryCodec.cons ctag hc _)
 have hstate : Computes p G initialState args state :=
  binary p G args HistoryCodec.pair _ _ _ _ _
   (unary p G args .succ initialTasks tasks (.succ tasks) hts (succComputes p G tasks))
   (constantValue p G args 0) (copies p G HistoryCodec.pair ptag hp _)
 have hfold : Computes p G rawFold args (UniformClosedSubstitutionRawFold.foldCall ftag formula state replacement) := by
  apply compose p G UniformClosedSubstitutionRawFold.foldCode _ args (formula ::ᵥ state ::ᵥ replacement ::ᵥ nil) _ _
   (copies p G UniformClosedSubstitutionRawFold.foldCode ftag hf _)
  intro i
  cases i using Fin.cases with
  | zero => exact projection p G args 0
  | succ i => cases i using Fin.cases with
    | zero => exact hstate
    | succ i => cases i using Fin.cases with
      | zero => exact projection p G args 1
      | succ i => exact Fin.elim0 i
 exact unary p G args (HistoryDecoder.decoder true) rawFold _ _ hfold
  (copies p G (HistoryDecoder.decoder true) rtag hr _)
theorem formulaValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (fval : Nat)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩) (formula replacement : Term ctx) :
 Computes p G formulaGuard (formula ::ᵥ replacement ::ᵥ nil)
  (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) :=
 binary p G _ LiteralSyntaxValidator.formulaValidator _ _ _ _ _
  (constantValue p G _ 1) (projection p G _ 0) (copies p G _ fval hf _)
theorem termValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (vtag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩) (formula replacement : Term ctx) :
 Computes p G termGuard (formula ::ᵥ replacement ::ᵥ nil)
  (TwoSol20261113.ReflexivityRecognizer.leafCall vtag replacement) :=
 unary p G _ TwoSol20261113.ReflexivityRecognizer.termValidator _ _ _
  (projection p G _ 1) (copies p G _ vtag hv _)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.InternalOutputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.InternalOutputProof
