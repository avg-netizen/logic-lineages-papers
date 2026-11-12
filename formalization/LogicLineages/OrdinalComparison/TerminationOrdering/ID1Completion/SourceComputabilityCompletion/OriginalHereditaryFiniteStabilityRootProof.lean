module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRootProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteStability OriginalRootObservation

theorem childValue (Q T : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s t : State (Fin n) arity) (h : StepAgreement Q T c s) (hc : Child s t) :
 typedValue Q c t.term = typedValue T c t.term := by
 exact congrArg (Nat.pair (typeNumber t.term.1)) (h t (Step.child hc))

theorem argumentsValue (Q T : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s : State (Fin n) arity) {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types)
 (h : StepAgreement Q T c s)
 (hc : ∀ q ∈ argumentList args, Child s ⟨Gamma,q⟩) :
 argumentValues Q c args = argumentValues T c args := by
 apply List.map_congr_left
 intro q hq
 exact childValue Q T c s ⟨Gamma,q⟩ h (hc q hq)

theorem nativeDependency (Q T : Program 2) (n : Nat) (arity : Fin n → Nat) (c : Nat)
 (s : State (Fin n) arity) (h : StepAgreement Q T c s) :
 nativeValue Q c s.term = nativeValue T c s.term := by
 rcases s with ⟨Gamma,tau,q⟩
 cases q with
 | var v => rfl
 | bottom t => rfl
 | @lam Gamma d t q =>
   have he := childValue Q T c ⟨Gamma,⟨.arrow d t,.lam q⟩⟩ ⟨d::Gamma,⟨t,q⟩⟩ h (Child.lam q)
   simp only [nativeValue,he]
 | @app Gamma d t q a =>
   have hf := childValue Q T c ⟨Gamma,⟨_,.app q a⟩⟩ ⟨Gamma,⟨_,q⟩⟩ h (Child.appFunction q a)
   have ha := childValue Q T c ⟨Gamma,⟨_,.app q a⟩⟩ ⟨Gamma,⟨_,a⟩⟩ h (Child.appArgument q a)
   simp only [nativeValue,hf,ha]
 | ordinary f args =>
   have he := argumentsValue Q T c ⟨Gamma,⟨_,.ordinary f args⟩⟩ args h (fun q hq => Child.ordinary f args q hq)
   simp only [nativeValue,he]
 | numbered k f tau args types extras =>
   have hb := argumentsValue Q T c ⟨Gamma,⟨tau,.numbered k f tau args types extras⟩⟩ args h
     (fun q hq => Child.numberedBase k f tau args types extras q hq)
   have he := argumentsValue Q T c ⟨Gamma,⟨tau,.numbered k f tau args types extras⟩⟩ extras h
     (fun q hq => Child.numberedExtra k f tau args types extras q hq)
   simp only [nativeValue,hb,he]

theorem rootDependency (Q T : Program 2) (n : Nat) (arity : Fin n → Nat) (c : Nat)
 (s : State (Fin n) arity) (h : StepAgreement Q T c s) :
 value (rootObservation Q) c s = value (rootObservation T) c s := by
 exact (OriginalRootObservationNativeProof.nativeCalibration Q n arity s.context c s.term).trans
   ((nativeDependency Q T n arity c s h).trans
     (OriginalRootObservationNativeProof.nativeCalibration T n arity s.context c s.term).symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityRootProof
