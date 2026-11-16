module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.StepCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorCoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open PrescribedRuntimeCallCongruence

theorem assemble {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (f : Program m) (tag : Nat) (G : List (Formula ctx)) (counter : Term ctx)
 (inputs : List.Vector (Term ctx) m) (previous result childCode index fuel : Term ctx) :
 let J := tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag previous
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag)
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ av)
 let left := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ av)
 let right := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let P := equalValue J.ctag J.atag priorCall priorNum
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula f tag) (counterRaw ::ᵥ av)
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag nextCall left) seed)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag right output) childCode)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue J.ctag J.atag P (equalValue J.ctag J.atag nextCall output))
   (certificate I f tag counter inputs previous result childCode))) := by
 dsimp only
 intro hroot hchild
 let J := tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag previous
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag)
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ av)
 let left := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ av)
 let right := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let P := equalValue J.ctag J.atag priorCall priorNum
 let V := RawReflexivityDispatcher.valid (ctx := ctx) I.previous.current.vtag
 have hav : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (V (av.get i))) := by
  intro i
  simpa only [av,CurrentCompositionCertificate.numeralValues,List.Vector.get_map] using
   (PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
    I.previous.previous.previous.previous.previous.hnumeral G (inputs.get i))
 have hn (value : Term ctx) := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
  I.previous.previous.previous.previous.previous.hnumeral G value
 obtain ⟨hcounter⟩ := hn counter
 obtain ⟨hprevious⟩ := hn previous
 obtain ⟨hnextCounter⟩ := hn (.succ counter)
 obtain ⟨houtput⟩ := hn result
 have hcons {n : Nat} (v : Term ctx) (vs : List.Vector (Term ctx) n)
  (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (V v))
  (hvs : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (V (vs.get i)))) :
  ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (V ((v ::ᵥ vs).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hv⟩
  | succ i => exact hvs i
 obtain ⟨hprior⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral tag) (counterRaw ::ᵥ av) (hcons counterRaw av hcounter hav)
 obtain ⟨hnext⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral tag) _ (hcons _ av hnextCounter hav)
 obtain ⟨hleft⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral (tag+GorbowPRChildTags.stepTag f)) _ (hcons counterRaw _ hcounter (hcons priorCall av hprior hav))
 obtain ⟨hright⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral (tag+GorbowPRChildTags.stepTag f)) _ (hcons counterRaw _ hcounter (hcons priorNum av hprevious hav))
 obtain ⟨hP⟩ := CurrentEqualityImplication.GuardProof.equal p installed lhs rhs t old a x I G false priorCall priorNum hprior hprevious
 obtain ⟨hrootValid⟩ := CurrentEqualityImplication.GuardProof.equal p installed lhs rhs t old a x I G false nextCall left hnext hleft
 obtain ⟨hchildValid⟩ := CurrentEqualityImplication.GuardProof.equal p installed lhs rhs t old a x I G false right output hright houtput
 obtain ⟨hcong⟩ := StepCongruenceProof.internal p installed lhs rhs t old a x I
  (tag+GorbowPRChildTags.stepTag f) G counterRaw priorCall priorNum index fuel av hcounter hprior hprevious hav
 obtain ⟨hliftRoot⟩ := CurrentEqualityImplication.RulesProof.lift p installed lhs rhs t old a x I G
  (equalValue J.ctag J.atag nextCall left) P _ index fuel ⟨hrootValid⟩ ⟨hP⟩ hroot
 have hliftRootCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hliftRoot
 obtain ⟨hfirst⟩ := CurrentEqualityImplication.TransitivityInternalProof.internal p installed lhs rhs t old a x I G
  P nextCall left right _ _ index fuel ⟨hP⟩ ⟨hnext⟩ ⟨hleft⟩ ⟨hright⟩ ⟨hliftRootCore⟩ ⟨hcong⟩
 have hfirstCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hfirst
 obtain ⟨hliftChild⟩ := CurrentEqualityImplication.RulesProof.lift p installed lhs rhs t old a x I G
  (equalValue J.ctag J.atag right output) P childCode index fuel ⟨hchildValid⟩ ⟨hP⟩ hchild
 have hliftChildCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hliftChild
 exact CurrentEqualityImplication.TransitivityInternalProof.internal p installed lhs rhs t old a x I G
  P nextCall right output _ _ index fuel ⟨hP⟩ ⟨hnext⟩ ⟨hright⟩ ⟨houtput⟩ ⟨hfirstCore⟩ ⟨hliftChildCore⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorCoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorCoreProof
