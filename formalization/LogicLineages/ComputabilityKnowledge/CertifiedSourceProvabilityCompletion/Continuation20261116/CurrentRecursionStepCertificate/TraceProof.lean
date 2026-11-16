module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TemplateTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConditionalTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.GeneralTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowPublishedDCB PrescribedRuntimeCallCongruence GorbowPRDefiningEquations

theorem exactTrace : Targets.InternalTrace := by
 intro installed lhs rhs k t old a baseX pF pR I m f tag counter inputs previous result childCode ctx
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let J := tags I.previous
 have hc := I.previous.current.h_ctag
 have ha := I.previous.current.h_atag
 have hn := I.previous.previous.previous.previous.previous.hnumeral
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag (inputs.map (Term.numeral (n := ctx)))
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) counter)
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) previous)
 let nextRaw := LiteralNumeralPrefix.numeralCall J.numeralTag (.succ (Term.numeral (n := ctx) counter))
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) result)
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag) (nextRaw ::ᵥ av)
 let left := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ av)
 let right := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let aa := GorbowPRNumeralCalculation.numeralArguments inputs
 let prior := call tag (Term.numeral counter ::ᵥ aa)
 let next := call tag (Term.numeral (counter+1) ::ᵥ aa)
 let lhsCall := call (tag+GorbowPRChildTags.stepTag f) (Term.numeral counter ::ᵥ prior ::ᵥ aa)
 let rhsCall := call (tag+GorbowPRChildTags.stepTag f) (Term.numeral counter ::ᵥ Term.numeral previous ::ᵥ aa)
 have hav := CurrentCompositionCertificate.NativeValuesProof.numerals (ctx := ctx) p J hn inputs
 obtain ⟨hcounter⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn counter
 obtain ⟨hprevious⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn previous
 obtain ⟨hnextCounter⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn (counter+1)
 obtain ⟨houtput⟩ := ValueTraceProof.numeral (ctx := ctx) p J hn result
 have hcons {n : Nat} (v : Term ctx) (vs : List.Vector (Term ctx) n) (w : Term 0) (ws : List.Vector (Term 0) n)
  (hv : Derivation T (.equal v (rawNumeral w)))
  (hvs : ∀ i, Nonempty (Derivation T (.equal (vs.get i) (rawNumeral (ws.get i))))) :
  ∀ i, Nonempty (Derivation T (.equal ((v ::ᵥ vs).get i) (rawNumeral ((w ::ᵥ ws).get i)))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hv⟩
  | succ i => exact hvs i
 obtain ⟨hprior⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J hc ha hn tag _ _
  (hcons counterRaw av (Term.numeral counter) aa hcounter hav)
 obtain ⟨hnext⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J hc ha hn tag _ _
  (hcons nextRaw av (Term.numeral (counter+1)) aa hnextCounter hav)
 obtain ⟨hleft⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J hc ha hn (tag+GorbowPRChildTags.stepTag f) _ _
  (hcons counterRaw _ (Term.numeral counter) _ hcounter (hcons priorCall av prior aa hprior hav))
 obtain ⟨hright⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J hc ha hn (tag+GorbowPRChildTags.stepTag f) _ _
  (hcons counterRaw _ (Term.numeral counter) _ hcounter (hcons priorNum av (Term.numeral previous) aa hprevious hav))
 let sigma := Fin.cases (Term.numeral counter) (fun i => (Term.numeral (inputs.get i) : Term 0))
 have hseedInputs : ∀ i, Nonempty (Derivation T
  (.equal ((counterRaw ::ᵥ av).get i) ((PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hcounter⟩
  | succ i =>
   simpa only [sigma,PrescribedRuntimeSpecialization.numeralInputs,Fin.cases_succ,List.Vector.get_ofFn,
    List.Vector.get_cons_succ,GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map] using hav i
 obtain ⟨hseedEq⟩ := CurrentCompositionCertificate.SeedInputProof.certificateCongruence p J.mtag
  I.previous.previous.current.ctag I.previous.previous.current.atag I.previous.previous.current.constructorTag
  I.previous.previous.current.h_ctag I.previous.previous.current.h_atag (m+1) (rootFormula f tag)
  (counterRaw ::ᵥ av) (PrescribedRuntimeSpecialization.numeralInputs sigma)
  (Term.numeral (PrescribedSourceAxiomSpecialization.seed (rootFormula f tag))) hseedInputs
 obtain ⟨hseedNative⟩ := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 p (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  I.previous.previous.current J.mtag I.previous.previous.previous.previous.previous.hmp
  (m+1) (rootFormula f tag) sigma ctx (PrescribedSourceAxiomSpecialization.seed (rootFormula f tag))
 have hseed := Logic.trans _ _ _ hseedEq hseedNative
 obtain ⟨hF⟩ := TemplateTraceProof.openStep (ctx := ctx) p J hc ha hn (tag+GorbowPRChildTags.stepTag f) counter inputs
 obtain ⟨hftCode⟩ := SymbolicProof.stepValue p J hc ha hn (tag+GorbowPRChildTags.stepTag f) counterRaw priorCall av
 obtain ⟨hfuCode⟩ := SymbolicProof.stepValue p J hc ha hn (tag+GorbowPRChildTags.stepTag f) counterRaw priorNum av
 have hft : Derivation T (.equal
  (specializedValue J.ctag J.atag (stepEnvironment m) (stepTemplate m (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ av) priorCall)
  (rawNumeral (GorbowClosedEquality.instantiateTerm (closedStepFunction (tag+GorbowPRChildTags.stepTag f) counter inputs) prior))) := by
  rw [TemplateTraceProof.instantiateStep]
  exact Logic.trans _ _ _ hftCode hleft
 have hfu : Derivation T (.equal
  (specializedValue J.ctag J.atag (stepEnvironment m) (stepTemplate m (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ av) priorNum)
  (rawNumeral (GorbowClosedEquality.instantiateTerm (closedStepFunction (tag+GorbowPRChildTags.stepTag f) counter inputs) (Term.numeral previous)))) := by
  rw [TemplateTraceProof.instantiateStep]
  exact Logic.trans _ _ _ hfuCode hright
 obtain ⟨hcong⟩ := GeneralTraceProof.internal p T (fun _ h => h) installed lhs rhs t old a _ I
  (stepEnvironment m) (stepTemplate m (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ av) priorCall priorNum
  (closedStepFunction (tag+GorbowPRChildTags.stepTag f) counter inputs) prior (Term.numeral previous)
  hprior hprevious hF hft hfu
 let P := equalValue J.ctag J.atag priorCall priorNum
 obtain ⟨hP⟩ := EncodingProof.equal p J.ctag J.atag hc ha priorCall priorNum prior (Term.numeral previous) hprior hprevious
 obtain ⟨hrootFormula⟩ := EncodingProof.equal p J.ctag J.atag hc ha nextCall left next lhsCall hnext hleft
 obtain ⟨hchildFormula⟩ := EncodingProof.equal p J.ctag J.atag hc ha right output rhsCall (Term.numeral result) hright houtput
 obtain ⟨hliftRoot⟩ := TraceOperations.lift p T (fun _ h => h) installed lhs rhs t old a _ I
  (equalValue J.ctag J.atag nextCall left) P _ (.equal next lhsCall) (.equal prior (Term.numeral previous)) _ hrootFormula hP hseed
 obtain ⟨hfirst⟩ := ConditionalTraceProof.trace p installed lhs rhs t old a _ I P nextCall left right _ _
  (.equal prior (Term.numeral previous)) next lhsCall rhsCall _ _ hP hnext hleft hright hliftRoot hcong
 obtain ⟨hliftChild⟩ := TraceOperations.lift p T (fun _ h => h) installed lhs rhs t old a _ I
  (equalValue J.ctag J.atag right output) P (Term.numeral childCode) (.equal rhsCall (Term.numeral result))
  (.equal prior (Term.numeral previous)) childCode hchildFormula hP (.logical (.reflexive _))
 obtain ⟨hfinal⟩ := ConditionalTraceProof.trace p installed lhs rhs t old a _ I P nextCall right output _ _
  (.equal prior (Term.numeral previous)) next rhsCall (Term.numeral result) _ _ hP hnext hright houtput hfirst hliftChild
 exact CumulativePropositionalSource.CapabilitySupport.inSource installed lhs rhs pF pR old a baseX _ ⟨hfinal⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceProof
