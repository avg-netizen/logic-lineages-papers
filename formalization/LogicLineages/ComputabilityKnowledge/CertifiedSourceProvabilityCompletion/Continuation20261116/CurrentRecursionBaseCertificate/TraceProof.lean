module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
theorem exactTrace : Targets.InternalTrace := by
 intro installed lhs rhs k t old a baseX pF pR c hA I m tag inputs result childCode ctx
 let p := CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let J := tags I
 let av := numeralValues J.numeralTag (inputs.map (Term.numeral (n := ctx)))
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let aa := GorbowPRNumeralCalculation.numeralArguments inputs
 have hav : ∀ i, Nonempty (Derivation T (.equal (av.get i) (rawNumeral (aa.get i)))) :=
  CurrentCompositionCertificate.NativeValuesProof.numerals p J I.previous.previous.previous.previous.hnumeral inputs
 obtain ⟨hz⟩ := ValueTraceProof.numeral (ctx := ctx) p J I.previous.previous.previous.previous.hnumeral 0
 have hargs : ∀ i, Nonempty (Derivation T
  (.equal ((zero ::ᵥ av).get i) (rawNumeral (((.zero : Term 0) ::ᵥ aa).get i)))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hz⟩
  | succ i => exact hav i
 obtain ⟨hparent⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral tag (zero ::ᵥ av) (.zero ::ᵥ aa) hargs
 obtain ⟨hchild⟩ := CurrentCompositionCertificate.NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral (tag+1) av aa hav
 obtain ⟨hout⟩ := ValueTraceProof.numeral (ctx := ctx) p J I.previous.previous.previous.previous.hnumeral result
 let sigma := fun i : Fin m => (Term.numeral (inputs.get i) : Term 0)
 have hseedInputs : ∀ i, Nonempty (Derivation T
  (.equal (av.get i) ((PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma).get i))) := by
  intro i
  simpa only [sigma,aa,GorbowPRNumeralCalculation.numeralArguments,PrescribedRuntimeSpecialization.numeralInputs,
   List.Vector.get_ofFn,List.Vector.get_map,rawNumeral] using hav i
 obtain ⟨hseedEq⟩ := CurrentCompositionCertificate.SeedInputProof.certificateCongruence p J.mtag
  I.previous.current.ctag I.previous.current.atag I.previous.current.constructorTag
  I.previous.current.h_ctag I.previous.current.h_atag m (rootFormula m tag)
  av (PrescribedRuntimeSpecialization.numeralInputs sigma)
  (Term.numeral (PrescribedSourceAxiomSpecialization.seed (rootFormula m tag))) hseedInputs
 obtain ⟨hseedNative⟩ := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 p (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  I.previous.current J.mtag I.previous.previous.previous.previous.hmp m (rootFormula m tag) sigma ctx
  (PrescribedSourceAxiomSpecialization.seed (rootFormula m tag))
 have hseed := Logic.trans _ _ _ hseedEq hseedNative
 obtain ⟨hfinal⟩ := TraceCoreProof.transitivity p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor _ _ _ _ _
  (GorbowPRDefiningEquations.call tag (.zero ::ᵥ aa)) (GorbowPRDefiningEquations.call (tag+1) aa)
  (Term.numeral result) _ childCode hparent hchild hout hseed (.logical (.reflexive _))
 exact GorbowTheoryProofProof.monotonicity T _
  (CurrentSourceSeededSpecialization.SourceProof.inclusion installed lhs rhs pF pR old a baseX) ctx _ ⟨hfinal⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.TraceProof
