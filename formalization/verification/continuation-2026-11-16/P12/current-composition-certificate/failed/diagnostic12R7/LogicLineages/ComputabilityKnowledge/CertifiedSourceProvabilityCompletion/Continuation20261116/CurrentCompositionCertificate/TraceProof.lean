module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.NativeValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem exactTrace : Targets.InternalTrace := by
 intro installed lhs rhs k t old a baseX pF pR c hA I m n f g tag inputs values result codes functionCode ctx
 let p := CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let J := tags I
 let av := numeralValues J.numeralTag (inputs.map (Term.numeral (n := ctx)))
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag (values.map (Term.numeral (n := ctx)))
 let aa := GorbowPRNumeralCalculation.numeralArguments inputs
 let bb := List.Vector.ofFn (fun i => GorbowPRDefiningEquations.call (tag+GorbowPRChildTags.argumentTag f g i) aa)
 let cc := GorbowPRNumeralCalculation.numeralArguments values
 have hav : ∀ i, Nonempty (Derivation T (.equal (av.get i) (rawNumeral (aa.get i)))) :=
  NativeValuesProof.numerals p J I.previous.previous.previous.previous.hnumeral inputs
 have hcv : ∀ i, Nonempty (Derivation T (.equal (cv.get i) (rawNumeral (cc.get i)))) :=
  NativeValuesProof.numerals p J I.previous.previous.previous.previous.hnumeral values
 have hbv : ∀ i, Nonempty (Derivation T (.equal (bv.get i) (rawNumeral (bb.get i)))) := by
  intro i
  have h := NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
   I.previous.previous.previous.previous.hnumeral (tag+GorbowPRChildTags.argumentTag f g i) av aa hav
  simpa only [bv,bb,childValues,List.Vector.get_ofFn] using h
 obtain ⟨hparent⟩ := NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral tag av aa hav
 obtain ⟨hleft⟩ := NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral (tag+1) bv bb hbv
 obtain ⟨hright⟩ := NativeValuesProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral (tag+1) cv cc hcv
 obtain ⟨hout⟩ := ValueTraceProof.numeral (ctx := ctx) p J I.previous.previous.previous.previous.hnumeral result
 let sigma := fun i : Fin m => (Term.numeral (inputs.get i) : Term 0)
 have hseedInputs : ∀ i, Nonempty (Derivation T
  (.equal (av.get i) ((PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma).get i))) := by
  intro i
  simpa only [sigma,aa,GorbowPRNumeralCalculation.numeralArguments,PrescribedRuntimeSpecialization.numeralInputs,
   List.Vector.get_ofFn,List.Vector.get_map,rawNumeral] using hav i
 obtain ⟨hseedEq⟩ := SeedInputProof.certificateCongruence p J.mtag I.previous.current.ctag I.previous.current.atag
  I.previous.current.constructorTag I.previous.current.h_ctag I.previous.current.h_atag m (rootFormula f g tag)
  av (PrescribedRuntimeSpecialization.numeralInputs sigma)
  (Term.numeral (PrescribedSourceAxiomSpecialization.seed (rootFormula f g tag))) hseedInputs
 obtain ⟨hseedNative⟩ := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 p (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  I.previous.current J.mtag I.previous.previous.previous.previous.hmp m (rootFormula f g tag) sigma ctx
  (PrescribedSourceAxiomSpecialization.seed (rootFormula f g tag))
 have hseed := Logic.trans _ _ _ hseedEq hseedNative
 have hcodes : ∀ i, Nonempty (Derivation T
  (.equal ((codes.map (Term.numeral (n := ctx))).get i) (Term.numeral (codes.get i)))) := by
  intro i
  rw [List.Vector.get_map]
  exact ⟨.logical (.reflexive _)⟩
 obtain ⟨hcall⟩ := TraceCallProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor
  I.previous.previous.previous.previous.hc I.previous.previous.previous.previous.hreflexivity
  I.previous.previous.previous.previous.hnumeral (tag+1) bv cv (codes.map Term.numeral) bb cc codes hbv hcv hcodes
 obtain ⟨hfirst⟩ := TraceCoreProof.transitivity p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor _ _ _ _ _
  (GorbowPRDefiningEquations.call tag aa) (GorbowPRDefiningEquations.call (tag+1) bb)
  (GorbowPRDefiningEquations.call (tag+1) cc) _ _ hparent hleft hright hseed hcall
 obtain ⟨hfinal⟩ := TraceCoreProof.transitivity p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor _ _ _ _ _
  (GorbowPRDefiningEquations.call tag aa) (GorbowPRDefiningEquations.call (tag+1) cc) (Term.numeral result)
  _ functionCode hparent hright hout hfirst (.logical (.reflexive _))
 exact GorbowTheoryProofProof.monotonicity T _
  (CurrentSourceSeededSpecialization.SourceProof.inclusion installed lhs rhs pF pR old a baseX) ctx _ ⟨hfinal⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceProof
