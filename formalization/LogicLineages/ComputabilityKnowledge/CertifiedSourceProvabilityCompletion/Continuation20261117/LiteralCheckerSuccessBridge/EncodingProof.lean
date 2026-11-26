module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open FixedFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph
/-- Structural congruence of the literal template encoder, not native evaluation. -/
theorem termCongruence {arity n depth inputs ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (e : Environment n depth inputs) (xs ys : List.Vector (Term ctx) inputs)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (ys.get i))))
 (t : Term n) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag e xs t) (termValue K.ctag K.atag e ys t))) := by
 induction t with
 | var i =>
  cases he : e i with
  | inl j =>
   simp only [termValue,he]
   exact ⟨.logical (.reflexive _)⟩
  | inr j => simpa only [termValue,he] using h j
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p K.ctag K.ctag 2 H.hc H.hc _ _ ih
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht; obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p K.ctag K.atag K.ctag K.atag 3 H.hc H.ha H.hc H.ha _ _ _ _ ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht; obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p K.ctag K.atag K.ctag K.atag 4 H.hc H.ha H.hc H.ha _ _ _ _ ht hu
 | universalFunction t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p K.ctag K.ctag 5 H.hc H.hc _ _ ih

/-- Convert actual numeral quotation calls through the original closed-term
encoding theorem; no conclusion is inferred from calibration alone. -/
theorem rawBinary {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K) (r s : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RetainedBaseLiteralBinary.rawBinary K (Term.numeral (n := ctx) r) (Term.numeral s))
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode
    (GorbowBooleanTruth.binaryCodeTerm (n := 0) 0 (Term.numeral r) (Term.numeral s))))))) := by
 let sigma : Fin 2 → Term 0 := (Term.numeral r ::ᵥ Term.numeral s ::ᵥ nil).get
 let xs : List.Vector (Term ctx) 2 := LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral r) ::ᵥ
  LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral s) ::ᵥ nil
 have hc : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (xs.get i) ((PrescribedRuntimeSpecialization.numeralInputs sigma).get i))) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [xs,sigma,PrescribedRuntimeSpecialization.numeralInputs,List.Vector.get_ofFn,List.Vector.get_cons_zero,rawNumeral] using
     PrescribedRuntimeCallCongruence.ValueProof.numeral (ctx := ctx) p K.numeralTag H.hn r
  · have hj : j = 0 := Fin.eq_zero j
    subst j
    simpa only [xs,sigma,PrescribedRuntimeSpecialization.numeralInputs,List.Vector.get_ofFn,List.Vector.get_cons_succ,List.Vector.get_cons_zero,rawNumeral] using
     PrescribedRuntimeCallCongruence.ValueProof.numeral (ctx := ctx) p K.numeralTag H.hn s
 obtain ⟨h1⟩ := termCongruence p K H (PrescribedRuntimeSpecialization.runtimeEnvironment 2) xs
  (PrescribedRuntimeSpecialization.numeralInputs sigma) hc (GorbowBooleanTruth.binaryCodeTerm 0 (.var 0) (.var 1))
 obtain ⟨h2⟩ := PrescribedRuntimeSpecialization.EncodingProof.term (ctx := ctx) p K.ctag K.atag H.hc H.ha
  (PrescribedRuntimeSpecialization.runtimeEnvironment 2) (GorbowBooleanTruth.binaryCodeTerm 0 (.var 0) (.var 1)) sigma
 have hget : ((Term.numeral r : Term 0) ::ᵥ Term.numeral s ::ᵥ nil).get (1 : Fin 2) = Term.numeral s := rfl
 have hv : GorbowSubstitution.substitute
   (assignment (PrescribedRuntimeSpecialization.runtimeEnvironment 2) sigma)
   (GorbowBooleanTruth.binaryCodeTerm 0 (.var 0) (.var 1)) =
   GorbowBooleanTruth.binaryCodeTerm (n := 0) 0 (Term.numeral r) (Term.numeral s) := by
  simp only [GorbowBooleanTruth.binaryCodeTerm,GorbowSubstitution.substitute,
   assignment,PrescribedRuntimeSpecialization.runtimeEnvironment,sigma,hget,List.Vector.get_cons_zero,
   List.Vector.get_cons_succ,CurrentCalculationFormulaProgram.NativeProof.substPair,
   CurrentCalculationFormulaProgram.NativeProof.substTuple,SixSol20261112.Fuel.Logic.substNumeral,
   GorbowRegistryTuple.headerTerm,List.map_cons,List.map_nil,GorbowFormulaSubstitution.renameTerm]
 rw [hv] at h2
 exact ⟨Logic.trans _ _ _ h1 h2⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.EncodingProof
