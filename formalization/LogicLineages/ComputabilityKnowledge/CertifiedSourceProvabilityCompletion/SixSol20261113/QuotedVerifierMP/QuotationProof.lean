module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.NativeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationProof
public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

/-- External calibration specialized to raw Nat lists, not a cast from the
typed History theorem. The same actual append AST and list codec are used. -/
theorem nativeAppendNat (left right : List Nat) :
 evaluate HistoryAppend.append (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) = Encodable.encode (left++right) := by
 rw [HistoryAppend.NativeProof.appendEval]
 induction left with
 | nil => rfl
 | cons a left ih =>
   rw [HistoryLookup.NativeProof.encodeCons,HistoryAppend.NativeProof.resultCons,ih]
   rfl

/-- Constructive PR numeral calculation followed by the proved closed lifting
rule. It does not turn native semantic truth into an additional source axiom. -/
theorem numeralCalculation {n arity : Nat} (p : Program n) tag (q : Program arity)
 (hq : (nodes p)[tag]? = some ⟨arity,q⟩) (v : List.Vector Nat arity) (ctx : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (v.map (Term.numeral : Nat → Term ctx))) (Term.numeral (evaluate q v)))) := by
 obtain ⟨h⟩ := GorbowPRNumeralCalculation.Proof.numeralCalculation n p tag arity q hq v
 obtain ⟨hl⟩ := GorbowDerivationSubstitution.Proof.closedLifting (GorbowPRNumeralCalculation.Theory p) _ ⟨h⟩ ctx
 have he : (v.map (Term.numeral : Nat → Term 0)).map (substitute (Fin.elim0 : Fin 0 → Term ctx)) =
   v.map (Term.numeral : Nat → Term ctx) := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map,Logic.substNumeral]
 simpa only [weakenClosed,substituteFormula,Logic.substCall,GorbowPRNumeralCalculation.numeralArguments,
  he,Logic.substNumeral] using (show Nonempty (Derivation _ _) from ⟨hl⟩)

theorem numeralAdd (T : Sentence → Prop) (ctx a b : Nat) :
 Nonempty (Derivation T (.equal (.add (Term.numeral a : Term ctx) (Term.numeral b)) (Term.numeral (a+b)))) := by
 induction b with
 | zero => exact ⟨.arithmetic (.addZero (Term.numeral a))⟩
 | succ b ih =>
   obtain ⟨hi⟩ := ih
   have hs := Logic.unary (.succ (.var 0)) _ _ hi
   simp only [substitute,Fin.cases_zero] at hs
   exact ⟨Logic.trans _ _ _ (.arithmetic (.addSucc (Term.numeral a) (Term.numeral b))) hs⟩

theorem doubleQuote (T : Sentence → Prop) (ctx : Nat) (sigma : Sentence) :
 Nonempty (Derivation T
  (.equal (.add (Term.numeral (GorbowCodeConstructors.formulaNumber sigma) : Term ctx)
    (Term.numeral (GorbowCodeConstructors.formulaNumber sigma)))
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))) := by
 simpa only [GorbowSortedSyntaxCode.formulaCode,GorbowSortedSyntaxCode.tagFormula,Nat.two_mul] using
  numeralAdd T ctx (GorbowCodeConstructors.formulaNumber sigma) (GorbowCodeConstructors.formulaNumber sigma)

theorem implicationQuote {n ctx : Nat} (p : Program n) atag ctag
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (sigma tau : Sentence) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralRawMP.implicationRaw atag ctag
    (Term.numeral (GorbowCodeConstructors.formulaNumber sigma) : Term ctx)
    (Term.numeral (GorbowCodeConstructors.formulaNumber tau)))
   (Term.numeral (GorbowCodeConstructors.formulaNumber (.imp sigma tau))))) := by
 let sr := GorbowFormulaPrefixCode.encode sigma
 let tr := GorbowFormulaPrefixCode.encode tau
 let middle := Encodable.encode (sr++tr)
 obtain ⟨happ⟩ := numeralCalculation p atag HistoryAppend.append ha
  (Encodable.encode sr ::ᵥ Encodable.encode tr ::ᵥ nil) ctx
 rw [nativeAppendNat] at happ
 obtain ⟨hcons⟩ := numeralCalculation p ctag HistoryCodec.cons hc (7 ::ᵥ middle ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.nativeConsAllVectors] at hcons
 have he := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) ctag
  (Term.numeral 7 ::ᵥ HistoryAppend.appendCall atag (Term.numeral (Encodable.encode sr)) (Term.numeral (Encodable.encode tr)) ::ᵥ nil)
  (Term.numeral 7 ::ᵥ Term.numeral middle ::ᵥ nil) (by
   intro i
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i =>
     have hi : i = 0 := Fin.eq_zero i
     subst i
     exact happ)
 exact ⟨Logic.trans _ _ _ he hcons⟩

theorem doubleImplicationQuote {n ctx : Nat} (p : Program n) atag ctag
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (sigma tau : Sentence) :
 let raw : Term ctx := LiteralRawMP.implicationRaw atag ctag
  (Term.numeral (GorbowCodeConstructors.formulaNumber sigma)) (Term.numeral (GorbowCodeConstructors.formulaNumber tau))
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (.add raw raw) (Term.numeral (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau))))) := by
 obtain ⟨h⟩ := implicationQuote (ctx := ctx) p atag ctag ha hc sigma tau
 have hd := Logic.unary (.add (.var 0) (.var 0)) _ _ h
 simp only [substitute,Fin.cases_zero] at hd
 obtain ⟨hnum⟩ := doubleQuote (GorbowPRNumeralCalculation.Theory p) ctx (.imp sigma tau)
 exact ⟨Logic.trans _ _ _ hd hnum⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
