module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NonIndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix InternalAtomsProof
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
/-- The fixed kind comparison is computed from original defining equations. -/
theorem zeroNotTwo {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) :
 Computes p G equalCode ((.zero : Term ctx) ::ᵥ Term.numeral 2 ::ᵥ nil) .zero := by
 have h := FiniteRuleFourDispatcher.NumericProof.numerals p G equalCode (0 ::ᵥ 2 ::ᵥ nil)
 simpa only [HistoryRuleSuffix.NativeProof.equalEval,List.Vector.map_cons,List.Vector.map_nil,
  show (0=2) = False from propext (by decide),ite_false,Term.numeral] using h
/-- Term variable marker is suppressed pending the actual index task. -/
theorem marker {n ctx : Nat} (p : Program n) etag ptag ctag
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (bound rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag .zero bound rest) .zero raw) .zero)) := by
 let args := activeInput ptag ctag .zero bound rest .zero raw
 have hk := kind p [] ptag ctag hp hc .zero bound rest .zero raw
 have hz := binary p [] args equalCode kindCode (constant 3 0) .zero .zero (.succ .zero)
  hk (constantValue p [] args 0) (equalDiagonal p [] .zero)
 have ht := binary p [] args equalCode kindCode (constant 3 2) .zero (Term.numeral 2) .zero
  hk (constantValue p [] args 2) (zeroNotTwo p [])
 have hn : Computes p [] nonIndexCode args .zero :=
  choosePositive p [] args _ singletonCode _ .zero .zero hz
   (chooseZero p [] args (.projection 1) (constant 3 0) singletonCode .zero
    (projection p [] args 1) (constantValue p [] args 0))
 have ha : Computes p [] activeCode args .zero := chooseZero p [] args _ nonIndexCode indexCode .zero ht hn
 obtain ⟨hout⟩ := enterActive p [] ptag ctag hc .zero bound rest .zero raw .zero ha etag he
 exact ⟨hout.finish⟩
theorem termSuccessor {n ctx : Nat} (p : Program n) etag ptag ctag
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (bound rest token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag .zero bound rest) (.succ token) raw)
   (singletonValue ctag (.succ token)))) := by
 let args := activeInput ptag ctag .zero bound rest (.succ token) raw
 have hk := kind p [] ptag ctag hp hc .zero bound rest (.succ token) raw
 have hz := binary p [] args equalCode kindCode (constant 3 0) .zero .zero (.succ .zero)
  hk (constantValue p [] args 0) (equalDiagonal p [] .zero)
 have ht := binary p [] args equalCode kindCode (constant 3 2) .zero (Term.numeral 2) .zero
  hk (constantValue p [] args 2) (zeroNotTwo p [])
 have hn : Computes p [] nonIndexCode args (singletonValue ctag (.succ token)) :=
  choosePositive p [] args _ singletonCode _ .zero _ hz
   (choosePositive p [] args (.projection 1) (constant 3 0) singletonCode token _
    (projection p [] args 1) (singleton p [] ctag hc _ (.succ token) raw))
 have ha : Computes p [] activeCode args (singletonValue ctag (.succ token)) :=
  chooseZero p [] args _ nonIndexCode indexCode _ ht hn
 obtain ⟨hout⟩ := enterActive p [] ptag ctag hc .zero bound rest (.succ token) raw _ ha etag he
 exact ⟨hout.finish⟩
/-- Formula-kind and malformed nonindex kinds are copied literally. -/
theorem otherKind {n ctx : Nat} (p : Program n) etag ptag ctag
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (k bound rest token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.neg (.equal k .zero)) (.imp (.neg (.equal k (Term.numeral 2)))
   (.equal (emitCall etag (stateValue ptag ctag k bound rest) token raw) (singletonValue ctag token))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let N0 := Formula.neg (.equal k .zero)
 let N2 := Formula.neg (.equal k (Term.numeral 2))
 let G := [N2,N0]
 let args := activeInput ptag ctag k bound rest token raw
 have h0 : Hilbert.Local T ctx G N0 := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have h2 : Hilbert.Local T ctx G N2 := .hypothesis List.mem_cons_self
 have hk := kind p G ptag ctag hp hc k bound rest token raw
 have hz := binary p G args equalCode kindCode (constant 3 0) k .zero .zero hk
  (constantValue p G args 0) (equalFalseLocal p G k .zero h0)
 have ht := binary p G args equalCode kindCode (constant 3 2) k (Term.numeral 2) .zero hk
  (constantValue p G args 2) (equalFalseLocal p G k (Term.numeral 2) h2)
 have hn : Computes p G nonIndexCode args (singletonValue ctag token) :=
  chooseZero p G args _ singletonCode _ _ hz (singleton p G ctag hc _ token raw)
 have ha : Computes p G activeCode args (singletonValue ctag token) :=
  chooseZero p G args _ nonIndexCode indexCode _ ht hn
 obtain ⟨hout⟩ := enterActive p G ptag ctag hc k bound rest token raw _ ha etag he
 exact ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NonIndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NonIndexProof
