module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.IndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryRuleSuffix InternalAtomsProof
/-- Select original kind2 branch after its actual decoded kind comparison. -/
theorem enterIndex {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (bound rest token raw out : Term ctx)
 (hi : Computes p G indexCode (activeInput ptag ctag (Term.numeral 2) bound rest token raw) out) :
 Computes p G emitCode (activeInput ptag ctag (Term.numeral 2) bound rest token raw) out := by
 let args := activeInput ptag ctag (Term.numeral 2) bound rest token raw
 have hk := kind p G ptag ctag hp hc (Term.numeral 2) bound rest token raw
 have ht := binary p G args equalCode kindCode (constant 3 2) (Term.numeral 2) (Term.numeral 2) (.succ .zero)
  hk (constantValue p G args 2) (equalDiagonal p G (Term.numeral 2))
 exact enterActive p G ptag ctag hc (Term.numeral 2) bound rest token raw out
  (choosePositive p G args _ nonIndexCode indexCode .zero out ht hi)
theorem zeroDepth {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (rest token raw : Term ctx) :
 Computes p G depthCode (activeInput ptag ctag (Term.numeral 2) .zero rest token raw) .zero := by
 apply unary p G _ HistoryCodec.predecessor boundCode .zero .zero
  (bound p G ptag ctag hp hc (Term.numeral 2) .zero rest token raw)
 intro tag ht
 obtain ⟨h⟩ := HistoryDifference.EquationsProof.predecessorZero n p tag ht ctx
 exact ⟨.base h⟩
theorem equalCase {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (state depth raw : Term ctx)
 (hd : Computes p G depthCode (state ::ᵥ depth ::ᵥ raw ::ᵥ nil) depth) :
 Computes p G indexCode (state ::ᵥ depth ::ᵥ raw ::ᵥ nil) raw := by
 let args := state ::ᵥ depth ::ᵥ raw ::ᵥ nil
 have hz := binary p G args HistoryCodec.difference (.projection 1) depthCode depth depth .zero
  (projection p G args 1) hd (ArithmeticProof.differenceDiagonal p G depth)
 have he := binary p G args equalCode (.projection 1) depthCode depth depth (.succ .zero)
  (projection p G args 1) hd (equalDiagonal p G depth)
 exact chooseZero p G args _ _ variableCode raw hz
  (choosePositive p G args _ (constant 3 0) (.projection 2) .zero raw he (projection p G args 2))
theorem belowCase {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state token depth gap raw : Term ctx)
 (hd : Computes p G depthCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) depth)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add token (.succ gap)) depth)) :
 Computes p G indexCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) (variableValue ctag token) := by
 let args := state ::ᵥ token ::ᵥ raw ::ᵥ nil
 have ht := binary p G args HistoryCodec.difference (.projection 1) depthCode token depth (.succ gap)
  (projection p G args 1) hd (ArithmeticProof.differenceBelow p G token depth gap h)
 exact choosePositive p G args _ _ variableCode gap _ ht (variableCodeValue p G ctag hc state token raw)
theorem aboveCase {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (state token depth gap raw : Term ctx)
 (hd : Computes p G depthCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) depth)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add depth (.succ gap)) token)) :
 Computes p G indexCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) .zero := by
 let args := state ::ᵥ token ::ᵥ raw ::ᵥ nil
 have hz := binary p G args HistoryCodec.difference (.projection 1) depthCode token depth .zero
  (projection p G args 1) hd (ArithmeticProof.differenceAbove p G token depth gap h)
 have he := binary p G args equalCode (.projection 1) depthCode token depth .zero
  (projection p G args 1) hd (ArithmeticProof.equalAbove p G token depth gap h)
 exact chooseZero p G args _ _ variableCode .zero hz
  (chooseZero p G args _ (constant 3 0) (.projection 2) .zero he (constantValue p G args 0))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.IndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.IndexProof
