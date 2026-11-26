module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRuntimeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof LiteralSyntaxStep.StepSupportProof ExpansionCasesSupportProof

theorem kindValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩) (task tok : Term ctx) :
 Computes p G kind (task ::ᵥ tok ::ᵥ nil) (call l (task ::ᵥ nil)) :=
 unary p G _ _ _ _ _ (projection p G _ 0) (copies p G _ l hl _)
theorem contextValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (r : Nat)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (task tok : Term ctx) :
 Computes p G context (task ::ᵥ tok ::ᵥ nil) (call r (task ::ᵥ nil)) :=
 unary p G _ _ _ _ _ (projection p G _ 0) (copies p G _ r hr _)

/-- Original term rejection, including ALL nonconstructor runtime tokens. -/
theorem termReject {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩) (task tok : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 0)))
 (hne : ∀ i : Fin 6, Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal tok (Term.numeral i.val)))) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) .zero := by
 let args := task ::ᵥ tok ::ᵥ nil
 have hkind := changeValue p G kind args _ (Term.numeral 0) (kindValue p G l hl task tok) hk
 have ht : Computes p G (.projection 1) args tok := projection p G args 1
 apply whenEq p G args _ _ _ 0 _ hkind
 apply whenEqualNo p G args _ _ _ 0 tok .zero ht (hne 0)
 apply whenEqualNo p G args _ _ _ 1 tok .zero ht (hne 1)
 apply whenEqualNo p G args _ _ _ 2 tok .zero ht (hne 2)
 apply whenEqualNo p G args _ _ _ 5 tok .zero ht (hne 5)
 apply whenEqualNo p G args _ _ _ 3 tok .zero ht (hne 3)
 apply whenEqualNo p G args _ _ _ 4 tok .zero ht (hne 4)
 exact constantValue p G args 0

/-- Original formula rejection, including ALL nonconstructor runtime tokens. -/
theorem formulaReject {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩) (task tok : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 1)))
 (hne : ∀ i : Fin 12, Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal tok (Term.numeral i.val)))) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) .zero := by
 let args := task ::ᵥ tok ::ᵥ nil
 have hkind := changeValue p G kind args _ (Term.numeral 1) (kindValue p G l hl task tok) hk
 have ht : Computes p G (.projection 1) args tok := projection p G args 1
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hkind
 apply whenEq p G args _ _ _ 1 _ hkind
 apply whenEqualNo p G args _ _ _ 0 tok .zero ht (hne 0)
 apply whenEqualNo p G args _ _ _ 4 tok .zero ht (hne 4)
 apply whenEqualNo p G args _ _ _ 1 tok .zero ht (hne 1)
 apply whenEqualNo p G args _ _ _ 2 tok .zero ht (hne 2)
 apply whenEqualNo p G args _ _ _ 3 tok .zero ht (hne 3)
 apply whenEqualNo p G args _ _ _ 5 tok .zero ht (hne 5)
 apply whenEqualNo p G args _ _ _ 6 tok .zero ht (hne 6)
 apply whenEqualNo p G args _ _ _ 7 tok .zero ht (hne 7)
 apply whenEqualNo p G args _ _ _ 8 tok .zero ht (hne 8)
 apply whenEqualNo p G args _ _ _ 9 tok .zero ht (hne 9)
 apply whenEqualNo p G args _ _ _ 10 tok .zero ht (hne 10)
 apply whenEqualNo p G args _ _ _ 11 tok .zero ht (hne 11)
 exact constantValue p G args 0

/-- Original outer fallback rejects every runtime task kind other than0/1/2. -/
theorem kindReject {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩) (task tok : Term ctx)
 (hne : ∀ i : Fin 3, Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.neg (.equal (call l (task ::ᵥ nil)) (Term.numeral i.val)))) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) .zero := by
 let args := task ::ᵥ tok ::ᵥ nil
 have hk := kindValue p G l hl task tok
 apply whenEqualNo p G args _ _ _ 0 _ .zero hk (hne 0)
 apply whenEqualNo p G args _ _ _ 1 _ .zero hk (hne 1)
 apply whenEqualNo p G args _ _ _ 2 _ .zero hk (hne 2)
 exact constantValue p G args 0

theorem indexRoute {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩) (task tok out : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 2)))
 (hi : Computes p G indexBranch (task ::ᵥ tok ::ᵥ nil) out) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) out := by
 let args := task ::ᵥ tok ::ᵥ nil
 have hkind := changeValue p G kind args _ (Term.numeral 2) (kindValue p G l hl task tok) hk
 apply whenNe p G args _ _ _ 2 0 _ (by decide) hkind
 apply whenNe p G args _ _ _ 2 1 _ (by decide) hkind
 exact whenEq p G args _ _ _ 2 _ hkind hi

theorem differenceValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (r dtag : Nat)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (task tok : Term ctx) :
 Computes p G (applyTwo HistoryCodec.difference (.projection 1) context) (task ::ᵥ tok ::ᵥ nil)
  (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil))) :=
 binary p G _ _ _ _ _ _ _ (projection p G _ 1) (contextValue p G r hr task tok) (copies p G _ dtag hd _)

theorem indexZero {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l r dtag : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (task tok : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 2)))
 (hz : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil))) .zero)) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) .zero := by
 apply indexRoute p G l hl task tok .zero hk
 exact chooseZero p G _ _ _ _ .zero
  (changeValue p G _ _ _ .zero (differenceValue p G r dtag hr hd task tok) hz)
  (constantValue p G _ 0)

theorem indexPositive {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (l r dtag : Nat)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (task tok gap : Term ctx)
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral 2)))
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil))) (.succ gap))) :
 Computes p G expandCode (task ::ᵥ tok ::ᵥ nil) (.succ .zero) := by
 apply indexRoute p G l hl task tok (.succ .zero) hk
 exact choosePositive p G _ _ _ _ gap (.succ .zero)
  (changeValue p G _ _ _ (.succ gap) (differenceValue p G r dtag hr hd task tok) hg)
  (constantValue p G _ 1)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRuntimeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRuntimeProof
