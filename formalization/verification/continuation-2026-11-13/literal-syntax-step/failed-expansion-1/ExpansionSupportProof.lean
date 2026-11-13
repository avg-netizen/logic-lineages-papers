module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem whenEq {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 (x yes no : Program 2) (k : Nat) (out : Term ctx)
 (hx : Computes p G x args (Term.numeral k)) (hy : Computes p G yes args out) :
 Computes p G (whenEqual x k yes no) args out := by
 exact choosePositive p G args _ _ _ .zero out
   (binary p G args equalCode x (constant 2 k) _ _ _ hx (constantValue p G args k) (equalDiagonal p G _)) hy

theorem whenNe {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 (x yes no : Program 2) (value k : Nat) (out : Term ctx) (hne : value ≠ k)
 (hx : Computes p G x args (Term.numeral value)) (hn : Computes p G no args out) :
 Computes p G (whenEqual x k yes no) args out := by
 obtain ⟨hc⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals (GorbowPRNumeralCalculation.Theory p) value k hne
 obtain ⟨hl⟩ := GorbowDerivationSubstitution.Proof.closedLifting (GorbowPRNumeralCalculation.Theory p) _ ⟨hc⟩ ctx
 exact chooseZero p G args _ _ _ out
   (binary p G args equalCode x (constant 2 k) _ _ _ hx (constantValue p G args k) (equalFalse p G _ _ hl)) hn

theorem taskFields {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (binder : Term ctx) (token : Nat) :
 Computes p G kind (taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil) (Term.numeral 1) ∧
 Computes p G context (taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil) binder := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral token ::ᵥ nil
 exact ⟨unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _),
   unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)⟩

theorem taskValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 ptag (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (k : Nat) (q : Program 2) (a : Term ctx)
 (hq : Computes p G q args a) : Computes p G (task k q) args (taskCall ptag k a) :=
 binary p G args _ _ _ _ _ _ (constantValue p G args k) hq (copies p G _ ptag hp _)

theorem singletonValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 ctag (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (q : Program 2) (a : Term ctx)
 (hq : Computes p G q args a) : Computes p G (singleton q) args (HistoryLookup.consCall ctag a .zero) :=
 binary p G args _ _ _ _ _ _ hq (constantValue p G args 0) (copies p G _ ctag hc _)

theorem doubleValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 ctag (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (q : Program 2) (a : Term ctx)
 (hq : Computes p G q args a) : Computes p G (double q) args
 (HistoryLookup.consCall ctag a (HistoryLookup.consCall ctag a .zero)) :=
 binary p G args _ _ _ _ _ _ hq (singletonValue p G args ctag hc q a hq) (copies p G _ ctag hc _)

theorem successValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 (q : Program 2) (a : Term ctx) (hq : Computes p G q args a) :
 Computes p G (success q) args (.succ a) :=
 unary p G args .succ q a (.succ a) hq (StepSupportProof.successor p G a)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.ExpansionSupportProof
