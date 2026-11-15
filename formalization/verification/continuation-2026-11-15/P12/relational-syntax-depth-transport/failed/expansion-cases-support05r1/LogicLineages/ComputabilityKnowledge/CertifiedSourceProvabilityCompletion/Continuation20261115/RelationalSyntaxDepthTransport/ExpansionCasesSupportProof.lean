module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof LiteralSyntaxStep.StepSupportProof

/-- Context weakening changes no source theory or object-level rule. -/
def push {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} {Q : Formula ctx}
 (P : Formula ctx) (h : Hilbert.Local T ctx G Q) : Hilbert.Local T ctx (P :: G) Q :=
 match h with
 | .base d => .base d
 | .hypothesis hm => .hypothesis (List.mem_cons_of_mem P hm)
 | .mp a b => .mp (push P a) (push P b)

/-- Ordinary classical local case analysis, compiled to the unchanged calculus. -/
noncomputable def cases {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (P Q : Formula ctx)
 (hy : Hilbert.Local T ctx (P :: G) Q) (hn : Hilbert.Local T ctx (.neg P :: G) Q) :
 Hilbert.Local T ctx G Q := by
 have hpq := Hilbert.Local.discharge hy
 have hnpq := Hilbert.Local.discharge hn
 apply Hilbert.Local.classical Q
 have hp : Hilbert.Local T ctx (.neg Q :: G) P := by
  apply Hilbert.Local.classical P
  have hq := Hilbert.Local.mp (push (.neg P) (push (.neg Q) hnpq)) (.hypothesis List.mem_cons_self)
  exact Hilbert.Local.explosion P hq (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
 exact Hilbert.Local.mp (push (.neg Q) hpq) hp

/-- Actual equalCode is zero under a local disequality, not only a closed
base-theory theorem. Its paid internal range/soundness supply the implication. -/
theorem equalFalseLocal {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a b : Term ctx)
 (hne : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.neg (.equal a b))) :
 Computes p G equalCode (a ::ᵥ b ::ᵥ nil) .zero := by
 intro tag ht
 let T := GorbowPRNumeralCalculation.Theory p
 let value := HistoryKernel.pairCall tag a b
 let Z := Formula.equal value .zero
 let O := Formula.equal value (.succ .zero)
 obtain ⟨hr⟩ := HistoryKernel.RangeProof.equalRange p tag ht a b
 obtain ⟨hs⟩ := HistoryKernel.EqualProof.internalEqualSound n p tag ht ctx a b
 have hh : Hilbert.Local T ctx (O :: G) O := .hypothesis List.mem_cons_self
 have hz : Hilbert.Local T ctx (O :: G) Z :=
  Hilbert.Local.explosion Z (.mp (.base hs) hh) (push O hne)
 have ho := Hilbert.Local.discharge hz
 exact ⟨.mp (.mp (.mp (.base (.logical (.orElim Z O Z))) (.base (Hilbert.identity Z))) ho) (.base hr)⟩

/-- Runtime equal branch from a genuine internal local equality. -/
theorem whenEqualYes {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 (x yes no : Program 2) (k : Nat) (value out : Term ctx)
 (hx : Computes p G x args value)
 (he : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal value (Term.numeral k)))
 (hy : Computes p G yes args out) : Computes p G (whenEqual x k yes no) args out := by
 exact whenEq p G args x yes no k out (changeValue p G x args value (Term.numeral k) hx he) hy

/-- Runtime rejected equality test, retaining the exact original no branch. -/
theorem whenEqualNo {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) 2)
 (x yes no : Program 2) (k : Nat) (value out : Term ctx)
 (hx : Computes p G x args value)
 (hne : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.neg (.equal value (Term.numeral k))))
 (hn : Computes p G no args out) : Computes p G (whenEqual x k yes no) args out := by
 exact chooseZero p G args _ _ _ out
  (binary p G args equalCode x (constant 2 k) value (Term.numeral k) .zero hx
   (constantValue p G args k) (equalFalseLocal p G value (Term.numeral k) hne)) hn
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
