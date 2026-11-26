module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherCombinatorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport DispatcherSupportProof

theorem projection {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity) (i : Fin arity) :
    Computes p G (.projection i) args (args.get i) := liftClosed p G _ _ _ (ConstructorSupportProof.projection p args i)
theorem constantValue {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity) (k : Nat) :
    Computes p G (constant arity k) args (Term.numeral k) := liftClosed p G _ _ _ (ConstructorSupportProof.constantValue p args k)
theorem copies {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (q : Program arity) qtag
    (hq : (nodes p)[qtag]? = some ⟨arity,q⟩) (args : List.Vector (Term ctx) arity) :
    Computes p G q args (call qtag args) := by
  intro tag ht
  obtain ⟨h⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag qtag arity q ht hq ctx args
  exact ⟨.base h⟩
theorem predecessor {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a : Term ctx) :
    Computes p G HistoryCodec.predecessor (.succ a ::ᵥ nil) a := by
  intro tag ht
  obtain ⟨h⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p tag ht ctx a
  exact ⟨.base h⟩
theorem decoder {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (right : Bool) (a b : Term ctx) :
    Computes p G (HistoryDecoder.decoder right) (HistoryKernel.pairCall ptag a b ::ᵥ nil)
      (HistoryDecoder.StepNormalProof.chosen right a b) := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.decoderCrossPair p tag ptag right ht hp a b
  exact ⟨.base h⟩
theorem equalDiagonal {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a : Term ctx) :
    Computes p G equalCode (a ::ᵥ a ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := HistoryKernel.EqualProof.diagonal p tag ht a
  exact ⟨.base h⟩
theorem equalFalse {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a b : Term ctx)
    (hne : Derivation (GorbowPRNumeralCalculation.Theory p) (.neg (.equal a b))) :
    Computes p G equalCode (a ::ᵥ b ::ᵥ nil) .zero := by
  intro tag ht
  let T := GorbowPRNumeralCalculation.Theory p
  let value := HistoryKernel.pairCall tag a b
  let Z := Formula.equal value .zero
  let O := Formula.equal value (.succ .zero)
  obtain ⟨hr⟩ := HistoryKernel.RangeProof.equalRange p tag ht a b
  obtain ⟨hs⟩ := HistoryKernel.EqualProof.internalEqualSound n p tag ht ctx a b
  have hh : Hilbert.Local T ctx [O] O := .hypothesis List.mem_cons_self
  have ho : Derivation T (.imp O Z) := Hilbert.Local.finish (Hilbert.Local.discharge
    (Hilbert.Local.explosion Z (.mp (.base hs) hh) (.base hne)))
  exact ⟨.base (.mp (.mp (.mp (.logical (.orElim Z O Z)) (Hilbert.identity Z)) ho) hr)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
