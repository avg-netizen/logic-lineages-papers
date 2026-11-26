module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
/-- ALL codes, including every task kind/token rejection. -/
def NativeExpand : Prop := ∀ v : List.Vector Nat 2,
 evaluate expandCode v = Encodable.encode (GorbowSyntaxValidation.expand (Nat.unpair (v.get 0)) (v.get 1))
/-- ALL codes and original decode/default State semantics, not valid-state-only. -/
def NativeStep : Prop := ∀ v : List.Vector Nat 2,
 evaluate stepCode v = Encodable.encode (GorbowSyntaxValidation.step
  ((Encodable.decode (α := GorbowSyntaxValidation.State) (v.get 0)).getD none) (v.get 1))

def InternalFormulaBinary : Prop := ∀ n (p : Program n) etag ptag ctag,
 (nodes p)[etag]? = some ⟨2,expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (binder : Term ctx) (i : Fin 3),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (taskCall ptag 1 binder) (Term.numeral (7+i.val)))
    (.succ (HistoryLookup.consCall ctag (taskCall ptag 1 binder)
      (HistoryLookup.consCall ctag (taskCall ptag 1 binder) .zero)))))
def InternalQuantifier : Prop := ∀ n (p : Program n) etag ptag ctag,
 (nodes p)[etag]? = some ⟨2,expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (binder : Term ctx) (i : Fin 2),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (expandCall etag (taskCall ptag 1 binder) (Term.numeral (10+i.val)))
    (.succ (HistoryLookup.consCall ctag (taskCall ptag 1 (.succ binder)) .zero))))

def InternalNone : Prop := ∀ n (p : Program n) stag,
 (nodes p)[stag]? = some ⟨2,stepCode⟩ → ∀ ctx (token : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag .zero token) .zero))
def InternalEmpty : Prop := ∀ n (p : Program n) stag,
 (nodes p)[stag]? = some ⟨2,stepCode⟩ → ∀ ctx (token : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall stag (.succ .zero) token) .zero))
/-- Actual expansion equality is a local branch premise, not native reflection.
The successful operational step prepends exactly the returned task row. -/
def InternalPrepend : Prop := ∀ n (p : Program n) stag etag ctag atag,
 (nodes p)[stag]? = some ⟨2,stepCode⟩ →
 (nodes p)[etag]? = some ⟨2,expandCode⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (t rest token added : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (expandCall etag t token) (.succ added))
    (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag t rest)) token)
      (.succ (HistoryAppend.appendCall atag added rest)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Targets
