module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.Fuel
/-- Explicit original cons constructor terms; not an assertion that an arbitrary
raw code is the image of a native list. Elements remain arbitrary runtime terms. -/
def prefixTerm {ctx : Nat} (ctag : Nat) : List (Term ctx) → Term ctx
 | [] => .zero
 | x :: xs => HistoryLookup.consCall ctag x (prefixTerm ctag xs)
/-- Local derivations permit the genuine task and remainder relations produced
by an expansion case. Only the explicitly constructor-built finite prefixes
are inductive here; no relation on arbitrary append inputs is assumed. -/
def InternalFinitePrefixAppend : Prop := ∀ n (p : Program n) len q l r ctag atag,
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (G : List (Formula ctx)) (xs ys : List (Term ctx)) (tail newTail : Term ctx),
 List.Forall₂ (fun x y => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r x y))) xs ys →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r tail newTail)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (stackRelation len q l r
   (HistoryAppend.appendCall atag (prefixTerm ctag xs) tail)
   (HistoryAppend.appendCall atag (prefixTerm ctag ys) newTail)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixTargets
