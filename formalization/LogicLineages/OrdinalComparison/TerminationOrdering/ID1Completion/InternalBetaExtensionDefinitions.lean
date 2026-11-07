module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtension
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
/-- The unchanged original beta formula, embedded into the original calculus. -/
abbrev beta {α : Type} (a b i r : OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)
/-- Every residue at a fixed index agrees in both directions. -/
def sameAt {α : Type} (a b c d i : OTerm α) : Formula α :=
  allOne (let old := beta (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))
          let new := beta (c.relabel Sum.inl) (d.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))
          old.imp new ⊓ new.imp old)
/-- The entire original prefix below the arbitrary object-language bound is preserved. -/
def sameBelow {α : Type} (a b c d n : OTerm α) : Formula α :=
  bounded (sameAt (a.relabel Sum.inl) (b.relabel Sum.inl) (c.relabel Sum.inl)
    (d.relabel Sum.inl) (.var (.inr 0))) n
/-- The new code preserves the old prefix and appends the specified value at n. -/
def extensionMatrix {α : Type} (a b n z c d : OTerm α) : Formula α :=
  sameBelow a b c d n ⊓ beta c d n z
/-- The second new code component is outside every index and residue binder. -/
def extensionWith {α : Type} (a b n z c : OTerm α) : Formula α :=
  existsOne (extensionMatrix (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl)
    (z.relabel Sum.inl) (c.relabel Sum.inl) (.var (.inr 0)))
/-- Both new code components precede all prefix tests; all old parameters remain shared. -/
def extension {α : Type} (a b n z : OTerm α) : Formula α :=
  existsOne (extensionWith (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl)
    (z.relabel Sum.inl) (.var (.inr 0)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtension
