module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons hopCodeTerm)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)

/-- Original raw polynomial code of the ordered one-hop list, not a
chosen witness from numeric validity or an invented existential. -/
def singletonCertificate {α : Type} (dst q w r : OTerm α) : OTerm α :=
  rawCons (hopCodeTerm dst q w r) z

/-- Separate actual raw5 success and both actual successful least3 calls
supply a positive class hop on their existing selected core. The
literal output certificate contains exactly those original raw terms. -/
def ExactOpenSingletonCore : Prop :=
  ∀ (body : PositiveArithmeticOperators.Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (ctx ty src dst q w r : OTerm α),
    Nonempty (Derivation body [] ((actualCalls raw least ctx ty src dst q w r).imp
      (positiveAt raw least ctx ty src (singletonCertificate dst q w r) dst)))

/-- Original physical addresses and actual validator graphs at the very
same packed context and type, with ordinary open symbolic terms. The
last conjunct contains the three genuine callback graph derivations. -/
def singletonInputs {α : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left right ctx ty src dst q w r : OTerm α) : Formula α :=
  addressReport left ctx ty src ⊓
    (addressReport right ctx ty dst ⊓
      (unary cv (suc z) ctx ⊓
        (unary tv (suc z) ty ⊓ actualCalls raw least ctx ty src dst q w r)))

/-- The same installed original Program3 accepts the explicit one-hop
certificate, in its original middle slot, on the exact same body.
No opaque callback semantics or extra scalar admission is assumed. -/
def ExactOpenInstalledSingleton : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
    (c : Nat) (α : Type) (left right ctx ty src dst q w r : OTerm α),
    let R := addressPositive cv tv raw least
    let B := sourceBody (data i j R d) c
    Nonempty (Derivation B [] ((singletonInputs cv tv raw least left right ctx ty src dst q w r).imp
      (accepts R left (singletonCertificate dst q w r) right)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
