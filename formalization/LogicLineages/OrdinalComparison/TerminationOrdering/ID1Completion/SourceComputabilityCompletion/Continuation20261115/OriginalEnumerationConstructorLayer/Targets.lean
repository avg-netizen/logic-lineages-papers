module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Actual original typed layer, including original HeadCode Encodable inputs.
Prior and opened are independent original-code lists here; the outer fuel
recursion relating them is deliberately a separate remaining obligation. -/
def NativeLayer : Prop := ∀ (n : Nat) (types : List Source.Ty)
    (heads : List (NumberedAuxiliaryCoding.HeadCode (Fin n)))
    (labels tupleBound variableBound : Nat)
    (prior opened : List (NumberedAuxiliaryCoding.Code (Fin n))),
  evaluate (layer n) (List.Vector.ofFn ![Encodable.encode types,Encodable.encode heads,
    labels,tupleBound,variableBound,Encodable.encode prior,Encodable.encode opened]) =
  Encodable.encode (NumberedCodeEnumerationPrimrecSupportProof.layer n
    ((types,heads,labels,tupleBound),variableBound,prior,opened))
/-- All eight actual component outputs, not supplied native list images. -/
def componentGraphs {alpha : Type} (n : Nat) (xs : Fin 7 → OTerm alpha)
    (ys : Fin 8 → OTerm alpha) : Formula alpha :=
  programGraph (components n 0) (ys 0) xs ⊓ programGraph (components n 1) (ys 1) xs ⊓
  programGraph (components n 2) (ys 2) xs ⊓ programGraph (components n 3) (ys 3) xs ⊓
  programGraph (components n 4) (ys 4) xs ⊓ programGraph (components n 5) (ys 5) xs ⊓
  programGraph (components n 6) (ys 6) xs ⊓ programGraph (components n 7) (ys 7) xs
/-- Membership in one of the eight original blocks, in source order. -/
def branchMember {alpha : Type} (ys : Fin 8 → OTerm alpha) (code : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) (ys 0) code ⊔
    (graph2 contains (numeral 1) (ys 1) code ⊔
    (graph2 contains (numeral 1) (ys 2) code ⊔
    (graph2 contains (numeral 1) (ys 3) code ⊔
    (graph2 contains (numeral 1) (ys 4) code ⊔
    (graph2 contains (numeral 1) (ys 5) code ⊔
    (graph2 contains (numeral 1) (ys 6) code ⊔ graph2 contains (numeral 1) (ys 7) code))))))
def witnessMatrix {alpha : Type} (n : Nat) (xs : Fin 7 → OTerm alpha)
    (code : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  componentGraphs n (fun i => (xs i).relabel Sum.inl) (fun i => .var (.inr i)) ⊓
    branchMember (fun i => .var (.inr i)) (code.relabel Sum.inl)
/-- Exact all-raw actual layer membership iff internally witnessed component
outputs and a genuine branch membership. No component, image, validity, head
conversion, or branch membership witness is an additional public premise. -/
def InternalMembership : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph (layer n) out xs)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) ↔
   Nonempty (Derivation body Delta (InternalFiniteBlocks.block (witnessMatrix n xs code))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Targets
