module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open SourceComputabilityCompletion.BottomSpineMeasure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original bottom-spine shape and original spineDepth on EVERY typed raw
term, independent of finite windows. Malformed inputs retain the total fold's
literal answer; later source-wrapper calibration must treat those separately. -/
def ActualOriginalBottomSpineMeasureCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau),
  evaluate measure (List.Vector.ofFn ![packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)]) = meaning q ∧
    (bottomFlag q = 1 ↔ NumberedBottomSpine.BottomSpine q)

/-- Actual INTERNAL structural equation on the original application
constructors, actual child mark graphs and literal left/right/successor
graphs. No source validity, run success, measure law, semantic reflection
or assumed descent property is supplied. -/
def ActualParameterizedSpineMeasureApplication : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (arrow domain codomain fp ap function argument parent
      functionMark argumentMark flag depth next out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((InternalApplicationValidityClosure.applicationConstructors
      arrow domain codomain fp ap function argument parent ⊓
      (graph functionMark function ⊓
        (graph argumentMark argument ⊓
          (graph1 InternalUnpair.left flag functionMark ⊓
            (graph1 InternalUnpair.right depth functionMark ⊓
              graph1 Program.succ next depth))))).imp
      ((graph out parent).iff (graph2 InternalPairing.pairing out flag next))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureTargets
