module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One global Data and window AST precede all windows and Gamma. The
existing source/member normalization is performed ONCE by BottomSource;
the extra SpineRepresentative selection changes only the oldR leaf. -/
def selectedData (data : Data) (window : Program 1) : Data :=
  BottomSource.selection (SpineRepresentative.baseData data window) window

def parameters (data : Data) (window : Program 1) : Data :=
  BottomParameter.baseData (SpineRepresentative.baseData data window)

/-- Actual FULL measure preservation through the unchanged selected
bounded-descent representative, at the SAME final validator and parameter.
No numeric calibration or assumed representative invariant occurs. -/
def ActualSelectedRepresentativeSpinePreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (α : Type) (Delta : List (Formula α)) (out input parameter mark : OTerm α),
  Nonempty (Derivation body Delta
    ((BottomRepresentative.activeGraph (parameters data window) window input parameter).imp
      ((graph2 (InternalOriginalUniformDescentSelection.representative (selectedData data window))
          out input parameter).imp
        ((BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark input)))))

/-- The SAME supplied actualJ output has the supplied function's actual
flag and successor depth. Argument N needs only the existing V/type facts;
neither an argument mark nor a global fold-mark invariant is assumed. -/
def ActualParameterizedApplicationSpineEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (α : Type) (Delta : List (Formula α))
    (arrow d e function argument out parameter functionMark flag depth next resultMark : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 (BottomRepresentative.windowAt window) (suc z) function parameter ⊓
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
          arrow d e function argument out parameter ⊓
        (BottomSpineMeasure.graph functionMark function ⊓
          (graph1 InternalUnpair.left flag functionMark ⊓
            (graph1 InternalUnpair.right depth functionMark ⊓
              graph1 Program.succ next depth))))).imp
      ((BottomSpineMeasure.graph resultMark out).iff
        (graph2 InternalPairing.pairing resultMark flag next))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
