module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Outer
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- These are the ORIGINAL total Object-code coordinates. Their native
calibration uses the original Object codec, with no new canonical-code test. -/
def gamma : Program 1 := InternalUnpair.left

def valid : Program 1 := InternalLessThan.constantOne 1

def tag : Program 2 := leftOf (rightOf (.projection 1))

def arrow : Program 2 := InternalListCodec.consCode

def parameter {m : Nat} (context object : Program m) : Program m :=
  pairOf context (leftOf object)

def windowAt {m : Nat} (window : Program 1) (context : Fin m) : Program m :=
  .composition window (fun _ : Fin 1 => .projection context)

/-- Raw checker inputs [payload,requestedType,pair(context,Gamma-code)]. -/
def typedBranch (data : Data) : Program 3 :=
  .composition (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (rightOf (.projection 2)) (Fin.cons (.projection 1)
      (Fin.cons (parameter (.projection 0) (.projection 2)) Fin.elim0)))

def typed (data : Data) (window : Program 1) (oldTyped : Program 3) : Program 3 :=
  InternalAcceptance.branch (windowAt window 0) oldTyped (typedBranch data)

def scalarBranch (rawScalar : Program 2) : Program 2 :=
  .composition rawScalar (Fin.cons (rightOf (.projection 1))
    (Fin.cons (parameter (.projection 0) (.projection 1)) Fin.elim0))

def scalar (rawScalar : Program 2) (window : Program 1) (oldScalar : Program 2) : Program 2 :=
  InternalAcceptance.branch (windowAt window 0) oldScalar (scalarBranch rawScalar)

def rawPositive (data : Data) (oldStep : Program 4) (bottom measure : Program 1) : Program 4 :=
  PositiveGuard.checker bottom measure (edgeChecker data oldStep)

/-- The inner same-Gamma factor makes this intermediate ORIGINAL object
positive checker calibrated before the literal outer GammaGuardedSource
factor is added. Source certificate and parameter remain separate. -/
def positiveBranch (positiveRaw : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (GammaGuardedSource.sameGamma gamma 1 2)
    (.composition positiveRaw
      (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
        (Fin.cons (.projection 3) (Fin.cons (parameter (.projection 0) (.projection 1)) Fin.elim0)))))

def positive (positiveRaw : Program 4) (window : Program 1) (oldPositive : Program 4) : Program 4 :=
  InternalAcceptance.branch (windowAt window 0) oldPositive (positiveBranch positiveRaw)

/-- The multiset/direct Programs remain explicit GLOBAL input choices.
Every replaced field retains its complete original inactive output. -/
def sourceBase (old : SourcePresentation.Data) (rawScalar : Program 2)
    (positiveRaw : Program 4) (window : Program 1) : SourcePresentation.Data :=
  { old with scalar := scalar rawScalar window old.scalar,
    positive := positive positiveRaw window old.positive }

/-- The ORIGINAL source constructor is retained verbatim. No finite source
window or ambient Gamma occurs in this selection. -/
def source (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4)
    (bottom measure window : Program 1) : SourcePresentation.Data :=
  GammaGuardedSource.source
    (sourceBase oldSrc rawScalar (rawPositive data oldStep bottom measure) window)
    (typed data window oldComp.typed) valid gamma tag window

def baseComputability (old : JointGammaComputability.Data) (data : Data)
    (window : Program 1) : JointGammaComputability.Data :=
  GammaGuardedSource.computability { old with typed := typed data window old.typed }
    valid gamma tag

/-- Literal original application-domain activation on all five object
inputs. It is shared by the selected result builder and application checker. -/
def resultActivation (old : JointGammaComputability.Data) (data : Data)
    (window : Program 1) : Program 5 :=
  let comp := baseComputability old data window
  ApplicationDomain.activation window comp.typed comp.guard arrow

/-- Pair the ORIGINAL runtime Gamma with the actual supplied raw vertex.
The function is direct; RAW argument normalization remains inside actualJ. -/
def resultBranch (vertex : Program 5) : Program 5 :=
  pairOf (leftOf (.projection 3))
    (.composition vertex
      (Fin.cons (parameter (.projection 0) (.projection 3))
        (Fin.cons (.projection 1) (Fin.cons (.projection 2)
          (Fin.cons (rightOf (.projection 4)) (Fin.cons (rightOf (.projection 3)) Fin.elim0))))))

def result (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) : Program 5 :=
  InternalAcceptance.branch (resultActivation old data window) oldResult
    (resultBranch (Path.vertex data window oldVertex))

/-- The ORIGINAL InternalApplication constructor supplies active graph,
totality and functionality. Its old application checker is untouched on
inactive inputs; typed/guard fields are the SAME ones used by the source. -/
def computability (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) : JointGammaComputability.Data :=
  InternalApplication.computability (baseComputability old data window) window arrow
    (result old data window oldVertex oldResult)

/-- Original [context,domain,codomain,argumentObject,certificate] inputs.
The ORIGINAL pathMap receives [certificate,p,domain,codomain,RAWargument].
No endpoint, new certificate field, fuel or Gamma-specific Program is added. -/
def lift (data : Data) (window : Program 1) (oldVertex : Program 5) : Program 5 :=
  .composition (InternalApplicationPathMap.pathMap (Path.vertex data window oldVertex))
    (Fin.cons (.projection 4) (Fin.cons (parameter (.projection 0) (.projection 3))
      (Fin.cons (.projection 1) (Fin.cons (.projection 2) (Fin.cons (rightOf (.projection 3)) Fin.elim0)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Outer
