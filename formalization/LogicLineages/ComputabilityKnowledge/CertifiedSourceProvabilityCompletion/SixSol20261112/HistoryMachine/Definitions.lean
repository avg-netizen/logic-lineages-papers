module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsDefinitions

@[expose] public section
/-! A syntax-explicit iteration of the ACTUAL original history checker.
The state retains the original Option History and remaining original List Line.
Only the outer iteration is fixed syntactically; no correctness of an opaque
kernel is used to infer an internal derivation. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPRDefiningEquations
open GorbowProofChecker GorbowPublishedDCB List.Vector

abbrev State := Option History × List Line

def decodedLines (certificate : Nat) : List Line :=
  (GorbowNumericCertificate.decodeCertificate certificate).getD []

def decodedState (state : Nat) : State :=
  (Encodable.decode state).getD (none,[])

def transition (index fuel : Nat) (state : State) : State :=
  match state.2 with
  | [] => state
  | line :: rest =>
      (GorbowTheoryChecker.step
        (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat Code index,fuel)) state.1 line,rest)

def kernelFunction (v : List.Vector Nat 3) : Nat :=
  Encodable.encode (transition v.tail.head v.tail.tail.head (decodedState v.head))

def boundFunction (v : List.Vector Nat 1) : Nat := Encodable.encode (decodedLines v.head)
def initialFunction (v : List.Vector Nat 1) : Nat :=
  Encodable.encode ((some [],decodedLines v.head) : State)

def finish (state : State) (context formula certificate : Nat) : Bool :=
  match GorbowSortedSyntaxCode.decodeFormulaRaw formula,
      GorbowNumericCertificate.decodeCertificate certificate,state.1 with
  | some raw,some _,some ((n,out)::_) => decide (context=n ∧ raw=out)
  | _,_,_ => false

def finishFunction (v : List.Vector Nat 4) : Nat :=
  if finish (decodedState v.head) v.tail.head v.tail.tail.head v.tail.tail.tail.head then 1 else 0

def KernelProgram (p : Program 3) : Prop := ∀ v, evaluate p v = kernelFunction v
def BoundProgram (p : Program 1) : Prop := ∀ v, evaluate p v = boundFunction v
def InitialProgram (p : Program 1) : Prop := ∀ v, evaluate p v = initialFunction v
def FinishProgram (p : Program 4) : Prop := ∀ v, evaluate p v = finishFunction v

/-- The recursion input is first: [count,initialState,index,fuel]. -/
def iterationBase : Program 3 := .projection 0
def iterationArguments : Fin 3 → Program 5 :=
  Fin.cases (.projection (1 : Fin 5))
    (Fin.cases (.projection (3 : Fin 5))
      (Fin.cases (.projection (4 : Fin 5)) Fin.elim0))
def iterationStep (kernel : Program 3) : Program 5 := .composition kernel iterationArguments
def iterator (kernel : Program 3) : Program 4 := .recursion iterationBase (iterationStep kernel)

def boundArgument (bound : Program 1) : Program 5 :=
  .composition bound (fun _ => .projection (4 : Fin 5))
def initialArgument (initial : Program 1) : Program 5 :=
  .composition initial (fun _ => .projection (4 : Fin 5))
def loopArguments (bound initial : Program 1) : Fin 4 → Program 5 :=
  Fin.cases (boundArgument bound) (Fin.cases (initialArgument initial)
    (Fin.cases (.projection (0 : Fin 5)) (Fin.cases (.projection (1 : Fin 5)) Fin.elim0)))
def loop (kernel : Program 3) (bound initial : Program 1) : Program 5 :=
  .composition (iterator kernel) (loopArguments bound initial)
def checkerArguments (kernel : Program 3) (bound initial : Program 1) : Fin 4 → Program 5 :=
  Fin.cases (loop kernel bound initial) (Fin.cases (.projection (2 : Fin 5))
    (Fin.cases (.projection (3 : Fin 5)) (Fin.cases (.projection (4 : Fin 5)) Fin.elim0)))
def checker (kernel : Program 3) (bound initial : Program 1) (finalizer : Program 4) : Program 5 :=
  .composition finalizer (checkerArguments kernel bound initial)

/-- Actual subtree offsets inside the unchanged saturating Fuel wrapper. -/
def coreCheckerTag (fuelTag : Nat) (q0 : Program 5) : Nat :=
  fuelTag + 2 + GorbowPRChildTags.argumentTag Fuel.isOne
    (fun _ : Fin 1 => Program.composition q0 Fuel.baseArguments) 0 + 1

def iteratorTag (fuelTag : Nat) (kernel : Program 3) (bound initial : Program 1)
    (finalizer : Program 4) : Nat :=
  coreCheckerTag fuelTag (checker kernel bound initial finalizer) +
    GorbowPRChildTags.argumentTag finalizer (checkerArguments kernel bound initial) 0 + 1

def iterationCall {ctx : Nat} (tag : Nat) (count state index fuel : Term ctx) : Term ctx :=
  call tag (count ::ᵥ state ::ᵥ index ::ᵥ fuel ::ᵥ nil)

/-- Variable zero is the arbitrary SECOND iteration count. All original
parameters are lifted under this genuine object-language induction binder. -/
def fusionTemplate {ctx : Nat} (tag : Nat) (s state index fuel : Term ctx) : Formula (ctx+1) :=
  .equal (iterationCall tag (.add (Fuel.liftTerm s) (.var 0))
      (Fuel.liftTerm state) (Fuel.liftTerm index) (Fuel.liftTerm fuel))
    (iterationCall tag (.var 0)
      (iterationCall tag (Fuel.liftTerm s) (Fuel.liftTerm state)
        (Fuel.liftTerm index) (Fuel.liftTerm fuel))
      (Fuel.liftTerm index) (Fuel.liftTerm fuel))

def fusionClause (pF : Program 1) (kernel : Program 3) (bound initial : Program 1)
    (finalizer : Program 4) : Sentence :=
  GorbowStandardInduction.universalClosure
    (fusionTemplate (iteratorTag (GorbowNamedInternalProvability.checkerTag pF)
      kernel bound initial finalizer) (.var 0 : Term 4) (.var 1) (.var 2) (.var 3))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine
