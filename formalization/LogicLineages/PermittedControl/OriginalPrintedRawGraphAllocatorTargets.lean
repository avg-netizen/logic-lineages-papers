module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (RawGate encodeGate)
open OriginalPrintedCircuitSequential (Gate)

abbrev ExteriorArgs := List Nat × Nat
abbrev AllocatorArgs := Nat × List RawGate
abbrev OriginalArgs := List Nat × Nat × List RawGate

def outputCode (g : RawGate) : Nat := g.2.2.1

def referencesCode (g : RawGate) : List Nat :=
  if g.1 = 0 then g.2.2.2.2.2.map Prod.snd else [g.2.1]

def namesCode (gates : List RawGate) : List Nat :=
  gates.map outputCode ++ gates.flatMap referencesCode

def baseCodes (gates : List RawGate) : List RawGate :=
  gates.filter (fun g => decide (g.1 ≤ 1))

def exteriorCode (p : ExteriorArgs) : Nat :=
  p.1.foldr max ((MaximalPlainBranchPrograms.Code.variables p.2).foldr max 0)

def protectedCode (p : AllocatorArgs) : Nat := (namesCode p.2).foldr max p.1

/-- Both original ceilings are retained, even when the protected inner
base-only maximum would be redundant on genuine source data. -/
def firstHiddenCode (p : AllocatorArgs) : Nat :=
  protectedCode (protectedCode p,baseCodes p.2) + 1

def initialCode (p : OriginalArgs) : Nat := firstHiddenCode (exteriorCode (p.1,p.2.1),p.2.2)

def ExactOriginalRawGraphNames : Prop :=
  (∀ g : Gate, outputCode (encodeGate g) = g.output ∧ referencesCode (encodeGate g) = g.references) ∧
  (∀ gs : List Gate, namesCode (gs.map encodeGate) = OriginalPrintedCircuitNormalization.names gs) ∧
  ∀ gs : List Gate, baseCodes (gs.map encodeGate) =
    (OriginalPrintedCircuitNormalization.baseGates gs).map (fun g => encodeGate (.base g))

def ExactOriginalRawGraphAllocator : Prop :=
  (∀ (known : List Nat) (p : NormalForm.Formula),
    exteriorCode (known,p.encode) = OriginalPrintedCircuitNormalizedTerminal.exterior known (.rows p)) ∧
  (∀ (ext : Nat) (gates : List Gate), protectedCode (ext,gates.map encodeGate) =
    OriginalPrintedCircuitNormalization.protectedCeiling ext gates) ∧
  (∀ (ext : Nat) (gates : List Gate), firstHiddenCode (ext,gates.map encodeGate) =
    OriginalPrintedCircuitNormalization.firstHidden ext gates) ∧
  ∀ (known : List Nat) (p : NormalForm.Formula) (gates : List Gate),
    initialCode (known,p.encode,gates.map encodeGate) =
      OriginalPrintedCircuitNormalization.firstHidden
        (OriginalPrintedCircuitNormalizedTerminal.exterior known (.rows p)) gates

def ExactOriginalRawGraphAllocatorEffectivity : Prop :=
  Primrec namesCode ∧ Primrec baseCodes ∧ Primrec exteriorCode ∧ Primrec initialCode

def FullOriginalPrintedRawGraphAllocator : Prop :=
  ExactOriginalRawGraphNames ∧ ExactOriginalRawGraphAllocator ∧ ExactOriginalRawGraphAllocatorEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
