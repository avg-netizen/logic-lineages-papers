module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
/-- All numeric inputs, preserving the original task/raw decoders and defaults.
No identification with any older existential validity leaf. -/
def NativeScan : Prop := ∀ v : List.Vector Nat 2,
 evaluate scanCode v = Encodable.encode (GorbowSyntaxValidation.scan
  ((Encodable.decode (α := List GorbowSyntaxValidation.Task) (v.get 0)).getD [])
  ((Encodable.decode (α := List Nat) (v.get 1)).getD []))
def InternalEmpty : Prop := ∀ n (p : Program n) stag,
 (nodes p)[stag]? = some ⟨2,scanCode⟩ → ∀ ctx (tasks : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (scanCall stag tasks .zero) (.succ tasks)))
/-- Actual successful prefix permits fusion, including failure on the right.
The intermediate stack is an explicit operational equality, not a native fact. -/
def InternalFusion : Prop := ∀ n (p : Program n) stag atag,
 (nodes p)[stag]? = some ⟨2,scanCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (tasks left right middle : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (scanCall stag tasks left) (.succ middle))
   (.equal (scanCall stag tasks (HistoryAppend.appendCall atag left right))
    (scanCall stag middle right))))
/-- Success-only task framing. No claim that failure is preserved by a suffix. -/
def InternalFrame : Prop := ∀ n (p : Program n) stag atag,
 (nodes p)[stag]? = some ⟨2,scanCode⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (tasks raw tasksOut suffix : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (scanCall stag tasks raw) (.succ tasksOut))
   (.equal (scanCall stag (HistoryAppend.appendCall atag tasks suffix) raw)
    (.succ (HistoryAppend.appendCall atag tasksOut suffix)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Targets
