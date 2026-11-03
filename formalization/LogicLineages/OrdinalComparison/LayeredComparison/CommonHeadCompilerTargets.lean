module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.Targets
open CommonHeadLargeRow CommonHeadLargeGuards
/-- The literal terminating finite guard compiler has exact truth for every
genuine source valuation, including dependent/repeated input values, signed
cancellation, empty rows, arbitrary desired signs and ALL finite exceptions. -/
def ExactFuelCompiler : Prop := ∀ fuel (rho:NONote),Order.IsSuccLimit rho.1.repr→
  ∀ K cs desired (ν:Nat→Nat),cs.length≤fuel→
  (∀ i<cs.length,actualOrdinalNorm rho.1.repr≤ν i)→
  ((compileFuel fuel (rawNoteEncode rho.1) K cs desired).eval ν ↔
    Int.sign (value rho.1.repr K (inputRow cs ν))=desired)
/-- No fresh index enters a recursively generated guard. This is essential
for later substitution of all guards into the SAME raw-variable assignment. -/
def ExactOriginalSupport : Prop := ∀ fuel h K cs desired,
  ∀ i∈(compileFuel fuel h K cs desired).variables,i<cs.length
/-- Source row instance, using exactly its actual occurrence count as fuel. -/
def ExactSourceRowCompiler : Prop := ∀ (rho:NONote),Order.IsSuccLimit rho.1.repr→
  ∀ K cs desired (ν:Nat→Nat),
  (∀ i<cs.length,actualOrdinalNorm rho.1.repr≤ν i)→
  ((compile (rawNoteEncode rho.1) K cs desired).eval ν ↔
    Int.sign (value rho.1.repr K (inputRow cs ν))=desired)
/-- Genuine numeric algorithm on ALL codes, not existence of a mathematical
formula and not a supplied closure/decision oracle. This is separately pending
until actual computation is proved. -/
def AllCodeEffectivity : Prop := Computable (fun p:Nat×Int×List Int×Int=>compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.Targets
