module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport
open LayeredComparison.SnyatkovCompletion
open LogicLineages.ModelsAlgebra.Forests
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem transport_decode_atom (a : Atom) :
    WordLinearDecisionCompletion.Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [WordLinearDecisionCompletion.Code.decodeAtom, Encodable.encodek, Option.getD_some]

attribute [local irreducible] WordLinearDecisionCompletion.Code.decodeAtom

private theorem atoms_code_step (payload tag : Nat) (ht : tag < 6) :
    LinearRows.Code.atoms (6 * payload + tag) =
      if tag = 0 then [] else if tag = 1 then []
      else if tag = 2 then [payload]
      else if tag = 3 then LinearRows.Code.atoms payload
      else LinearRows.Code.atoms payload.unpair.1 ++ LinearRows.Code.atoms payload.unpair.2 := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [LinearRows.Code.atoms, hm, hd]

theorem transport_atoms_code (p : Formula) :
    LinearRows.Code.atoms (Formula.encode p) = p.atoms.map (fun a => Encodable.encode a.data) := by
  induction p with
  | bot => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms] using atoms_code_step 0 1 (by decide)
  | top => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms] using atoms_code_step 0 0 (by decide)
  | atom a => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms] using atoms_code_step (Encodable.encode a.data) 2 (by decide)
  | neg p hp => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms, hp] using atoms_code_step (Formula.encode p) 3 (by decide)
  | conj p q hp hq => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms, Nat.unpair_pair, hp, hq, List.map_append] using atoms_code_step (Nat.pair (Formula.encode p) (Formula.encode q)) 4 (by decide)
  | disj p q hp hq => simpa [Formula.encode, CotreePresburgerUnit.Boolean.atoms, Nat.unpair_pair, hp, hq, List.map_append] using atoms_code_step (Nat.pair (Formula.encode p) (Formula.encode q)) 5 (by decide)

theorem inequalityRows_calibration (p : Formula) :
    Code.inequalityRows (Formula.encode p) = inequalityRows p := by
  simp only [Code.inequalityRows, transport_atoms_code, List.filterMap_map,
    Function.comp_def, transport_decode_atom, inequalityRows]
  congr 1
  funext a
  cases a <;> simp [Atom.data]

theorem originalTail_calibration (p : Formula) :
    Code.originalTail (Formula.encode p) = originalTail p := by
  simp only [Code.originalTail, transport_atoms_code, List.map_map,
    Function.comp_def, transport_decode_atom, originalTail]
  congr 2
  funext a
  cases a <;> rfl

theorem outcomeFormula_calibration (o : OutcomeData) :
    Code.outcomeFormula o = Formula.encode (outcomeFormula o) := by
  by_cases h0 : o.1 = 0
  · simp [Code.outcomeFormula, outcomeFormula, h0, Formula.encode]
  · by_cases h2 : o.1 = 2
    · simp [Code.outcomeFormula, outcomeFormula, h0, h2, Formula.encode]
    · simp [Code.outcomeFormula, outcomeFormula, h0, h2, Formula.encode, Atom.data]

theorem transport_atom_calibration (table : Table) (a : Atom) :
    Code.atom table (Encodable.encode a.data) = Formula.encode (rewriteWith table (.atom a)) := by
  simp only [Code.atom, transport_decode_atom]
  cases a with
  | nonnegative r =>
      change Code.outcomeFormula (lookup (Encodable.encode r) table) =
        Formula.encode (outcomeFormula (lookup (Encodable.encode r) table))
      exact outcomeFormula_calibration _
  | divisible m r => rfl

private theorem bind_code_step (op : Nat → Nat) (payload tag : Nat) (ht : tag < 6) :
    Code.bind op (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1 else if tag = 2 then op payload
      else if tag = 3 then 6 * Code.bind op payload + 3
      else 6 * Nat.pair (Code.bind op payload.unpair.1) (Code.bind op payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.bind, hm, hd]

theorem rewriteWith_calibration (table : Table) (p : Formula) :
    Code.bind (Code.atom table) (Formula.encode p) = Formula.encode (rewriteWith table p) := by
  induction p with
  | bot => simpa [Formula.encode, rewriteWith] using bind_code_step (Code.atom table) 0 1 (by decide)
  | top => simpa [Formula.encode, rewriteWith] using bind_code_step (Code.atom table) 0 0 (by decide)
  | atom a => simpa [Formula.encode, transport_atom_calibration] using bind_code_step (Code.atom table) (Encodable.encode a.data) 2 (by decide)
  | neg p hp => simpa [Formula.encode, rewriteWith, hp] using bind_code_step (Code.atom table) (Formula.encode p) 3 (by decide)
  | conj p q hp hq => simpa [Formula.encode, rewriteWith, Nat.unpair_pair, hp, hq] using bind_code_step (Code.atom table) (Nat.pair (Formula.encode p) (Formula.encode q)) 4 (by decide)
  | disj p q hp hq => simpa [Formula.encode, rewriteWith, Nat.unpair_pair, hp, hq] using bind_code_step (Code.atom table) (Nat.pair (Formula.encode p) (Formula.encode q)) 5 (by decide)

theorem rewrite_calibration (p : Formula) (outcomes : List Outcome) :
    Code.rewrite (Formula.encode p) (outcomes.map outcomeData) =
      Formula.encode (OutcomeTransport.rewrite p outcomes) := by
  simp only [Code.rewrite, inequalityRows_calibration, OutcomeTransport.rewrite,
    rewriteWith_calibration]

theorem transform_calibration (p : Formula) (pack : Package) :
    Code.transform (Formula.encode p) (encodePackage pack) = encodeMatrix (transform p pack) := by
  simp only [Code.transform, encodePackage, originalTail_calibration, encodeMatrix,
    transform, List.map_map, Function.comp_def, Formula.encode]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact congrArg (fun n => 6 * Nat.pair (Formula.encode c.guard) n + 4)
    (rewrite_calibration p c.outcomes)

theorem compile_calibration (D maximum : Nat) (p : Formula) :
    Code.compile D maximum (Formula.encode p) = encodeMatrix (OutcomeTransport.compile D maximum p) := by
  simp only [Code.compile, inequalityRows_calibration, OutcomeTransport.compile,
    transform_calibration]

theorem literalCodeCalibration : OutcomeTransportTargets.LiteralCodeCalibration :=
  ⟨inequalityRows_calibration, transform_calibration, compile_calibration⟩

/- Explicit per-file audit includes private helpers before module export. -/
#print axioms transport_decode_atom
#print axioms atoms_code_step
#print axioms transport_atoms_code
#print axioms inequalityRows_calibration
#print axioms originalTail_calibration
#print axioms outcomeFormula_calibration
#print axioms transport_atom_calibration
#print axioms bind_code_step
#print axioms rewriteWith_calibration
#print axioms rewrite_calibration
#print axioms transform_calibration
#print axioms compile_calibration
#print axioms literalCodeCalibration

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
