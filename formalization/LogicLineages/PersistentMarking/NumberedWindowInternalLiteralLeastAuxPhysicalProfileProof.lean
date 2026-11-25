module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxProfileProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof

open NumberedWindowFieldAlgorithm (unpack unpackNode pack)
open NumberedWindowSyntaxAlgorithm (Row table termNext argsNext termParts syntaxBits)
open NumberedWindowScalarAlgorithm (Settings edge vertices least)
open NumberedWindowClassAlgorithm (rounds)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (header roundsInvariant)
open NumberedWindowInternalLiteralLeastAuxProfileProof (auxProfile exact_LiteralScalarEdgeAuxProfile)

/-- All coordinates are the values of the actual selected raw
programs. Non-tag-six inputs need no further guard. -/
def physicalAuxProfile (q : Nat) : Option (Nat × Nat × Nat) :=
  if run termShape q = 1 then
    some (run (field 0) q,run (field 1) q,run cellHead (run (field 2) q))
  else none

private theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier {k n : Nat} (h : k < n) :
    (table n)[k]? = some (syntaxBits k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : k < n
    · simp only [table,List.getElem?_append_left (tableLength n ▸ prior)]
      exact ih prior
    · have last : k = n := by omega
      subst k
      simpa only [table,tableLength,syntaxBits] using
        (List.getElem?_concat_length (l := table n) (a := (termNext n (table n),argsNext n (table n))))

private theorem syntaxSelectedDecoded (n q : Nat) (held : ((table n).getD q (false,false)).1 = true) :
    ∃ tag fs, unpackNode q = some (tag,fs) := by
  rw [List.getD_eq_getElem?_getD] at held
  by_cases inList : q < n
  · rw [earlier inList] at held
    change termNext q (table q) = true at held
    unfold termNext at held
    cases h : unpackNode q with
    | none => simp [h] at held
    | some p => exact ⟨p.1,p.2,by cases p; rfl⟩
  · have none : (table n)[q]? = none := by
      apply List.getElem?_eq_none
      rw [tableLength]
      omega
    simp [none] at held

private theorem auxSyntaxFields (q : Nat) (fs : List Nat)
    (syn : (syntaxBits q).1 = true) (read : unpackNode q = some (6,fs)) :
    ∃ d c f a, fs = [d,c,f,a] ∧ ∃ k ls, unpackNode f = some (k,ls) := by
  change termNext q (table q) = true at syn
  simp only [termNext,read,Option.any_some] at syn
  rcases fs with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨a,_ | ⟨e,es⟩⟩⟩⟩⟩ <;> simp [termParts] at syn
  exact ⟨d,c,f,a,rfl,syntaxSelectedDecoded q f syn.1.2⟩

private theorem rawHeadOf {q tag : Nat} {fs : List Nat} (decoded : unpackNode q = some (tag,fs)) :
    run cellHead q = tag := by
  rw [codeOfNode decoded]
  exact (headTailOfCell (cellAt tag (pack fs))).1

private def normalizeProfile (p : Nat × Nat × Option Nat) : Nat × Nat × Nat :=
  (p.1,p.2.1,p.2.2.getD 0)

private theorem profileOnSyntax (q : Nat) (syn : (syntaxBits q).1 = true) :
    physicalAuxProfile q = (auxProfile q).map normalizeProfile := by
  cases hu : unpackNode q with
  | none =>
    have no : run termShape q ≠ 1 := fun yes => by
      obtain ⟨d,c,f,a,h⟩ := (termOne q).mp yes
      simp [hu] at h
    simp [physicalAuxProfile,no,auxProfile,hu]
  | some p =>
    obtain ⟨tag,fs⟩ := p
    by_cases isAux : tag = 6
    · subst tag
      obtain ⟨d,c,f,a,rfl,k,child,parsed⟩ := auxSyntaxFields q fs syn hu
      have yes := (termOne q).mpr ⟨d,c,f,a,hu⟩
      obtain ⟨hd,hc,hf,_⟩ := termFields hu
      simp [physicalAuxProfile,yes,hd,hc,hf,auxProfile,hu,normalizeProfile,header,parsed,rawHeadOf parsed]
    · have no : run termShape q ≠ 1 := fun yes => by
        obtain ⟨d,c,f,a,h⟩ := (termOne q).mp yes
        rw [hu] at h
        exact isAux (congrArg Prod.fst (Option.some.inj h))
      simp [physicalAuxProfile,no,auxProfile,hu,isAux]

theorem exact_LiteralScalarEdgePhysicalAuxProfile (s : Settings) (ctx : List Nat) (ty a b : Nat)
    (h : edge s ctx ty a b = true) : physicalAuxProfile a = physicalAuxProfile b := by
  have same := exact_LiteralScalarEdgeAuxProfile s ctx ty a b h
  simp only [edge,NumberedWindowExchangeAlgorithm.bits,Bool.and_eq_true] at h
  rw [profileOnSyntax a h.1.1.1.1,profileOnSyntax b h.1.1.1.2,same]

theorem exact_LiteralPackedLeastPhysicalAuxProfile (s : Settings) (ctx ty a b : Nat)
    (h : packedLeast s ctx ty a = some b) : physicalAuxProfile a = physicalAuxProfile b := by
  unfold packedLeast at h
  cases hc : unpack ctx with
  | none => simp [hc] at h
  | some c =>
    have one : least s c ty a = some b := by simpa [hc] using h
    let pool := vertices s a
    change (rounds (edge s c ty) pool a pool.length).min? = some b at one
    exact roundsInvariant physicalAuxProfile (exact_LiteralScalarEdgePhysicalAuxProfile s c ty) pool a pool.length b
      (List.min?_eq_some_iff.mp one).1

#print axioms exact_LiteralScalarEdgePhysicalAuxProfile
#print axioms exact_LiteralPackedLeastPhysicalAuxProfile
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
