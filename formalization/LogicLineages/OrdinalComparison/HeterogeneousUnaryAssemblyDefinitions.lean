module
public import LogicLineages.OrdinalComparison.SourceUnaryChainDefinitions
public import LogicLineages.OrdinalComparison.WWSourceRenamingDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly
open SourceTypedPorts
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Private names are local to one occurrence; the suffix Γ is shared by all
inputs. Actual whole vectors, including scalar, are retained. -/
structure Operator (Γ : List Ty) where
  privateContext : List Ty
  term : OriginalTerm (privateContext ++ Γ) (Ty.curriedGround 1)
  vector : OrdinalVector (privateContext ++ Γ) 1
  assigned : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy term = some vector

def context {Γ : List Ty} : List (Operator Γ) → List Ty
  | [] => Γ
  | op :: ops => op.privateContext ++ context ops

def prefixLift {Γ Δ : List Ty} (r : Renaming Γ Δ) : (ps : List Ty) → Renaming (ps ++ Γ) (ps ++ Δ)
  | [] => r
  | _ :: ps => Renaming.lift (prefixLift r ps)

def baseMap {Γ : List Ty} : (ops : List (Operator Γ)) → Renaming Γ (context ops)
  | [] => fun x => x
  | op :: ops => fun x => shiftVariable op.privateContext (baseMap ops x)

def headMap {Γ : List Ty} (op : Operator Γ) (ops : List (Operator Γ)) :
    Renaming (op.privateContext ++ Γ) (context (op :: ops)) := prefixLift (baseMap ops) op.privateContext

/-- Literal paired renaming of sources and WHOLE vectors, in original list
order. Duplicate occurrences are traversed and retained, never deduplicated. -/
def merged {Γ : List Ty} : (ops : List (Operator Γ)) →
    List (OriginalTerm (context ops) (Ty.curriedGround 1) × OrdinalVector (context ops) 1)
  | [] => []
  | op :: ops =>
      (op.term.rename (headMap op ops), SourceRenaming.renameVector (headMap op ops) op.vector) ::
      (merged ops).map (fun p => (p.1.rename (shiftVariable op.privateContext),
        SourceRenaming.renameVector (shiftVariable op.privateContext) p.2))

def terms {Γ : List Ty} (ops : List (Operator Γ)) := (merged ops).map Prod.fst
def vectors {Γ : List Ty} (ops : List (Operator Γ)) := (merged ops).map Prod.snd

noncomputable def chargedSum : List Ordinal → Ordinal
  | [] => 1
  | a :: as => ordinalNaturalSum (a + 3) (chargedSum as)
end LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly
