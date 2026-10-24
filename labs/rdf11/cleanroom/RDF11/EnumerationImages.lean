/-
Derived representation obligation: mapping a set may identify members.
Its finite enumeration must deduplicate the image, not retain duplicate rows.
-/
import RDF11.Enumeration

namespace RDF11

theorem Set.image_ofList (f : α → β) (xs : List α) :
    Set.image f (Set.ofList xs) = Set.ofList (xs.map f) := by
  apply Set.ext
  intro b
  simp only [Set.image, Set.ofList, List.mem_map]

namespace Enumeration

variable {α : Type u} {β : Type v} {G H : Set α}

theorem transport_length (h : G = H) (e : Enumeration G) :
    (h ▸ e : Enumeration H).triples.length = e.triples.length := by
  cases h
  rfl

def imageDeduplicated [DecidableEq β] (e : Enumeration G) (f : α → β) : Enumeration (Set.image f G) where
  triples := unique (e.triples.map f)
  nodup := unique_nodup _
  membership := by
    intro b
    simp only [mem_unique, List.mem_map, Set.image]
    exact ⟨fun ⟨a, ha, hab⟩ => ⟨a, (e.membership a).mp ha, hab⟩,
      fun ⟨a, ha, hab⟩ => ⟨a, (e.membership a).mpr ha, hab⟩⟩

theorem image_length_le [DecidableEq β] (e : Enumeration G) (f : α → β) :
    (e.imageDeduplicated f).triples.length ≤ e.triples.length := by
  have h := (unique_nodup (e.triples.map f)).length_le_of_subset
    (fun b hb => (mem_unique _ b).mp hb)
  simpa only [imageDeduplicated, List.length_map] using h

end Enumeration
end RDF11
