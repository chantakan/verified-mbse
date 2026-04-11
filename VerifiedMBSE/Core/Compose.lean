import VerifiedMBSE.Core.Component

/-!
# Structural System Composition

Defines `System.compose`, which joins two systems via bridge connectors,
and proves that composition preserves `WellFormed`.
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  System.compose
-- ============================================================

/-- Compose two systems via bridge connectors. -/
def System.compose (s1 s2 : System) (bridge : List Connector) : System :=
  { parts      := s1.parts ++ s2.parts
    connectors := s1.connectors ++ s2.connectors ++ bridge }

/-- parts after compose is the concatenation. -/
theorem System.compose_parts (s1 s2 : System) (bridge : List Connector) :
    (System.compose s1 s2 bridge).parts = s1.parts ++ s2.parts := rfl

/-- connectors after compose is the concatenation. -/
theorem System.compose_connectors (s1 s2 : System) (bridge : List Connector) :
    (System.compose s1 s2 bridge).connectors =
    s1.connectors ++ s2.connectors ++ bridge := rfl

-- ============================================================
-- §2  Preserving WellFormed
-- ============================================================

/-- compose preserves WellFormed:
    if both systems are WellFormed and bridges reference composed parts,
    the result is also WellFormed. -/
theorem System.compose_WellFormed
    (s1 s2 : System) (bridge : List Connector)
    (hw1 : s1.WellFormed) (hw2 : s2.WellFormed)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.parts ++ s2.parts ∧
        c.target.part ∈ s1.parts ++ s2.parts) :
    (System.compose s1 s2 bridge).WellFormed := by
  intro c hc
  simp only [System.compose] at hc
  rw [List.mem_append] at hc
  rcases hc with hc12 | hcb
  · rw [List.mem_append] at hc12
    rcases hc12 with hc1 | hc2
    · obtain ⟨hs, ht⟩ := hw1 c hc1
      exact ⟨List.mem_append_left _ hs, List.mem_append_left _ ht⟩
    · obtain ⟨hs, ht⟩ := hw2 c hc2
      exact ⟨List.mem_append_right _ hs, List.mem_append_right _ ht⟩
  · exact hbridge c hcb

end VerifiedMBSE.Core
