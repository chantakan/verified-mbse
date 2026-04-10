import VerifiedMBSE.Core.Component

/-!
# システムの構造的合成

2つの System を bridge コネクタで結合する `compose` と
その WellFormed 保存定理を定義する。
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  System.compose
-- ============================================================

/-- 2つのシステムを bridge コネクタ経由で合成する。 -/
def System.compose (s1 s2 : System) (bridge : List Connector) : System :=
  { parts      := s1.parts ++ s2.parts
    connectors := s1.connectors ++ s2.connectors ++ bridge }

/-- compose 後の parts は連結。 -/
theorem System.compose_parts (s1 s2 : System) (bridge : List Connector) :
    (System.compose s1 s2 bridge).parts = s1.parts ++ s2.parts := rfl

/-- compose 後の connectors は連結。 -/
theorem System.compose_connectors (s1 s2 : System) (bridge : List Connector) :
    (System.compose s1 s2 bridge).connectors =
    s1.connectors ++ s2.connectors ++ bridge := rfl

-- ============================================================
-- §2  WellFormed の保存
-- ============================================================

/-- compose は WellFormed を保存する：
    両システムが WellFormed かつ bridge が合成 parts を参照するなら、
    合成結果も WellFormed。 -/
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
